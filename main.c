#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
#include <stdbool.h>
#include <relic.h>
#include <openssl/sha.h>
#include "accumulator.h"

#define maxUsers 1020000
#define batchMax 10000
#define maxEpochs 1000
#define MEMBERSHIP true
#define NONMEMBERSHIP false

//Accumulator initialization
void init(t_state * accumulator) {

	bn_t n2;

	g1_null(accumulator->P);
	g1_null(accumulator->X);
	g1_null(accumulator->Z);
	g1_null(accumulator->J);
	g1_null(accumulator->K);
	g1_null(accumulator->V);
	g2_null(accumulator->Pt);
	g2_null(accumulator->Qt);
	gt_null(accumulator->ePPt);
	gt_null(accumulator->eZPt);
	gt_null(accumulator->eZQt);
	gt_null(accumulator->eKPt);
	gt_null(accumulator->eVPt);
	bn_null(accumulator->n);
	bn_null(n2);
	bn_null(accumulator->a);

	TRY {
		g1_new(accumulator->P);
		g1_new(accumulator->X);
		g1_new(accumulator->Z);
		g1_new(accumulator->J);
		g1_new(accumulator->K);
		g1_new(accumulator->V);
		g2_new(accumulator->Pt);
		g2_new(accumulator->Qt);
		gt_new(accumulator->ePPt);
		gt_new(accumulator->eZPt);
		gt_new(accumulator->eZQt);
		gt_new(accumulator->eKPt);
		gt_new(accumulator->eVPt);
		bn_new(accumulator->n);
		bn_new(n2);
		bn_new(accumulator->a);

		//|G1| = |G2| ?
		g1_get_ord(accumulator->n);
		g2_get_ord(n2);
		assert(bn_cmp(accumulator->n, n2) == RLC_EQ);

		//Secret alpha
		bn_rand_mod(accumulator->a, accumulator->n);

		//Generators initialization
		g1_get_gen(accumulator->P);
		g2_get_gen(accumulator->Pt);
		g2_mul(accumulator->Qt, accumulator->Pt, accumulator->a);

		//Generators for the ZK protocol
		g1_rand(accumulator->X);
		g1_rand(accumulator->Z);
		g1_rand(accumulator->J);
		g1_rand(accumulator->K);

		//accumulator initialization V0=P
		g1_get_gen(accumulator->V);

		//Cached pairings, for fast zkproofs creation and verification
		pc_map(accumulator->ePPt, accumulator->P, accumulator->Pt);
		pc_map(accumulator->eZPt, accumulator->Z, accumulator->Pt);
		pc_map(accumulator->eZQt, accumulator->Z, accumulator->Qt);
		pc_map(accumulator->eKPt, accumulator->K, accumulator->Pt);
		pc_map(accumulator->eVPt, accumulator->V, accumulator->Pt);

		//No accumulated elements
		accumulator->totAccEl = 0;

		//fV(a) = 1
		bn_null(accumulator->fVa);
		bn_new(accumulator->fVa);
		bn_set_dig(accumulator->fVa, 1);

		//The set of all accumulated elements
		accumulator->Y = (bn_t *)malloc(sizeof(bn_t)*(maxUsers));
		for (int i = 0; i<maxUsers; i++) {
			bn_null(accumulator->Y[i]);
			bn_new(accumulator->Y[i]);
			bn_set_dig(accumulator->Y[i], 0);
		}

		//Initializing epoch array
		accumulator->epochs = (t_epoch *)malloc(sizeof(t_epoch)*maxEpochs);
		accumulator->currentEpoch = 0;
		g1_copy((accumulator->epochs[0]).V, accumulator->V);
		(accumulator->epochs[0]).Y_add = NULL;
		(accumulator->epochs[0]).Y_del = NULL;
		(accumulator->epochs[0]).addSize = 0;
		(accumulator->epochs[0]).delSize = 0;
		(accumulator->epochs[0]).OmegaAdd = NULL;
		(accumulator->epochs[0]).OmegaDel = NULL;

	}

	CATCH_ANY {
		util_print("FATAL ERROR!\n");
	}

	bn_free(n2);

	return;
}

//Issue (non-)membership witnesses
t_witness * issueWitness(t_state * accumulator, bn_t y, bool isMembership) {

	t_witness * w_y = (t_witness *)malloc(sizeof(t_witness));

	bn_t tmp, one, yplusainv;

	bn_null(w_y->y);
	g1_null(w_y->C);
	bn_null(w_y->d);
	gt_null(w_y->eCPt);

	bn_null(tmp);
	bn_null(one);
	bn_null(yplusainv);

	TRY {

		bn_new(w_y->y);
		g1_new(w_y->C);
		bn_new(w_y->d);
		gt_new(w_y->eCPt);

		bn_new(one);
		bn_new(tmp);
		bn_new(yplusainv);

		//Compute 1/y+a = y+a^{-1} (n)
		bn_add(tmp, y, accumulator->a);
		bn_mod(tmp, tmp, accumulator->n);
		//Computing inverse
		bn_gcd_ext_lehme(one, yplusainv, tmp, tmp, accumulator->n);
		assert(bn_cmp_dig(one,1) == RLC_EQ);
		bn_mod(yplusainv, yplusainv, accumulator->n);

		if (isMembership == true) {

			g1_mul(w_y->C, accumulator->V, yplusainv);
			bn_set_dig(w_y->d, 0);
		}

		else {

			//Compute fV(-y)
			bn_set_dig(w_y->d, 1);

			//Computing fV(-y) everyime is better than keeping fV updated
			for (int i=0; i< accumulator->totAccEl; i++) {
				bn_sub(tmp, accumulator->Y[i], y);
				bn_mul(w_y->d, w_y->d, tmp);
				bn_mod(w_y->d, w_y->d, accumulator->n);
			}

			//Check y is not already accumulated
			assert(bn_cmp_dig(w_y->d, 0) != RLC_EQ);

			//Compute fV(a)-d
			bn_sub(tmp, accumulator->fVa, w_y->d);
			bn_mul(tmp, tmp, yplusainv);
			bn_mod(tmp, tmp, accumulator->n);

			//Compute fV(a)-d C = (fV(a)-d)/(y+a)P
			g1_mul(w_y->C, accumulator->P, tmp);

		}

		//Store associated accumulator epoch and identity
		w_y->epoch = accumulator->currentEpoch;
		bn_copy(w_y->y, y);

		//Set e(C,Pt) value for efficient ZK PoK
		pc_map(w_y->eCPt, w_y->C, accumulator->Pt);

	}

	CATCH_ANY {
		util_print("FATAL ERROR!\n");
	}

	bn_free(one);
	bn_free(yplusainv);
	bn_free(tmp);

	return w_y;
}

//Witness Verification
void verifyWitness(t_state * accumulator, t_witness * wit) {

	gt_t e, ed;
	g2_t yPt, yPtpQt;

	g2_null(yPt); g2_null(yPtpQt);
	gt_null(e);   gt_null(ed);

	g2_new(yPt);  g2_new(yPtpQt);
	gt_new(e);    gt_new(ed);

	//yPtpQt =  Qt + yPt
	g2_copy(yPtpQt, accumulator->Qt);
	g2_mul(yPt, accumulator->Pt, wit->y);
	g2_add(yPtpQt, yPtpQt, yPt);

	//e = e(C, yPt + Qt)
	pc_map(e, wit->C, yPtpQt);

	//e *= e(P, Pt)^d
	gt_exp(ed, accumulator->ePPt, wit->d);
	gt_mul(e, e, ed);

	if (bn_cmp_dig(wit->d,0) == RLC_EQ)
		printf("\tMembership ");
	else
		printf("\tNon-membership ");

	if (gt_cmp(e, accumulator->eVPt) == RLC_EQ)
		printf("Witness Verification SUCCEEDED!\n");
	else
		printf("Witness Verification FAILED!\n");

	g2_free(yPtpQt);
	gt_free(e);
	gt_free(ed);

	return;
}

//Update witness to current epoch
void updateWitness(t_state * accumulator, t_witness * w_y) {

	bn_t x; bn_null(x); bn_new(x);
	bn_t y; bn_null(y); bn_new(y);
	bn_t tmp; bn_null(tmp); bn_new(tmp);
	bn_t res; bn_null(res); bn_new(res);
	g1_t g1tmp; g1_null(g1tmp); g1_new(g1tmp);
	g1_t g1res; g1_null(g1res); g1_new(g1res);

	g1_t * OmegaAdd;
	bn_t * Y_add;
	int addSize;
	g1_t * OmegaDel;
	bn_t * Y_del;
	int delSize;

	//All polynomials are computed in -x rather than x. I will simply evaluate in -y.
	bn_neg(y, w_y->y);

	while (w_y->epoch != accumulator->currentEpoch) {

		OmegaAdd = (accumulator->epochs[w_y->epoch+1]).OmegaAdd;
		addSize =  (accumulator->epochs[w_y->epoch+1]).addSize;
		Y_add =  (accumulator->epochs[w_y->epoch+1]).Y_add;
		OmegaDel = (accumulator->epochs[w_y->epoch+1]).OmegaDel;
		delSize =  (accumulator->epochs[w_y->epoch+1]).delSize;
		Y_del =  (accumulator->epochs[w_y->epoch+1]).Y_del;
		g1_set_infty(g1res);

		//TODO: combine Add and Del in one Omega
		//Addition
		if(addSize > 0) {

			bn_set_dig(res,1);
			bn_set_dig(x,1);

			for(int i=0; i<addSize; i++){

				//<Yy,Omega> computation
				g1_mul(g1tmp, OmegaAdd[i], x);
				g1_add(g1res, g1res, g1tmp);

				//dA(y) computation
				bn_add(tmp, Y_add[i], y);
				bn_mul(res, res, tmp);
				bn_mod(res, res, accumulator->n);

				bn_mul(x,x,y);
				bn_mod(x,x,accumulator->n);

			}

			g1_mul(w_y->C, w_y->C, res);
			g1_add(w_y->C, w_y->C, g1res);

			if (bn_cmp_dig(w_y->d,0) != RLC_EQ) {
				bn_mul(w_y->d, w_y->d, res);
				bn_mod(w_y->d, w_y->d, accumulator->n);
			}
		}

		//Deletion
		if(delSize > 0) {

			bn_set_dig(x,1);
			bn_set_dig(res,1);

			for(int i=0; i<delSize; i++){

				//<Yy,Omega> computation
				g1_mul(g1tmp, OmegaDel[i], x);
				g1_add(g1res, g1res, g1tmp);

				//dD(y) computation
				bn_add(tmp, Y_del[i], y);
				bn_mul(res, res, tmp);
				bn_mod(res, res, accumulator->n);

				//x *= y (=y^i)
				bn_mul(x,x,y);
				bn_mod(x,x,accumulator->n);

			}

			//Compute 1/dD(y)
			bn_t one; bn_null(one); bn_new(one); bn_set_dig(one, 1);
			bn_t tmp2; bn_null(tmp2); bn_new(tmp2);
			bn_gcd_ext_lehme(one, tmp, tmp2, res, accumulator->n);
			//The inverse cannot be computed if current user was revoked
			if (bn_cmp_dig(one,1) != RLC_EQ) {
				printf("\tUser revoked. No update possible.\n");
				return;
			}

			bn_copy(res, tmp);
			bn_mod(res, res, accumulator->n);

			//C' = 1/dD(y)*( C - vD(y)V )
			g1_sub(w_y->C, w_y->C, g1res);
			g1_mul(w_y->C, w_y->C, res);

			if (bn_cmp_dig(w_y->d,0) != RLC_EQ) {
				bn_mul(w_y->d, w_y->d, res);
				bn_mod(w_y->d, w_y->d, accumulator->n);
			}

		}

		//Update witness epoch
		w_y->epoch += 1;
	}

	//Update e(C, Pt) value for efficient ZK PoK
	pc_map(w_y->eCPt, w_y->C, accumulator->Pt);

	return;

}


//Update witness to current epoch
void updateWitnessNonBatch(t_state * accumulator, t_witness * w_y) {

	bn_t y; bn_null(y); bn_new(y);
	bn_t tmp; bn_null(tmp); bn_new(tmp);
	bn_t tmp2; bn_null(tmp2); bn_new(tmp2);
	bn_t res; bn_null(res); bn_new(res);
	bn_t one; bn_null(one); bn_new(one);
	g1_t V; g1_null(V); g1_new(V);

	bn_t * Y_add;
	int addSize;
	bn_t * Y_del;
	int delSize;

	//I will simply evaluate in -y.
	bn_neg(y, w_y->y);

	while (w_y->epoch != accumulator->currentEpoch) {

		g1_copy(V, (accumulator->epochs[w_y->epoch]).V);
		addSize =  (accumulator->epochs[w_y->epoch+1]).addSize;
		Y_add =  (accumulator->epochs[w_y->epoch+1]).Y_add;
		delSize =  (accumulator->epochs[w_y->epoch+1]).delSize;
		Y_del =  (accumulator->epochs[w_y->epoch+1]).Y_del;

		//Addition
		if(addSize > 0) {

			for(int i=0; i<addSize; i++){

				//C' = (y'-y)C + V
				bn_add(res, Y_add[i], y);
				g1_mul(w_y->C, w_y->C, res);
				g1_add(w_y->C, w_y->C, V);

				//d' = (y'-y)d
				if (bn_cmp_dig(w_y->d,0) != RLC_EQ) {
					bn_mul(w_y->d, w_y->d, res);
					bn_mod(w_y->d, w_y->d, accumulator->n);
				}

				//update acc V' = (y'+a)V
				bn_add(res, Y_add[i], accumulator->a);
				g1_mul(V, V, res);

			}

		}

		//Deletion
		if(delSize > 0) {

			bn_set_dig(res,1);

			for(int i=0; i<delSize; i++){

				//update acc V' = 1/(y'+a)V
				bn_add(res, Y_del[i], accumulator->a);
				bn_gcd_ext_lehme(one, tmp, tmp2, res, accumulator->n);
				if (bn_cmp_dig(one,1) != RLC_EQ) {
						printf("\tUser revoked equals alpha.\n");
						return;
				}
				bn_copy(res, tmp);
				bn_mod(res, res, accumulator->n);
				g1_mul(V, V, res);

				//1/(y'-y) computation
				bn_add(res, Y_del[i], y);
				bn_mod(res, res, accumulator->n);

				//Compute 1/(y'-y)
				bn_gcd_ext_lehme(one, tmp, tmp2, res, accumulator->n);
				if (bn_cmp_dig(one,1) != RLC_EQ) {
					printf("\tUser revoked. No update possible.\n");
					return;
				}
				bn_copy(res, tmp);
				bn_mod(res, res, accumulator->n);

				//C' = 1/(y'-y)*( C - V' )
				g1_sub(w_y->C, w_y->C, V);
				g1_mul(w_y->C, w_y->C, res);

				if (bn_cmp_dig(w_y->d,0) != RLC_EQ) {
					bn_mul(w_y->d, w_y->d, res);
					bn_mod(w_y->d, w_y->d, accumulator->n);
				}

			}

		}

		//Update witness epoch
		w_y->epoch += 1;
	}

	//Update e(C, Pt) value for efficient ZK PoK
	pc_map(w_y->eCPt, w_y->C, accumulator->Pt);

	return;

}

//Basic Batch Addition (no batch update data)
void basicBatchAdd(t_state * accumulator, int batchSize) {

	//Check if maxUsers is reached
	assert(accumulator->totAccEl + batchSize <= maxUsers);

	bn_t currfVa; bn_null(currfVa); bn_new(currfVa); bn_set_dig(currfVa, 1);
	bn_t tmp; bn_null(tmp); bn_new(tmp);

	bn_t * Y_add = (bn_t *)malloc(sizeof(bn_t)*batchSize);

	clock_t start,end; double cpu_time_used = 0;

	for (int i = 0; i<batchSize; i++) {

		//Initializing arrays
		bn_null(Y_add[i]);    bn_new(Y_add[i]);

		//Random y element. We measure the time needed to generate elements
		start = clock();
		bn_rand_mod(Y_add[i], accumulator->n);
		end = clock();
		cpu_time_used += ((double) (end - start)) / CLOCKS_PER_SEC;

		//Computing Pr(y+a)
		bn_add(tmp, Y_add[i], accumulator->a);
		bn_mul(currfVa, currfVa, tmp);
		bn_mod(currfVa, currfVa, accumulator->n);

	}

	printf("~~Elements generation and storage took %fs\n",  cpu_time_used);

	//Copy the batch added elements to all accumulated ones
	memcpy(accumulator->Y+accumulator->totAccEl, Y_add, sizeof(bn_t)*batchSize);

	//Update fVa (for non-membership witnesses)
	bn_mul(accumulator->fVa, accumulator->fVa, currfVa);
	bn_mod(accumulator->fVa, accumulator->fVa, accumulator->n);

	//Accumulator Update
	g1_mul(accumulator->V, accumulator->V, currfVa);

	//Update cached pairing value
	gt_exp(accumulator->eVPt, accumulator->eVPt, currfVa);

	//Update total number of accumulated elements
	accumulator->totAccEl = accumulator->totAccEl + batchSize;

	bn_free(tmp);
	bn_free(currfVa);
	free(Y_add);

	return;

}

//Basic Batch Deletion (no batch update data)
void basicBatchDel(t_state * accumulator, int batchSize) {

	//Check if there are enough elements to delete
	assert(accumulator->totAccEl - batchSize >= 0);

	bn_t currfVa; bn_null(currfVa); bn_new(currfVa); bn_set_dig(currfVa, 1);
	bn_t tmp; bn_null(tmp); bn_new(tmp);
	bn_t tmp2; bn_null(tmp2); bn_new(tmp2);
	bn_t one; bn_null(one); bn_new(one);

	bn_t * Y_del = (bn_t *)malloc(sizeof(bn_t)*batchSize);

	//Pick random added elements to delete. Last index set to totAccEl to properly memmove
	int * delIdx = randomIdx(accumulator->totAccEl, batchSize);
	//delIdx[batchSize] = accumulator->totAccEl;

	//Sort indexes
	qsort(delIdx, batchSize, sizeof(int), compare);

	for (int i = 0; i<batchSize; i++) {

		//Store deleted elements
		bn_null(Y_del[i]); bn_new(Y_del[i]); bn_copy(Y_del[i], accumulator->Y[delIdx[i]]);
		//Removing deleted elements from accumulated values set
		memmove(accumulator->Y + delIdx[i] - i, accumulator->Y + delIdx[i] + 1, sizeof(bn_t)*(delIdx[i+1]-delIdx[i]-1));

		//Computing Prod(y+a)
		bn_add(tmp, Y_del[i], accumulator->a);
		bn_mul(currfVa, currfVa, tmp);
		bn_mod(currfVa, currfVa, accumulator->n);

	}

	//tmp = 1/currfVa
	bn_gcd_ext_lehme(one, tmp, tmp2, currfVa, accumulator->n);
	assert(bn_cmp_dig(one,1) == RLC_EQ);
	bn_mod(tmp, tmp, accumulator->n);

	//Update fVa (for non-membership witnesses)
	bn_mul(accumulator->fVa, accumulator->fVa, tmp);
	bn_mod(accumulator->fVa, accumulator->fVa, accumulator->n);

	//Update Accumulator value
	g1_mul(accumulator->V, accumulator->V, tmp);

	//Update cached pairing value
	gt_exp(accumulator->eVPt, accumulator->eVPt, tmp);

	//Update total number of accumulated elements
	accumulator->totAccEl = accumulator->totAccEl - batchSize;

	bn_free(tmp);
	bn_free(currfVa);
	bn_free(y_add);

	return;

}

//Batch Addition operation
void batchAdd(t_state * accumulator, int batchSize) {

	//Check if maxUsers is reached
	assert(accumulator->totAccEl + batchSize <= maxUsers);

	//Generate batchMax random elements
	bn_t currfVa; bn_null(currfVa); bn_new(currfVa); bn_set_dig(currfVa, 1);
	bn_t tmp; bn_null(tmp); bn_new(tmp);

	bn_t * tmpPoly = (bn_t *)malloc(sizeof(bn_t)*(batchSize));
	bn_t * vA = (bn_t *)malloc(sizeof(bn_t)*(batchSize));

	bn_t * Y_add = (bn_t *)malloc(sizeof(bn_t)*batchSize);
	bn_t * lpr = (bn_t *)malloc(sizeof(bn_t)*batchSize);

	bn_null(lpr[0]);    bn_new(lpr[0]);	bn_set_dig(lpr[0],1);

	for (int i = 0; i<batchSize; i++) {
		//Initializing arrays
		bn_null(Y_add[i]);    bn_new(Y_add[i]);

		//Random y element
		bn_rand_mod(Y_add[i], accumulator->n);

		//Computing Pr(y+a)
		bn_add(tmp, Y_add[i], accumulator->a);
		bn_mul(currfVa, currfVa, tmp);
		bn_mod(currfVa, currfVa, accumulator->n);

		//I store consecutive products up to batchSize-1
		if (i<batchSize-1) {
			bn_null(lpr[i+1]);    bn_new(lpr[i+1]);
			bn_copy(lpr[i+1], currfVa);
		}

		//tmpPoly initilization
		bn_null(tmpPoly[i]);  bn_new(tmpPoly[i]);
		if (i==0)
			bn_set_dig(tmpPoly[i], 1);
		else
			bn_set_dig(tmpPoly[i], 0);

		//vA initialization
		bn_null(vA[i]);  bn_new(vA[i]);  bn_set_dig(vA[i], 0);

	}

	//Store partial product polynomial for witness update
	for (int i=0; i<batchSize; i++) {

		if (i>0) {
			memmove(tmpPoly+1, tmpPoly, sizeof(bn_t)*i);
			bn_set_dig(tmpPoly[0],0);
		}

		for (int j=0; j<=accumulator->totAccEl+i; j++) {
			if ((i>0) && (j<=i-1)) {
				bn_mul(tmp,tmpPoly[j+1],Y_add[i]);
				bn_add(tmp,tmpPoly[j],tmp);
				bn_mod(tmpPoly[j],tmp,accumulator->n);
			}
		}

	}

	//Omega EC points vector
	//External Sum
	for(int s=0; s<batchSize; s++) {

		//Add to vA lpr*tmpPoly
		for(int i=0; i<batchSize; i++) {
			bn_mul(tmp, lpr[s], tmpPoly[i]);
			bn_add(vA[i], vA[i], tmp);
			bn_mod(vA[i], vA[i], accumulator->n);
		}

		if (s<batchSize-1) {

			//Dividing tmpPoly by y+x
			for (int j=batchSize-s-1; j>0; j--) {
				bn_mul(tmp,tmpPoly[j],Y_add[s+1]);
				bn_sub(tmpPoly[j-1],tmpPoly[j-1],tmp);
				bn_mod(tmpPoly[j-1],tmpPoly[j-1],accumulator->n);
			}
			memmove(tmpPoly, tmpPoly+1, sizeof(bn_t)*(batchSize-s-1));
			bn_set_dig(tmpPoly[batchSize-s-1],0);

		}
	}

	free(tmpPoly);
	free(lpr);

	//Copy the batch added elements to all accumulated ones
	memcpy(accumulator->Y+accumulator->totAccEl, Y_add, sizeof(bn_t)*batchSize);

	//Update total number of accumulated elements
	accumulator->totAccEl = accumulator->totAccEl + batchSize;

	//Update fVa (for non-membership witnesses)
	bn_mul(accumulator->fVa, accumulator->fVa, currfVa);
	bn_mod(accumulator->fVa, accumulator->fVa, accumulator->n);

	//Computing the ECP vector from vA. Note we need V before update.
	g1_t * OmegaAdd = (g1_t *)malloc(sizeof(g1_t)*(batchSize));

	for (int i=0; i<batchSize; i++){
		g1_null(OmegaAdd[i]); g1_new(OmegaAdd[i]);
		g1_mul(OmegaAdd[i],  accumulator->V, vA[i]);
	}

	free(vA);

	//Update accumulator value
	g1_mul(accumulator->V, accumulator->V, currfVa);

	//Update cached pairing value
	gt_exp(accumulator->eVPt, accumulator->eVPt, currfVa);

	//Update epoch
	accumulator->currentEpoch += 1;
	g1_copy((accumulator->epochs[accumulator->currentEpoch]).V, accumulator->V);
	(accumulator->epochs[accumulator->currentEpoch]).Y_add = Y_add;
	(accumulator->epochs[accumulator->currentEpoch]).Y_del = NULL;
	(accumulator->epochs[accumulator->currentEpoch]).addSize = batchSize;
	(accumulator->epochs[accumulator->currentEpoch]).delSize = 0;
	(accumulator->epochs[accumulator->currentEpoch]).OmegaAdd = OmegaAdd;
	(accumulator->epochs[accumulator->currentEpoch]).OmegaDel = NULL;

	bn_free(tmp);
	bn_free(currfVa);

	return;

}

//Batch Deletion operation
void batchDel(t_state * accumulator, int batchSize) {

	//Check if there are enough elements to delete
	assert(accumulator->totAccEl - batchSize >= 0);

	bn_t tmp, tmp2, currfVa, one;
	bn_t * Y_del = (bn_t *)malloc(sizeof(bn_t)*batchSize);

	bn_t * lpr = (bn_t *)malloc(sizeof(bn_t)*batchSize);
	bn_t * tmpPoly = (bn_t *)malloc(sizeof(bn_t)*(batchSize));
	bn_t * vD = (bn_t *)malloc(sizeof(bn_t)*(batchSize));

	bn_null(tmp); bn_new(tmp);
	bn_null(tmp2); bn_new(tmp2);
	bn_null(one); bn_new(one);
	bn_null(currfVa); bn_new(currfVa); bn_set_dig(currfVa, 1);

	//Pick random added elements to delete. Last index set to totAccEl in randomIdx to properly memmove
	int * delIdx = randomIdx(accumulator->totAccEl, batchSize);

	//Sort indexes
	qsort(delIdx, batchSize, sizeof(int), compare);

	for(int i=0; i<batchSize; i++) {

		//Store deleted elements
		bn_null(Y_del[i]); bn_new(Y_del[i]); bn_copy(Y_del[i], accumulator->Y[delIdx[i]]);

		//Removing deleted elements from accumulated values set
		memmove(accumulator->Y + delIdx[i] - i, accumulator->Y + delIdx[i] + 1, sizeof(bn_t)*(delIdx[i+1]-delIdx[i]-1));

		//Computing Prod(y+a)
		bn_add(tmp, Y_del[i], accumulator->a);
		bn_mul(currfVa, currfVa, tmp);
		bn_mod(currfVa, currfVa, accumulator->n);

		//I store consecutive products up to batchSize-1
		bn_null(lpr[i]);    bn_new(lpr[i]);
		bn_gcd_ext_lehme(one, tmp, tmp2, currfVa, accumulator->n);
		assert(bn_cmp_dig(one,1) == RLC_EQ);
		bn_mod(tmp, tmp, accumulator->n);
		bn_copy(lpr[i], tmp);

		//tmpPoly initilization
		bn_null(tmpPoly[i]);  bn_new(tmpPoly[i]);
		if (i==0)
			bn_set_dig(tmpPoly[i], 1);
		else
			bn_set_dig(tmpPoly[i], 0);

		//vA initialization
		bn_null(vD[i]);  bn_new(vD[i]);  bn_set_dig(vD[i], 0);

	}

	for (int s=0; s<batchSize; s++) {

		//sum tmpPoly to vD
		//Add to vA lpr*tmpPoly
		for(int i=0; i<s+1; i++) {
			bn_mul(tmp,tmpPoly[i], lpr[s]);
			bn_mod(tmp,tmp,accumulator->n);
			bn_add(vD[i], vD[i], tmp);
			bn_mod(vD[i], vD[i], accumulator->n);

		}

		if (s<batchSize-1) {
			memmove(tmpPoly+1, tmpPoly, sizeof(bn_t)*(s+1));
			bn_set_dig(tmpPoly[0],0);

			for (int j=0; j<=s; j++) {
					bn_mul(tmp,tmpPoly[j+1],Y_del[s]);
					bn_add(tmp,tmpPoly[j],tmp);
					bn_mod(tmpPoly[j],tmp,accumulator->n);
			}
		}


	}

	free(tmpPoly);

	//Computing the ECP vector from vA. Note we need -V before update.
	g1_t * OmegaDel = (g1_t *)malloc(sizeof(g1_t)*(batchSize));

	for (int i=0; i<batchSize; i++){
		g1_null(OmegaDel[i]); g1_new(OmegaDel[i]);
		g1_mul(OmegaDel[i],  accumulator->V, vD[i]);
	}

	free(vD);

	//TODO: we can skip this step. totAccEl is the relevant parameter
	//Zeroing the trail moved memory
	for(int i=0; i<batchSize; i++)
		bn_set_dig(accumulator->Y[accumulator->totAccEl-batchSize+i], 0);

	//Updating fVa and V
	bn_mul(accumulator->fVa, accumulator->fVa, lpr[batchSize-1]);
	bn_mod(accumulator->fVa, accumulator->fVa, accumulator->n);
	g1_mul(accumulator->V, accumulator->V, lpr[batchSize-1]);

	//Update cached pairing value
	gt_exp(accumulator->eVPt, accumulator->eVPt, lpr[batchSize-1]);

	//Updating the total number of accumulated values
	accumulator->totAccEl = accumulator->totAccEl-batchSize;

	//Update epoch
	accumulator->currentEpoch += 1;
	g1_copy((accumulator->epochs[accumulator->currentEpoch]).V, accumulator->V);
	(accumulator->epochs[accumulator->currentEpoch]).Y_add = NULL;
	(accumulator->epochs[accumulator->currentEpoch]).Y_del = Y_del;
	(accumulator->epochs[accumulator->currentEpoch]).addSize = 0;
	(accumulator->epochs[accumulator->currentEpoch]).delSize = batchSize;
	(accumulator->epochs[accumulator->currentEpoch]).OmegaAdd = NULL;
	(accumulator->epochs[accumulator->currentEpoch]).OmegaDel = OmegaDel;

	free(lpr);
	free(delIdx);
	bn_free(tmp);
	bn_free(currfVa);
	bn_free(tmp2);

	return;

}

//Witness Verification
void zkVerifier(t_state * accumulator, t_proof * proof) {

	unsigned char hash[SHA512_DIGEST_LENGTH];
	int data_size = 0, pos = 0, l;

	gt_t Re;
	g1_t Rsigma;
	g1_t Rrho;
	g1_t Rdeltasigma;
	g1_t Rdeltarho;
	g1_t tmp;
	g1_t Ra;
	g1_t Rb;
	g2_t tmp2;
	gt_t tmpt;
	bn_t tmpb;
	bn_t c;

	gt_null(Re);            gt_new(Re);             gt_set_unity(Re);
	g1_null(Rsigma);        g1_new(Rsigma);
	g1_null(Rrho);          g1_new(Rrho);
	g1_null(Rdeltasigma);   g1_new(Rdeltasigma);
	g1_null(Rdeltarho);     g1_new(Rdeltarho);
	g1_null(tmp);           g1_new(tmp);
	g2_null(tmp2);          g2_new(tmp2);
	gt_null(tmpt);          gt_new(tmpt);
	bn_null(tmpb);          bn_new(tmpb);
	bn_null(c);             bn_new(c);

	//Rsigma = ssigmaX - cTsigma
	bn_neg(tmpb, proof->c);
	bn_mod(tmpb, tmpb, accumulator->n);
	g1_mul_sim(Rsigma, accumulator->X, proof->ssigma, proof->Tsigma, tmpb);

	//Rrho = srhoJ - cTrho (-c = tmpb)
	g1_mul_sim(Rrho, accumulator->J, proof->srho, proof->Trho, tmpb);

	//Rdeltasigma = syTsigma - sdeltasigmaX
	bn_neg(tmpb, proof->sdeltasigma);
	bn_mod(tmpb, tmpb, accumulator->n);
	g1_mul_sim(Rdeltasigma, proof->Tsigma, proof->sy, accumulator->X, tmpb);

	//Rdeltarho = syTrho - sdeltarhoJ
	bn_neg(tmpb, proof->sdeltarho);
	bn_mod(tmpb, tmpb, accumulator->n);
	g1_mul_sim(Rdeltarho, proof->Trho, proof->sy, accumulator->J, tmpb);

	//Re
	//Re *= e(Ec,syPt + cQt)
	g2_mul_sim(tmp2, accumulator->Pt, proof->sy, accumulator->Qt, proof->c);
	pc_map(tmpt, proof->Ec, tmp2);
	gt_mul(Re, Re, tmpt);

	//Re *= e(Z,Pt)^(-sdeltasigma -sdeltarho)
	bn_add(tmpb, proof->sdeltasigma, proof->sdeltarho);
	bn_neg(tmpb, tmpb);
	bn_mod(tmpb, tmpb, accumulator->n);
	gt_exp(tmpt, accumulator->eZPt, tmpb);
	gt_mul(Re, Re, tmpt);

	//Re *= e(Z,Qt)^(-ssigma -srho)
	bn_add(tmpb, proof->ssigma, proof->srho);
	bn_neg(tmpb, tmpb);
	bn_mod(tmpb, tmpb, accumulator->n);
	gt_exp(tmpt, accumulator->eZQt, tmpb);
	gt_mul(Re, Re, tmpt);

	//Re *= e(V,Pt)^(-c)
	bn_neg(tmpb, proof->c);
	bn_mod(tmpb, tmpb, accumulator->n);
	gt_exp(tmpt, accumulator->eVPt, tmpb);
	gt_mul(Re, Re, tmpt);

	if (!proof->isMembership) {

		g1_null(Ra); g1_new(Ra); g1_set_infty(Ra);
		g1_null(Rb); g1_new(Rb); g1_set_infty(Rb);

		//Ra = suP + svK - cEd
		g1_mul(tmp, accumulator->P, proof->su);
		g1_add(Ra, Ra, tmp);
		g1_mul(tmp, accumulator->K, proof->sv);
		g1_add(Ra, Ra, tmp);
		g1_mul(tmp, proof->Ed, proof->c);
		g1_sub(Ra, Ra, tmp);

		//Rb = swK + suEd_1 - cP
		g1_mul(tmp, accumulator->K, proof->sw);
		g1_add(Rb, Rb, tmp);
		g1_mul(tmp, proof->Ed_1, proof->su);
		g1_add(Rb, Rb, tmp);
		g1_mul(tmp, accumulator->P, proof->c);
		g1_sub(Rb, Rb, tmp);

		//Re *= e(K,Pt)^(-sv)
		bn_neg(tmpb, proof->sv);
		bn_mod(tmpb, tmpb, accumulator->n);
		gt_exp(tmpt, accumulator->eKPt, tmpb);
		gt_mul(Re, Re, tmpt);

		//Re *= e(Ed,P)^c
		pc_map(tmpt, proof->Ed, accumulator->Pt);
		gt_exp(tmpt, tmpt, proof->c);
		gt_mul(Re, Re, tmpt);

		//Update data size
		data_size += g1_size_bin(proof->Ed  , 1) +
					 g1_size_bin(proof->Ed_1, 1) +
					 g1_size_bin(Ra         , 1) +
					 g1_size_bin(Rb         , 1);
	}

	//Update data size (not before because Re can be updated by non-membership)
	data_size += g1_size_bin(accumulator->V, 1) +
				 g1_size_bin(proof->Ec     , 1) +
				 g1_size_bin(proof->Tsigma , 1) +
				 g1_size_bin(proof->Trho   , 1) +
				 gt_size_bin(Re            , 1) +
				 g1_size_bin(Rsigma        , 1) +
				 g1_size_bin(Rrho          , 1) +
				 g1_size_bin(Rdeltasigma   , 1) +
				 g1_size_bin(Rdeltarho     , 1);

	//Point normalization
	g1_norm(Rsigma, Rsigma);
	g1_norm(Rrho, Rrho);
	g1_norm(Rdeltasigma, Rdeltasigma);
	g1_norm(Rdeltarho, Rdeltarho);

	//Collecting challenge element in one buffer for hash
	//c = H(V,Ec,Tsigma,Trho,Re,Rsigma,Rrho,Rdeltasigma,Rdeltarho, -  Ed,Ed_1,Ra,Rb);
	unsigned char * data = malloc(sizeof(char)*data_size);

	l = g1_size_bin(accumulator->V, 1); g1_write_bin(data + pos, l, accumulator->V, 1); pos += l;
	l = g1_size_bin(proof->Ec     , 1); g1_write_bin(data + pos, l, proof->Ec     , 1); pos += l;
	l = g1_size_bin(proof->Tsigma , 1); g1_write_bin(data + pos, l, proof->Tsigma , 1); pos += l;
	l = g1_size_bin(proof->Trho   , 1); g1_write_bin(data + pos, l, proof->Trho   , 1); pos += l;
	l = gt_size_bin(Re            , 1); gt_write_bin(data + pos, l, Re            , 1); pos += l;
	l = g1_size_bin(Rsigma        , 1); g1_write_bin(data + pos, l, Rsigma        , 1); pos += l;
	l = g1_size_bin(Rrho          , 1); g1_write_bin(data + pos, l, Rrho          , 1); pos += l;
	l = g1_size_bin(Rdeltasigma   , 1); g1_write_bin(data + pos, l, Rdeltasigma   , 1); pos += l;
	l = g1_size_bin(Rdeltarho     , 1); g1_write_bin(data + pos, l, Rdeltarho     , 1); pos += l;

	if (!proof->isMembership) {

		//Point normalization
		g1_norm(Ra, Ra);
		g1_norm(Rb, Rb);

		l = g1_size_bin(proof->Ed  , 1); g1_write_bin(data + pos, l, proof->Ed  , 1); pos += l;
		l = g1_size_bin(proof->Ed_1, 1); g1_write_bin(data + pos, l, proof->Ed_1, 1); pos += l;
		l = g1_size_bin(Ra         , 1); g1_write_bin(data + pos, l, Ra         , 1); pos += l;
		l = g1_size_bin(Rb         , 1); g1_write_bin(data + pos, l, Rb         , 1); pos += l;

	}

	//Hashing
	SHA512(data, data_size, hash);

	//Compute challenge
	bn_read_bin(c, hash, SHA512_DIGEST_LENGTH);
	bn_mod(c, c, accumulator->n);

	//Print result
	if (proof->isMembership)
		printf("\n\tZK Membership ");
	else
		printf("\n\tZK Non-membership ");

	if (bn_cmp(c, proof->c) == RLC_EQ)
		printf("Witness Verification SUCCEEDED!\n");
	else
		printf("Witness Verification FAILED!\n");

	//Freeing memory
	free(data);

	gt_free(Re);
	g1_free(Rsigma);
	g1_free(Rrho);
	g1_free(Rdeltasigma);
	g1_free(Rdeltarho);
	g1_free(tmp);
	g2_free(tmp2);
	g2_free(tmp2b);
	gt_free(tmpt);
	bn_free(tmpb)
	bn_free(c);

	if (!proof->isMembership) {
		g1_free(Ra);
		g1_free(Rb);
	}

	return;
}

//Witness Verification
t_proof * zkProver(t_state * accumulator, t_witness * wit) {

	unsigned char hash[SHA512_DIGEST_LENGTH];
	int data_size = 0, pos = 0, l;

	bool isMembership;

	bn_t sigma;
	bn_t rho;
	bn_t tau;
	bn_t pi;
	bn_t d_1;
	bn_t deltasigma;
	bn_t deltarho;
	bn_t ry;            bn_t sy;
	bn_t ru;            bn_t su;
	bn_t rv;            bn_t sv;
	bn_t rw;            bn_t sw;
	bn_t rsigma;        bn_t ssigma;
	bn_t rrho;          bn_t srho;
	bn_t rdeltasigma;   bn_t sdeltasigma;
	bn_t rdeltarho;     bn_t sdeltarho;
	bn_t c;
	bn_t tmpb;
	bn_t one;

	g1_t Ec;
	g1_t Ed;
	g1_t Ed_1;
	g1_t Tsigma;
	g1_t Trho;
	g1_t Ra;
	g1_t Rb;
	g1_t Rsigma;
	g1_t Rrho;
	g1_t Rdeltasigma;
	g1_t Rdeltarho;
	g1_t tmp1;

	gt_t Re;
	gt_t tmpt;

	bn_null(sigma);         bn_new(sigma);
	bn_null(rho);           bn_new(rho);
	bn_null(deltasigma);    bn_new(deltasigma);
	bn_null(deltarho);      bn_new(deltarho);
	bn_null(ry);            bn_new(ry);
	bn_null(rsigma);        bn_new(rsigma);
	bn_null(rrho);          bn_new(rrho);
	bn_null(rdeltasigma);   bn_new(rdeltasigma);
	bn_null(rdeltarho);     bn_new(rdeltarho);
	bn_null(sy);            bn_new(sy);
	bn_null(ssigma);        bn_new(ssigma);
	bn_null(srho);          bn_new(srho);
	bn_null(sdeltasigma);   bn_new(sdeltasigma);
	bn_null(sdeltarho);     bn_new(sdeltarho);
	bn_null(c);             bn_new(c);
	bn_null(one);           bn_new(one);
	bn_null(tmpb);          bn_new(tmpb);

	g1_null(Ec);            g1_new(Ec);             g1_set_infty(Ec);
	g1_null(Tsigma);        g1_new(Tsigma);
	g1_null(Trho);          g1_new(Trho);

	g1_null(Rsigma);        g1_new(Rsigma);
	g1_null(Rrho);          g1_new(Rrho);
	g1_null(Rdeltasigma);   g1_new(Rdeltasigma);
	g1_null(Rdeltarho);     g1_new(Rdeltarho);
	g1_null(tmp1);          g1_new(tmp1);

	gt_null(Re);            gt_new(Re);             gt_set_unity(Re);
	gt_null(tmpt);          gt_new(tmpt);


	//Flag to identify membership witnesses
	if (bn_cmp_dig(wit->d,0) == RLC_EQ)
		isMembership = true;
	else
		isMembership = false;

	//Generate random parameters
	bn_rand_mod(sigma      , accumulator->n);
	bn_rand_mod(rho        , accumulator->n);
	bn_rand_mod(deltasigma , accumulator->n);
	bn_rand_mod(deltarho   , accumulator->n);
	bn_rand_mod(ry         , accumulator->n);
	bn_rand_mod(rsigma     , accumulator->n);
	bn_rand_mod(rrho       , accumulator->n);
	bn_rand_mod(rdeltasigma, accumulator->n);
	bn_rand_mod(rdeltarho  , accumulator->n);

	//Ec = C + (sigma+rho)Z
	bn_add(tmpb, sigma, rho);
	bn_mod(tmpb, tmpb, accumulator->n);
	g1_mul(tmp1, accumulator->Z, tmpb);
	g1_add(Ec, Ec, tmp1);
	g1_add(Ec, Ec, wit->C);

	//Tsigma = sigmaX
	g1_mul(Tsigma, accumulator->X, sigma);

	//Trho = rhoJ
	g1_mul(Trho, accumulator->J, rho);

	//deltasigma = ysigma
	bn_mul(deltasigma, wit->y, sigma);
	bn_mod(deltasigma, deltasigma, accumulator->n);

	//deltarho = yrho
	bn_mul(deltarho, wit->y, rho);
	bn_mod(deltarho, deltarho, accumulator->n);

	//Rsigma = rsigmaX
	g1_mul(Rsigma, accumulator->X, rsigma);

	//Rrho = rrhoJ
	g1_mul(Rrho, accumulator->J, rrho);

	//Rdeltasigma = ryTsigma - rdeltasigmaX
	bn_neg(tmpb, rdeltasigma);
	bn_mod(tmpb, tmpb, accumulator->n);
	g1_mul_sim(Rdeltasigma, Tsigma, ry, accumulator->X, tmpb);

	//Rdeltarho = ryTrho - rdeltarhoJ
	bn_neg(tmpb, rdeltarho);
	bn_mod(tmpb, tmpb, accumulator->n);
	g1_mul_sim(Rdeltarho, Trho, ry, accumulator->J, tmpb);

	//Re
	//Re = e(Ec,Pt)^ry  (Ec = C + (sigma+rho)Z)
	bn_add(tmpb, sigma, rho);
	bn_mod(tmpb, tmpb, accumulator->n);
	gt_exp(tmpt, accumulator->eZPt, tmpb);
	gt_mul(tmpt, tmpt, wit->eCPt);
	gt_exp(tmpt, tmpt, ry);
	gt_mul(Re, Re, tmpt);

	//Re *= e(Z,Pt)^(-rdeltasigma - rdeltarho)
	bn_add(tmpb, rdeltasigma, rdeltarho);
	bn_neg(tmpb, tmpb);
	bn_mod(tmpb, tmpb, accumulator->n);
	gt_exp(tmpt, accumulator->eZPt, tmpb);
	gt_mul(Re, Re, tmpt);

	//Re *= e(Z,Qt)^(-rsigma - rrho)
	bn_add(tmpb, rsigma, rrho);
	bn_neg(tmpb, tmpb);
	bn_mod(tmpb, tmpb, accumulator->n);
	gt_exp(tmpt, accumulator->eZQt, tmpb);
	gt_mul(Re, Re, tmpt);

	//Compute non-membership related proof elements
	if (!isMembership) {

		bn_null(tau);   bn_new(tau);
		bn_null(pi);    bn_new(pi);
		bn_null(ru);    bn_new(ru);
		bn_null(rv);    bn_new(rv);
		bn_null(rw);    bn_new(rw);

		bn_null(d_1);   bn_new(d_1);

		g1_null(Ed);    g1_new(Ed);     g1_set_infty(Ed);
		g1_null(Ed_1);  g1_new(Ed_1);   g1_set_infty(Ed_1);
		g1_null(Ra);    g1_new(Ra);     g1_set_infty(Ra);
		g1_null(Rb);    g1_new(Rb);     g1_set_infty(Rb);

		//Generate random parameters
		bn_rand_mod(tau , accumulator->n);
		bn_rand_mod(pi  , accumulator->n);
		bn_rand_mod(ru  , accumulator->n);
		bn_rand_mod(rv  , accumulator->n);
		bn_rand_mod(rw  , accumulator->n);

		//Compute d^-1
		bn_gcd_ext_lehme(one, d_1, tmpb, wit->d, accumulator->n);
		assert(bn_cmp_dig(one,1) == RLC_EQ);
		bn_mod(d_1, d_1, accumulator->n);

		//Ed = dP + tauK
		g1_mul_sim(Ed, accumulator->P, wit->d, accumulator->K, tau);

		//Ed_1 = d^(-1)P + piK
		g1_mul_sim(Ed_1, accumulator->P, d_1, accumulator->K, pi);

		//Ra = ruP + rvK
		g1_mul_sim(Ra, accumulator->P, ru, accumulator->K, rv);

		//Rb = ruEd_1 + rwK
		g1_mul_sim(Rb, Ed_1, ru, accumulator->K, rw);

		//Re *= e(K,Pt)^(-rv)
		bn_neg(tmpb, rv);
		bn_mod(tmpb, tmpb, accumulator->n);
		gt_exp(tmpt, accumulator->eKPt, tmpb);
		gt_mul(Re, Re, tmpt);

		//Update data size
		data_size += g1_size_bin(Ed  , 1) +
					 g1_size_bin(Ed_1, 1) +
					 g1_size_bin(Ra  , 1) +
					 g1_size_bin(Rb  , 1);
		}

		//Update data size
		data_size += g1_size_bin(accumulator->V, 1) +
					 g1_size_bin(Ec	           , 1) +
					 g1_size_bin(Tsigma	       , 1) +
					 g1_size_bin(Trho          , 1) +
					 gt_size_bin(Re            , 1) +
					 g1_size_bin(Rsigma        , 1) +
					 g1_size_bin(Rrho          , 1) +
					 g1_size_bin(Rdeltasigma   , 1) +
					 g1_size_bin(Rdeltarho     , 1);

	//Point normalization
	g1_norm(Ec, Ec);
	g1_norm(Tsigma, Tsigma);
	g1_norm(Trho, Trho);
	g1_norm(Rsigma, Rsigma);
	g1_norm(Rrho, Rrho);
	g1_norm(Rdeltasigma, Rdeltasigma);
	g1_norm(Rdeltarho, Rdeltarho);

	//Collecting challenge element in one buffer for hash
	//c = H(V,Ec,Tsigma,Trho,Re,Rsigma,Rrho,Rdeltasigma,Rdeltarho - Ed,Ed_1,Ra,Rb);
	unsigned char * data = malloc(sizeof(char)*data_size);

	l = g1_size_bin(accumulator->V, 1); g1_write_bin(data + pos, l, accumulator->V, 1); pos += l;
	l = g1_size_bin(Ec            , 1); g1_write_bin(data + pos, l, Ec            , 1); pos += l;
	l = g1_size_bin(Tsigma        , 1); g1_write_bin(data + pos, l, Tsigma        , 1); pos += l;
	l = g1_size_bin(Trho          , 1); g1_write_bin(data + pos, l, Trho          , 1); pos += l;
	l = gt_size_bin(Re            , 1); gt_write_bin(data + pos, l, Re            , 1); pos += l;
	l = g1_size_bin(Rsigma        , 1); g1_write_bin(data + pos, l, Rsigma        , 1); pos += l;
	l = g1_size_bin(Rrho          , 1); g1_write_bin(data + pos, l, Rrho          , 1); pos += l;
	l = g1_size_bin(Rdeltasigma   , 1); g1_write_bin(data + pos, l, Rdeltasigma   , 1); pos += l;
	l = g1_size_bin(Rdeltarho     , 1); g1_write_bin(data + pos, l, Rdeltarho     , 1); pos += l;

	if (!isMembership) {

		//Point normalization
		g1_norm(Ed, Ed);
		g1_norm(Ed_1, Ed_1);
		g1_norm(Ra, Ra);
		g1_norm(Rb, Rb);

		l = g1_size_bin(Ed  , 1); g1_write_bin(data + pos, l, Ed  , 1); pos += l;
		l = g1_size_bin(Ed_1, 1); g1_write_bin(data + pos, l, Ed_1, 1); pos += l;
		l = g1_size_bin(Ra  , 1); g1_write_bin(data + pos, l, Ra  , 1); pos += l;
		l = g1_size_bin(Rb  , 1); g1_write_bin(data + pos, l, Rb  , 1); pos += l;

	}

	//Hashing
	SHA512(data, data_size,  hash);

	//Compute challenge
	bn_read_bin(c, hash, SHA512_DIGEST_LENGTH);
	bn_mod(c, c, accumulator->n);

	//Compute response
	//sy = ry + cy
	bn_mul(tmpb, c, wit->y);
	bn_add(sy, ry, tmpb);
	bn_mod(sy, sy, accumulator->n);

	//ssigma = rsigma + csigma
	bn_mul(tmpb, c, sigma);
	bn_add(ssigma, rsigma, tmpb);
	bn_mod(ssigma, ssigma, accumulator->n);

	//srho = rrho + crho
	bn_mul(tmpb, c, rho);
	bn_add(srho, rrho, tmpb);
	bn_mod(srho, srho, accumulator->n);

	//sdeltasigma = rdeltasigma + cdeltasigma
	bn_mul(tmpb, c, deltasigma);
	bn_add(sdeltasigma, rdeltasigma, tmpb);
	bn_mod(sdeltasigma, sdeltasigma, accumulator->n);

	//sdeltarho = rdeltarho + cdeltarho
	bn_mul(tmpb, c, deltarho);
	bn_add(sdeltarho, rdeltarho, tmpb);
	bn_mod(sdeltarho, sdeltarho, accumulator->n);

	if (!isMembership) {

		bn_null(su);    bn_new(su);
		bn_null(sv);    bn_new(sv);
		bn_null(sw);    bn_new(sw);

		//su = ru + cd
		bn_mul(tmpb, c, wit->d);
		bn_add(su, ru, tmpb);
		bn_mod(su, su, accumulator->n);

		//sv = rv + ctau
		bn_mul(tmpb, c, tau);
		bn_add(sv, rv, tmpb);
		bn_mod(sv, sv, accumulator->n);

		//sw = rw - cdpi
		bn_mul(tmpb, wit->d, pi);
		bn_mod(tmpb, tmpb, accumulator->n);
		bn_mul(tmpb, c, tmpb);
		bn_sub(sw, rw, tmpb);
		bn_mod(sw, sw, accumulator->n);

	}

	//Create proof
	t_proof * proof = (t_proof *)malloc(sizeof(t_proof));

	g1_null(proof->Ec);             g1_new(proof->Ec);
	g1_null(proof->Tsigma);         g1_new(proof->Tsigma);
	g1_null(proof->Trho);           g1_new(proof->Trho);
	bn_null(proof->c);              bn_new(proof->c);
	bn_null(proof->sy);             bn_new(proof->sy);
	bn_null(proof->ssigma);         bn_new(proof->ssigma);
	bn_null(proof->srho);           bn_new(proof->srho);
	bn_null(proof->sdeltasigma);    bn_new(proof->sdeltasigma);
	bn_null(proof->sdeltarho);      bn_new(proof->sdeltarho);

	g1_copy(proof->Ec         , Ec         );
	g1_copy(proof->Tsigma     , Tsigma     );
	g1_copy(proof->Trho       , Trho       );
	bn_copy(proof->c          , c          );
	bn_copy(proof->sy         , sy         );
	bn_copy(proof->ssigma     , ssigma     );
	bn_copy(proof->srho       , srho       );
	bn_copy(proof->sdeltasigma, sdeltasigma);
	bn_copy(proof->sdeltarho  , sdeltarho  );

	if (!isMembership) {

		g1_null(proof->Ed);        g1_new(proof->Ed);
		g1_null(proof->Ed_1);      g1_new(proof->Ed_1);
		bn_null(proof->su);        bn_new(proof->su);
		bn_null(proof->sv);        bn_new(proof->sv);
		bn_null(proof->sw);        bn_new(proof->sw);

		g1_copy(proof->Ed  , Ed  );
		g1_copy(proof->Ed_1, Ed_1);
		bn_copy(proof->su  , su  );
		bn_copy(proof->sv  , sv  );
		bn_copy(proof->sw  , sw  );

	}

	//Membership flag
	proof->isMembership = isMembership;

	//Freeing memory
	free(data);

	bn_free(sigma);
	bn_free(rho);
	bn_free(deltasigma);
	bn_free(deltarho);
	bn_free(ry);
	bn_free(rsigma);
	bn_free(rrho);
	bn_free(rdeltasigma);
	bn_free(rdeltarho);
	bn_free(sy);
	bn_free(ssigma);
	bn_free(srho);
	bn_free(sdeltasigma);
	bn_free(sdeltarho);
	bn_free(c);
	bn_free(one);
	bn_free(tmpb);
	g1_free(Ec);
	g1_free(Rsigma);
	g1_free(Rrho);
	g1_free(Rdeltasigma);
	g1_free(Rdeltarho);
	g1_free(tmp1);
	gt_free(Re);
	gt_free(tmpt);

	if (isMembership) {
		bn_free(tau);
		bn_free(pi);
		bn_free(rtau);
		bn_free(rpi);
		bn_free(ru);
		bn_free(rv);
		bn_free(rw);
		bn_free(d_1);
		g1_free(Ed);
		g1_free(Ed_1);
		g1_free(Ra);
		g1_free(Rb);
		bn_free(stau);
		bn_free(spi);
		bn_free(su);
		bn_free(sv);
		bn_free(sw);
	}

	return proof;
}


//Run some tests
int main(void) {

	clock_t start,end; double cpu_time_used;

	if (core_init() != RLC_OK) {
		core_clean();
		return 1;
	}


	if (pc_param_set_any() != RLC_OK) {
		THROW(ERR_NO_CURVE);
		core_clean();
		return 0;
	}

	pc_param_print();

	//Initialize global accumulator state
	printf("\nAccumulator Initialization:\n");
	t_state * accumulator = malloc(sizeof(t_state));
	init(accumulator);

	bn_t yb; bn_null(yb); bn_new(yb);
	bn_rand_mod(yb, accumulator->n);
	t_witness * wb_y;
	t_witness * w_y;

	///////////////////////////////////////////////////////////////////
	// Testing main primitives
	///////////////////////////////////////////////////////////////////

	//Add random elements
	int batchSize = 1000000;
	printf("->Add Batching %d elements to run experiments...\n", batchSize);

	start = clock();
	basicBatchAdd(accumulator, batchSize);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("~~Batch addition overall took %fs\n",  cpu_time_used);


	printf("\n\nTesting Witness issuing and verification:\n");
	//Non-membership witness for an empty accumulator
	start = clock();
	w_y = issueWitness(accumulator, accumulator->Y[0], MEMBERSHIP);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("~~Issue Membership witness took %fs\n",  cpu_time_used);

	start = clock();
	wb_y = issueWitness(accumulator, yb, NONMEMBERSHIP);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("~~Issue Non-membership witness took %fs\n",  cpu_time_used);

	start = clock();
	verifyWitness(accumulator, w_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("~~Membership verification took %fs\n", cpu_time_used);

	start = clock();
	verifyWitness(accumulator, wb_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("~~Non-Membership verification took %fs\n", cpu_time_used);

	printf("\n\nTesting ZK proof protocol:\n");
	t_proof * proof;
	start = clock();
	proof = zkProver(accumulator, w_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("~~ZK Membership proof creation took %fs", cpu_time_used);
	start = clock();
	zkVerifier(accumulator, proof);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("~~ZK Membership proof verification took %fs\n\n", cpu_time_used);

	free(proof);

	start = clock();
	proof = zkProver(accumulator, wb_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("~~ZK Non-Membership proof creation took %fs", cpu_time_used);
	start = clock();
	zkVerifier(accumulator, proof);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("~~ZK Non-Membership proof verification took %fs\n", cpu_time_used);

	printf("\n\nEmptying the accumulator:\n");
	//Remove all elements
	printf("->Del Batching %d elements...\n", batchSize);

	start = clock();
	basicBatchDel(accumulator, batchSize);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("~~Batch deletion took %fs\n",  cpu_time_used);
	///////////////////////////////////////////////////////////////////


	///////////////////////////////////////////////////////////////////
	//Testing updates withouth Batch Update Protocol
	///////////////////////////////////////////////////////////////////

	printf("\n\nTesting Non-batch Witness Updates:\n");

	printf("\n- Membership witness\n");

	//We issue a new non-membership witness
	free(w_y);
	w_y = issueWitness(accumulator, accumulator->Y[0], MEMBERSHIP);

	//Batch Addition
	batchSize = 10000;
	printf("->Batch Addition... ");
	start = clock();
	batchAdd(accumulator, batchSize);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\t%d additions took %fs\n", batchSize, cpu_time_used);

	//Should FAIL since witness is not updated wrt last batchAdd
	printf("(FAIL) \t");
	verifyWitness(accumulator, w_y);

	printf("->Updating Witness (Non-Batch)... ");
	start = clock();
	updateWitnessNonBatch(accumulator, w_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\tWitness update for %d additions took %fs\n", batchSize, cpu_time_used);

	//Should SUCCEED
	printf("(SUCCEED) ");
	verifyWitness(accumulator, w_y);


	//Batch Deletion
	batchSize = 10000;
	printf("->Batch Deletion... ");
	start = clock();
	//Note that the test element might be removed here
	batchDel(accumulator, batchSize);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\t%d deletions took %fs\n", batchSize, cpu_time_used);

	//Should FAIL
	printf("(FAIL) \t");
	verifyWitness(accumulator, w_y);

	printf("->Updating Witness (Non-Batch)... ");
	start = clock();
	updateWitnessNonBatch(accumulator, w_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\tWitness update for %d deletions took %fs\n", batchSize, cpu_time_used);

	//Should SUCCEED
	printf("(SUCCEED) ");
	verifyWitness(accumulator, w_y);

	printf("\n- Non-membership witness\n");

	//We issue a new non-membership witness
	free(wb_y);
	wb_y = issueWitness(accumulator, yb, NONMEMBERSHIP);

	//Batch Addition
	batchSize = 10000;
	printf("->Batch Addition... ");
	start = clock();
	batchAdd(accumulator, batchSize);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\t%d additions took %fs\n", batchSize, cpu_time_used);

	//Should FAIL since witness is not updated wrt last batchAdd
	printf("(FAIL) \t");
	verifyWitness(accumulator, wb_y);

	printf("->Updating Witness (Non-Batch)... ");
	start = clock();
	updateWitnessNonBatch(accumulator, wb_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\tWitness update for %d additions took %fs\n", batchSize, cpu_time_used);

	//Should SUCCEED
	printf("(SUCCEED) ");
	verifyWitness(accumulator, wb_y);


	//Batch Deletion
	batchSize = 10000;
	printf("->Batch Deletion... ");
	start = clock();
	batchDel(accumulator, batchSize);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\t%d deletions took %fs\n", batchSize, cpu_time_used);

	//Should FAIL
	printf("(FAIL) \t");
	verifyWitness(accumulator, wb_y);

	printf("->Updating Witness (Non-Batch)... ");
	start = clock();
	updateWitnessNonBatch(accumulator, wb_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\tWitness update for %d deletions took %fs\n", batchSize, cpu_time_used);

	//Should SUCCEED
	printf("(SUCCEED) ");
	verifyWitness(accumulator, wb_y);
	///////////////////////////////////////////////////////////////////

	///////////////////////////////////////////////////////////////////
	//Testing non-membership witness batch updates
	///////////////////////////////////////////////////////////////////

	printf("\n\nTesting Witness Update Protocol:\n");

	printf("\n- Membership witness\n");

	//We issue a new non-membership witness
	free(w_y);
	w_y = issueWitness(accumulator, accumulator->Y[0], MEMBERSHIP);

	//Batch Addition
	batchSize = 10000;
	printf("->Batch Addition... ");
	start = clock();
	batchAdd(accumulator, batchSize);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\t%d additions took %fs\n", batchSize, cpu_time_used);

	//Should FAIL since witness is not updated wrt last batchAdd
	printf("(FAIL) \t");
	verifyWitness(accumulator, w_y);

	printf("->Updating Witness (Batch)... ");
	start = clock();
	updateWitness(accumulator, w_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\tWitness update for %d additions took %fs\n", batchSize, cpu_time_used);

	//Should SUCCEED
	printf("(SUCCEED) ");
	verifyWitness(accumulator, w_y);


	//Batch Deletion
	batchSize = 10000;
	printf("->Batch Deletion... ");
	start = clock();
	//Note that the test element might be removed here
	batchDel(accumulator, batchSize);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\t%d deletions took %fs\n", batchSize, cpu_time_used);

	//Should FAIL
	printf("(FAIL) \t");
	verifyWitness(accumulator, w_y);

	printf("->Updating Witness (Batch)... ");
	start = clock();
	updateWitness(accumulator, w_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\tWitness update for %d deletions took %fs\n", batchSize, cpu_time_used);

	//Should SUCCEED
	printf("(SUCCEED) ");
	verifyWitness(accumulator, w_y);


	printf("\n- Non-membership witness\n");

	//We issue a new non-membership witness
	free(wb_y);
	wb_y = issueWitness(accumulator, yb, NONMEMBERSHIP);

	//Batch Addition
	batchSize = 10000;
	printf("->Batch Addition... ");
	start = clock();
	batchAdd(accumulator, batchSize);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\t%d additions took %fs\n", batchSize, cpu_time_used);

	//Should FAIL since witness is not updated wrt last batchAdd
	printf("(FAIL) \t");
	verifyWitness(accumulator, wb_y);

	printf("->Updating Witness (Batch)... ");
	start = clock();
	updateWitness(accumulator, wb_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\tWitness update for %d additions took %fs\n", batchSize, cpu_time_used);

	//Should SUCCEED
	printf("(SUCCEED) ");
	verifyWitness(accumulator, wb_y);


	//Batch Deletion
	batchSize = 10000;
	printf("->Batch Deletion... ");
	start = clock();
	batchDel(accumulator, batchSize);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\t%d deletions took %fs\n", batchSize, cpu_time_used);

	//Should FAIL
	printf("(FAIL) \t");
	verifyWitness(accumulator, wb_y);

	printf("->Updating Witness (Batch)... ");
	start = clock();
	updateWitness(accumulator, wb_y);
	end = clock();
	cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("\tWitness update for %d deletions took %fs\n", batchSize, cpu_time_used);

	//Should SUCCEED
	printf("(SUCCEED) ");
	verifyWitness(accumulator, wb_y);
	///////////////////////////////////////////////////////////////////


	///////////////////////////////////////////////////////////////////
	// Testing multiple-epochs updates
	///////////////////////////////////////////////////////////////////
	printf("\n\nTest multiple epochs witness update:\n");

	free(wb_y);
	free(w_y);

	w_y = issueWitness(accumulator, accumulator->Y[0], MEMBERSHIP);
	wb_y = issueWitness(accumulator, yb, NONMEMBERSHIP);

	printf("->Freshly issued witnesses verification...\n");
	printf("(SUCCEED) ");
	verifyWitness(accumulator, w_y);
	printf("(SUCCEED) ");
	verifyWitness(accumulator, wb_y);

	printf("->10 random Add and Delete operations..\n");
	for(int i=0; i<10; i++){
		batchAdd(accumulator, 100);
		batchDel(accumulator, 100);
	}

	printf("->Updating witnesses (Batch)...\n");
	updateWitness(accumulator, w_y);
	updateWitness(accumulator, wb_y);

	printf("->Verification...\n");
	printf("(SUCCEED) ");
	verifyWitness(accumulator, w_y);
	printf("(SUCCEED) ");
	verifyWitness(accumulator, wb_y);
	///////////////////////////////////////////////////////////////////

	//Freeing memory
	free(w_y);
	free(wb_y);
	free_accumulator(accumulator);

	printf("\n\nDone!\n");

	return 0;
}
