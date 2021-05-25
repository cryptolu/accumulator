//Accumulator data Structures
typedef struct s_epoch {
	g1_t V;
	bn_t * Y_add;
	int addSize;
	bn_t * Y_del;
	int delSize;
	g1_t * OmegaAdd;
	g1_t * OmegaDel;
} t_epoch;


typedef struct s_state {
	g1_t  V;
	g1_t  P;
	g1_t  X;
	g1_t  Z;
	g1_t  J; //Y in the paper
	g1_t  K;
	g2_t  Pt;
	g2_t  Qt;
	gt_t ePPt;
	gt_t eZPt;
	gt_t eZQt;
	gt_t eKPt;
	gt_t eVPt;
	bn_t  n;
	bn_t  a;
	bn_t * Y;
	int totAccEl;
	bn_t fVa;
	t_epoch * epochs;
	int currentEpoch;
} t_state;


typedef struct s_witness {
	bn_t y;
	g1_t C;
	bn_t d;
	int epoch;
	gt_t eCPt;
} t_witness;


typedef struct s_proof {
	g1_t Ec;
	g1_t Ed;
	g1_t Ed_1;
	g1_t Tsigma;
	g1_t Trho;
	bn_t c;
	bn_t sy;
	bn_t su;
	bn_t sv;
	bn_t sw;
	bn_t ssigma;
	bn_t srho;
	bn_t sdeltasigma;
	bn_t sdeltarho;
	bool isMembership;
} t_proof;

//Used for qsort
int compare( const void* a, const void* b ) {
	if( *(int*)a == *(int*)b ) return 0;
	return *(int*)a < *(int*)b ? -1 : 1;
}


//Utility function To select random indexes without repetition
//(used to select random added elements during a batchDelete)
int * randomIdx(int n, int batchSize){

	//Check if n is greater than batchSize
		assert(batchSize <= n);

		srand(time(NULL));

		int * res = (int *)malloc(sizeof(int)*(batchSize+1));
		int * indx = (int *)malloc(sizeof(int)*n);

		int tmp, rndIdx;

		//Do a random shuffle of [0,n-1]
		for (int i = 0; i < n; i++)
				indx[i] = i;

		for (int i = 0; i < batchSize; i++) {
				tmp = indx[i];
				rndIdx = rand() % n;
				indx[i] = indx[rndIdx];
				indx[rndIdx] = tmp;
		}

		//Select only first batchSize indexes
		for (int i = 0; i < batchSize; i++)
				res[i] = indx[i];

		//Set last element to n
		res[batchSize] = n;

		free(indx);

		return res;
}


//Feeing memory
void free_accumulator(t_state * accumulator) {

	for(int i=0; i<accumulator->currentEpoch; i++) {
				free((accumulator->epochs[i]).Y_add);
				free((accumulator->epochs[i]).Y_del);
				free((accumulator->epochs[i]).OmegaAdd);
				free((accumulator->epochs[i]).OmegaDel);
		}

		free((accumulator->epochs[accumulator->currentEpoch]).OmegaAdd);
		free((accumulator->epochs[accumulator->currentEpoch]).Y_add);
		free((accumulator->epochs[accumulator->currentEpoch]).OmegaDel);
		free((accumulator->epochs[accumulator->currentEpoch]).Y_del);

		free(accumulator->epochs);
		free(accumulator->Y);
		free(accumulator);

	return;
}
