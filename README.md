## About
This repository contains an implementation of the Dynamic Universal Accumulator Scheme detailed in 

[Dynamic Universal Accumulator with Batch Update over Bilinear Groups](https://eprint.iacr.org/2020/777)

by _Giuseppe Vitto_ and _Alex Biryukov_.

## Functionalities
The following accumulator scheme features are implemented:
* Batch operations for accumulator updates;
* Membership and non-membership witness verification;
* Epoch-based Public Batch Witness Updates;
* Zero-Knowledge Proof of Knowledge of a valid membership and non-membership witness.

## Dependencies
The following libraries are needed for compilation
* [RELIC toolkit](https://github.com/relic-toolkit/relic)
* [PBC](https://crypto.stanford.edu/pbc/)
* [GMP](https://gmplib.org/)
* [OpenSSL](https://github.com/openssl/openssl)

## Compilation
To compile
```
gcc main.c -o acc -I/usr/local/include/relic/ -lrt /usr/local/lib/libpbc.a /usr/local/lib/librelic_s.a /usr/local/lib/libgmp.a -lgmp -lrelic -lpbc -lssl -lcrypto -ggdb -Wall

```

