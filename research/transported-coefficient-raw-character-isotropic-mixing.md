---
rg: 2
id: transported-coefficient-raw-character-isotropic-mixing
kind: claim
title: The comb-transported coefficient involutions mix the four raw character sectors isotropically
distinct_from:
  pauli-carrier-membership-decoder: This is an exact finite-packet block-mass calculation for the two transported coefficient involutions; the decoder asks for asymptotic recovery of the transported carrier inside the raw binary algebra.
  full-packet-bicommutant-synchronization: This computes two fixed operators against four raw character cuts; bicommutant synchronization quantifies over every raw-packet commutant unitary in arbitrary microstates.
artifacts:
  - experiments/atlas_transported_coefficient_raw_character_mixing.py
  - experiments/atlas-transported-coefficient-raw-character-mixing.json
---

Let `F_epsilon`, `epsilon in {+-1}^2`, be the four trace-`1/8` raw
coefficient-character cuts in the two-sheet corner `q` of the exact binary
Leavitt-prefix atlas model.  Let `B_0,B_1` be the two raw coefficient
involutions and let

```text
T_i = comb^* B_i comb.
```

Order the four characters arbitrarily and write `J` for the `4 x 4` all-ones
matrix.  Then the exact canonical-trace block-mass matrices

```text
K_i(epsilon,delta) = tau(F_epsilon T_i F_delta T_i)
```

are

```text
K_0 = (20 I + J) / 256,
K_1 = ( 4 I + J) / 128.
```

Equivalently, every diagonal block of `T_0` has squared Hilbert--Schmidt mass
`21/256` and every off-diagonal block has mass `1/256`; for `T_1` the values
are `5/128` and `1/128`.

Because `tau(F_epsilon)=1/8`, normalizing a row by the raw-sector trace gives
the substochastic kernels

```text
P_0 = (20 I + J) / 32,
P_1 = ( 4 I + J) / 16.
```

Their constant-vector eigenvalues are respectively `3/4` and `1/2`, the
fraction of one raw sector that survives in the raw coefficient corner after
transport.  On the three-dimensional centered character space their
eigenvalues are respectively `5/8` and `1/4`.

Thus comb transport is neither a permutation nor arbitrary leakage on the raw
`C_2^2` character packet: each transported coefficient involution induces an
exact isotropic `a I + b J` mixer.  This is useful diagnostic structure for
the carrier decoder, but it does not by itself prove that the transported
carrier lies in the raw binary algebra.
