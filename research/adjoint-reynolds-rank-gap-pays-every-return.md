---
rg: 2
id: adjoint-reynolds-rank-gap-pays-every-return
kind: claim
title: Every attempted adjoint return pays the full packet Reynolds rank gap
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that computes the rank difference between the two Reynolds projections; this converts it into a normalized-HS lower bound against every returned copy and relates adjoint error to ordinary word error.
  finite-group-multiplicity-mismatch-pays-hs-energy: that compares two representations of one finite group on the original Hilbert space; this compares commutant projections for nested packet groups on the adjoint Hilbert space.
  compressor-covariant-packet-reynolds-return: that must create a return from finitely many group relations while retaining the exact non-CE model; this proves that any such return automatically has the required dimension-free payment.
---

Use the notation of `predicate-rank-jump-forces-adjoint-reynolds-gap`.  Thus
`R_A,R_B` are the Reynolds projections on `End(H_-)`, normalized as a Hilbert
space of dimension `d^2`, and forbidden packet mass `q` gives

```text
(rank R_A-rank R_B)/d^2 >= (3/(4D^2K)) q^2.          (ARR1)
```

For every unitary `V` on the adjoint Hilbert space,

```text
||R_A-V R_B V^*||_(HS,d^2)^2
  >= (rank R_A-rank R_B)/d^2
  >= (3/(4D^2K)) q^2.                                (ARR2)
```

For the fixed support packet the constant is `3/16`.

There is no hidden adjoint-dimension loss when `V=Ad_W` comes from a unitary
`W` on `H_-`.  For unitaries `U,U'` on `H_-`,

```text
||Ad_U-Ad_(U')||_(HS,d^2)^2 <= 2||U-U'||_(2,d)^2.    (ARR3)
```

Consequently, suppose a proposed covariance gadget supplies a finite list of
unitary words `a_h` indexed by a finite packet group `H`, such that

```text
R_A=(1/|H|) sum_h Ad_(a_h),
R_B=(1/|H|) sum_h Ad_(rho(h)).                        (ARR4)
```

Then every return word `W` obeys

```text
(3/(4D^2K))q^2
 <= (2/|H|) sum_h ||a_h-W rho(h) W^*||_2^2.          (ARR5)
```

Thus a bounded word/certificate realization of `(ARR4)` immediately gives the
dimension-free relator payment sought by the contextual multiplicity route.
The remaining difficulty is algebraic: constructing that covariance without
collapsing the exact non-CE packet model.
