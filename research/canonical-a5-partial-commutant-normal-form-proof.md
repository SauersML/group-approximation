---
rg: 2
id: canonical-a5-partial-commutant-normal-form-proof
kind: route
title: Average one partial lamp intertwiner and expose its full copy commutant
target: canonical-a5-window-leaves-a-partial-commutant-cocycle
requires:
  - finite-subgroup-near-regular-has-large-regular-core
  - simple-lamp-normalizers-have-unitary-multiplicity-fibers
  - finite-cylinder-mixed-traces-kill-normalizer-holonomy
---

Apply the finite-subgroup regular-core theorem to `Q_Y=K^Y`, giving `(APC1)`
after flexible exactification.  For one arrow, extend its partial coordinate
map to `bar alpha:Y->Y` and put `C=P_(bar alpha)^*U`.  Exact covariance says
that `C` commutes with `lambda(K^D)`, and the tensor factorization of the
regular representation gives `(APC3)`.

Under `(APC4)`, average

```text
B=|K^D|^(-1) sum_(q in K^D) lambda(q)^* C lambda(q).
```

Then `B` lies in the commutant and `||B-C||_2<=epsilon`.  Contractivity of
`B` and unitarity of `C` give `||B^*B-1||_2<=2epsilon`.  In a finite matrix
commutant the polar partial isometry extends to a unitary `V`, and
`||B-V||_2<=||B^*B-1||_2`, proving `(APC5)`.  Substitution in
`U_gU_h approximately U_(gh)` gives `(APC6)--(APC7)`.

Tensoring a partial coordinate implementation with an arbitrary actor
microstate proves `(APC8)` and the trace assertion by factorization.  A
normalizer of a rank-one diagonal masa is monomial.  By contrast, `r`
commuting binary labels leave a block of rank at least `m/2^r`; putting a
Fourier matrix in that block preserves every label, while its overlap with
any monomial on the block is at most the inverse square root of the block
rank.  Counting the identity contribution off the block gives the global
bound `(APC9)`.  Therefore only a growing separating copy PVM can eliminate the
residual algebra.  The finite-cylinder theorem then supplies the stated
phase-to-permutation upgrade once a coherent actor table is available.

Formula `(APC10)` is a direct tensor calculation.  Every added left-regular
packet acts trivially on `H_v`, its coordinate permutation commutes with
`v_g`, and normalized traces factor.  Therefore no fixed number of replicated
packets constrains the external actor cocycle.

Finally, amplification sends every evaluated group word `w(rho)` to
`w(rho) tensor 1_M`.  Functional calculus and finite algebraic combinations
preserve the same tensor factor.  Hence any copy PVM produced functorially
from a fixed relation retains the full matrix commutant `M_M(C)`, proving the
amplification fence for relation-only proposals.
