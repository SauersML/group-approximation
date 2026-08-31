---
rg: 2
id: four-sheet-monomial-mixing-reduces-to-commutant
kind: claim
title: Up to four monomial carrier sheets cannot repair the Jacobson head
distinct_from:
  pauli-swap-coherence-reduces-to-the-commutant-gate: that treats one fixed two-sheet Pauli swap; this allows arbitrary generator-dependent permutations of as many as four sheets
  presentation-defect-does-not-control-off-commutant-mass: that permits unrestricted frame motion; this isolates a finite normalizer quotient for which presentation defect has a fixed detection threshold
  bounded-coherence-toeplitz-gauges-cannot-retain-head: that begins after all sheet permutations have vanished; this supplies that reduction
---

Let `2<=k<=4` and decompose

```text
H=H_1 directSum ... directSum H_k
```

into equal-dimensional carrier sheets. Suppose every Toeplitz carrier
matrix `A_s` is block diagonal and every relative gauge is block monomial:

```text
Z_s=D_s P_s,                                            (FSM1)
```

where `D_s` is block diagonal in `rho(F_N)'` and `P_s` is the unitary of
a permutation `p_s in S_k`. Put `U_s=A_sZ_s`.

If

```text
delta(U)<2/sqrt(k),                                     (FSM2)
```

then `p_s=1` for every presentation generator. Hence all gauges in
`(FSM1)` lie in the carrier commutant, and the bounded- or unbounded-
coherence conclusions apply exactly as before.

More generally, for arbitrary fixed `k`, condition `(FSM2)` forces the
permutations `p_s` to define a genuine homomorphism

```text
EL_28(J) -> S_k.                                        (FSM3)
```

Thus finite-sheet monomial mixing is classified by finite permutation
quotients, not by an analytic approximation problem. Perfectness kills
`(FSM3)` for `k<=4` because `S_k` is solvable. The first discrete sector
not eliminated by this argument is an `A_5`-type five-sheet quotient.
This statement does not assert that such a quotient exists.

Continuous block rotations are not monomial and remain outside this
firewall.

DERIVATION
moved-sheet-hamming-cost-and-perfect-image-proof
