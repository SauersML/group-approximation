---
rg: 2
id: binary-jacobson-typed-pi-selector-vacuity-proof
kind: route
title: Correct the ambient rank and apply the no-head gap to the sequential selector
target: binary-jacobson-typed-pi-selector-is-still-target-equivalent
requires:
  - binary-jacobson-active-cycle-generates-rank-three
  - binary-jacobson-steinberg-cover-is-elementary
  - finitely-presented-marked-involution-corona-gap
  - binary-jacobson-head-sector-has-native-two-qubit-packet
  - opnorm-common-intertwiner-pi-gap-is-sparse-terminal
---

First fix the ambient type.  The equality

```text
<a_12,x_12(1),x_23(1),x_31(1)>=EL_3(J)
```

holds in the upper-left block of `EL_5(J)`; it is a subgroup-generation
statement, not a presentation containing the external packet words.  Every
word in those four matrices fixes coordinates four and five, whereas
`x_14(Q)` and `x_43(1)` have nonzero off-block entries.  Hence the latter
cannot be evaluated as words in a presentation tuple for that `EL_3(J)`.
By `binary-jacobson-steinberg-cover-is-elementary`, the coherent ambient
interface is instead one fixed finite presentation of

```text
Gamma_T=St_5(J)~=EL_5(J),
```

in which both the named active cycle and the four target words are
evaluated.

Assume first that the corrected selector exists and that a norm-corona
homomorphism of `Gamma_T` retains `w_T`.  Choose coordinate lifts of the
fixed presentation.  Their presentation defects `epsilon_n` tend to zero,
and on a subsequence the rounded negative head cuts are nonzero.  Apply the
selector.  On its nonzero reducing projections `P_n`, the source tuple lies
in `M_2 tensor I`, so

```text
s_4(C_1^(n),C_2^(n),C_3^(n),C_4^(n))=0.                 (1)
```

The corrected literal target is the native two-qubit packet, and hence

```text
||s_4(D_1^(n),D_2^(n),D_3^(n),D_4^(n))||_op=8.          (2)
```

The common contractions `R_n` satisfy

```text
||R_n R_n^*-P_n||_op
  +sum_j ||D_j^(n)R_n-R_n C_j^(n)||_op
    <= omega(epsilon_n) -> 0.                            (3)
```

Equations `(1)--(3)` contradict
`opnorm-common-intertwiner-pi-gap-is-sparse-terminal`, even when every
`P_n` has rank one.  Thus the selector implies `(JPTE1)`.

Conversely assume `(JPTE1)`.  Apply
`finitely-presented-marked-involution-corona-gap` to this presentation and
mark.  There is `gamma>0` such that

```text
P_-(U)!=0  =>  Def_R(U)>=gamma.                          (4)
```

Choose once and for all a finite word package containing the active-cycle
occurrences and the native packet, and choose any deterministic operation
of the permitted syntactic form, for example fixed spectral cuts followed
by the polar of a named raw-cycle compression.  Also choose any modulus
tending to zero.  If a sequence had presentation defect tending to zero,
then eventually its defect would be below `gamma`; by `(4)` its rounded
negative head cut would be zero.  Therefore no sequence satisfies the
antecedent on which the current selector requires its typed outputs and
`(JPI1)` estimate.  Its entire asserted semantics is vacuous.

This proves the reverse implication and the equivalence.  Notice that the
argument uses the selector's actual sequence-level phrase "presentation
defect tends to zero."  Replacing it by a genuinely calibrated pointwise
statement would require fixing the occurrence formula and its numerical
estimate in advance, rather than existentially choosing both under the
full-presentation no-head antecedent.

