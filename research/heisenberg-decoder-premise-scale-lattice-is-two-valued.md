---
rg: 2
id: heisenberg-decoder-premise-scale-lattice-is-two-valued
kind: claim
title: Every premise scale of the Leavitt-corner decoder gives either the goal verbatim or nonhyperlinearity
distinct_from:
  coherent-heisenberg-decoder-is-marked-nonhyperlinearity: that proves the stated normalized-HS decoder is equivalent to nonhyperlinearity; this classifies all premise scales, including the operator-norm/full-support class the consuming route actually uses, where the decoder is the MF-radical goal itself.
  affine-leavitt-decoder-interface-is-mark-collapse-equivalent: that shows a payment-type interface (ADI1-ADI2) adds nothing beyond marked-root collapse; this concerns the pure corner-output decoder and shows that no change of premise scale makes it a proper decomposition step.
  binary-jacobson-typed-square-decoder-is-still-target-equivalent: that is the analogous audit for the Jacobson head root and its square decoder; this is the Leavitt-corner output with a scale-by-scale premise table.
  simple-torsion-non-mf-iff-trivial-mf-characters: that reformulates the goal by MF characters; this is a logical audit of the decoder interface and of the full-support-HS-decoder route.
artifacts:
  - research/artifacts/heisenberg-decoder-premise-scale-lattice-proof-2026-09-18.md
---

**OPEN** (demoted 2026-09-18 at landing: the referee stage returned no votes
for this result, so it has not survived review).  The proof is kept as the
attempt artifact
`research/artifacts/heisenberg-decoder-premise-scale-lattice-proof-2026-09-18.md`.
Not independently reviewed.

**Claimed logical firewall.**  Let `R=L_(F_2)(1,2)`, let `G`
be `H=EL_20(R)` or `Delta=St_20(R)`, and let `z` be the involutory root
`x_13(s_1t_1)` (or its image in `H`).  Fix a finite generating set containing
`z` and a countable presentation.

For a class `Pi` of unitary asymptotic representations `U_n:G->U(k_n)` that
keep `z` away from `1`, let `D_z^Pi` be the decoder assertion restricted to
`Pi`.  It says that every member of `Pi` supplies corners `P_n` of uniformly
positive normalized trace and contractions `S_0,S_1,T_0,T_1` satisfying the
Leavitt relations `(CHD1)-(CHD2)` with corner-normalized HS defect tending
to zero.

**(E) Emptiness principle.**  For every class `Pi`,

```text
D_z^Pi   <=>   Pi is empty.
```

This holds for any defect norm and keep-away norm in the premise.  It also
holds with no positivity of `tr P_n` and when the output defects are measured
in operator norm.  The reason is the dimension-free cyclic floor `(CHD3)`: no
finite corner inhabits the output.

**(L) Scale table.**

```text
premise scale (defect / keep-away)          Pi empty  <=>
exact finite-dimensional representations    true for H (vacuous)
normalized Schatten-p, any p in [1,inf)      Rad_hyp(G)=G   (H: nonhyperlinear)
normalized HS with trace profile delta_e     H nonhyperlinear
operator norm / operator norm                Rad_MF(G)=G    (Delta: the goal)
operator norm / normalized HS (full support) Rad_MF(G)=G    (Delta: the goal)
```

All normalized Schatten scales coincide on unitary words, because
`||X||_op<=2` makes the normalized `p`-norms uniformly equivalent on small
and on separated values.

**(C) Route circularity.**  The route
`property-t-free-leavitt-via-full-support-hs-decoder` feeds the decoder only
the full-support operator-norm class produced by
`torsion-normal-generator-has-full-support-corona-core`.  On that class the
decoder is literally `Rad_MF(Delta)=Delta`.  In its stated HS form it is
`Rad_hyp(G)=G`, which is strictly at least as strong as the goal; for `H` it
is the flagship `non-hyperlinear-group` instance.  The route's other inputs
add nothing to the logic, because `(E)` already rules out the output.
Therefore no premise-scale variant of `coherent-heisenberg-multiplicity-decoder`
decomposes the goal.

**Death step for the class.**  Changing the *scale* of a universal decoder
with a Leavitt-corner *output* cannot help.  The output dies at `(CHD3)` at
every scale, so the decoder always collapses to emptiness of its premise, and
the table shows the only nonvacuous emptiness statements are the goal or
nonhyperlinearity.  Surviving approaches must change the output instead.  The
output must become an inhabitable finite-matrix inequality with an explicit
finite relator window and constant.  One example is the payment dichotomy of
`paired-same-reservoir-boundary-lemma`, in the format of
`mf-radical-words-have-linear-certificates`.

No Property `(T)`, stability or character-rigidity input is used.

## Attempts

- **2026-09-18, cyclic floor plus Schatten collapse, corona lifting and the
  full-support core (swarm-0917 d-ptf-heis).**  The worker's route (the
  dimension-free floor `(CHD3)` for `(E)`, Malcev for exact representations,
  normalized Schatten equivalence and Radulescu--Pestov amplification for the
  tracial scales, corona lifting and
  `torsion-normal-generator-has-full-support-corona-core` for the
  operator-norm scales) is kept as the attempt artifact
  `research/artifacts/heisenberg-decoder-premise-scale-lattice-proof-2026-09-18.md`.
  Referee reason for demotion: no referee votes were returned for this
  established result (votes lost), so it did not survive review.  Restore the
  route once a full referee pass survives.
