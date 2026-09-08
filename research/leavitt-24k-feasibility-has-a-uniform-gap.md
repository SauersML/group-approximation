---
rg: 2
id: leavitt-24k-feasibility-has-a-uniform-gap
kind: claim
title: Some 24k relation set has a dimension-uniform normalized-HS gap
distinct_from:
  leavitt-24k-feasibility-vanishes: that is the opposite branch, vanishing of every infimum; exactly one of the two holds and neither is proved.
  binary-leavitt-hyperlinear-iff-24k-feasible: that is the proved equivalence connecting these branches to hyperlinearity; this is one of the two matrix alternatives it leaves open.
  leavitt-24k-first-relation-has-exact-finite-model: that proves the first relation is NOT such a set, by exhibiting an exact GL_3(F_8) solution of it; this asks for some other set that is.
artifacts:
  - research/artifacts/leavitt-24k-relative-unitary-reduction-2026-09-08.md
---

**OPEN.**  In the notation of `binary-leavitt-hyperlinear-iff-24k-feasible`,
exhibit `m` and `eta > 0` with

```text
max_(r in T_m) || pi_(k,U)(r) - I ||_(2,24k) >= eta
```

for every `k >= 1` and every `U in U(24k)`.  By that criterion this is
equivalent to nonhyperlinearity of the binary Leavitt unit group, which is
nonsofic (`openai-leavitt-unit-nonsofic`), and so would produce the first
nonhyperlinear group.

## Attempts

- **The operator-norm analogue is already true, and does not transfer.**  If
  every operator-norm infimum vanished, a diagonal choice would embed `H` in
  the unitary group of a matrix norm quotient with `c` nontrivial
  (`||C_k - I||_op = sqrt 3`), and such an image is MF, contradicting the
  supplied obstruction.  So some operator-norm gap exists.  The norms are not
  comparable in the needed direction: `diag(-1,1,...,1)` is at operator
  distance `2` and normalized-HS distance `2/sqrt d` from the identity.
- **One relation is not enough, provably.**  The necessary bound `(LR2)`
  forces a commutator of size `1/sqrt 2 - o(1)`, but
  `leavitt-24k-first-relation-has-exact-finite-model` gives an exact
  `GL_3(F_8)` solution of that relation, so `m` must be large enough to see
  genuinely more of `ker q`.
- **One explicit packet now has a positive minimum in every fixed
  dimension.** The nine native words of
  `leavitt-has-an-explicit-finite-c-killing-certificate` compile the
  Bleak--Quick presentation of Thompson's `V` and force `c=1` in every
  exact finite-dimensional unitary model. Their maximum expanded length
  is `52920`. Thus this single packet has positive minimum at each
  fixed `24k`; the remaining issue is a positive bound independent of
  `k`. The earlier compactness argument only supplied a possibly
  dimension-dependent relation stage `m(k)`.
- **The four-word coefficient packet has an exact countermodel.** The claim
  `leavitt-24k-kernel-packet-excludes-scalar-field-models` supplies
  `r_*`, `R_v`, `R_0`, and `R_sum` in the marked kernel. Two new rows
  reject the first-relation F8 model at normalized-HS distance `sqrt(2)`.
  The exact first-relation control now has an algebraic construction in
  dimension `4608=24*192`, recorded in
  `leavitt-first-relation-has-a-4608-dimensional-seed`. However,
  `leavitt-four-word-packet-has-an-exact-24-dimensional-model` gives
  an explicit four-swap relative permutation satisfying all four words
  already at `k=1`, and hence at every amplification. This packet cannot
  witness a gap. Its image is `S_3 x C_2^2`; the derived root `d` has
  order three. Adding the true native relation `d^2=1` excludes that
  model, while the augmented packet needs separate analysis.
- **The coefficient class has a quantitative obstruction.** The claim
  `leavitt-kernel-packet-has-a-finite-coefficient-rank-gap` proves a
  normalized-rank gap of `1/15` for three packet words in literal
  elementary matrices over finite-dimensional characteristic-two
  coefficients. It does not yield a normalized-HS gap for arbitrary
  complex relative unitaries. Constructing an appropriate additive
  coefficient receiver inside such models remains missing.
- **Tracial moment relaxations cannot supply the bound, at any level.**
  `tracial-moment-relaxations-cannot-certify-the-leavitt-gap` proves that
  `y_w = 1_(q(w)=1)` is feasible at every finite level of the ordinary
  tracial moment relaxation in these four generators, satisfies traciality,
  every true relation of `H` and the prescribed regular characters on both
  frozen factors, and makes the squared defect energy exactly zero. So every
  level has optimum zero, and no sum-of-squares certificate whose only
  premises are positivity, traciality, the group relations and those
  character values can give a positive `eta`. The dead route is
  `leavitt-uniform-gap-via-tracial-moment-certificate`. A proof must use a
  genuine finite-dimensionality input, as
  `leavitt-24k-models-avoid-blockwise-error-basis-normalizers` does inside
  its restricted class.
- **The unrestricted lower bound remains open.** A mechanism must survive
  amplification, since the criterion's models are closed under tensoring
  with the identity. The packet is a finite test set, not a claimed
  presentation or a proved witness for this claim.
