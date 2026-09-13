---
rg: 2
id: effective-subshift-invariant-measure-existence-is-pi01
kind: claim
title: For effectively closed subshifts of a finitely generated group with solvable word problem, existence of an invariant probability measure is Pi-zero-one
distinct_from:
  lef-recognition-has-a-pi2-upper-bound: that bounds LEF recognition for recursive group presentations at Pi-zero-two; this bounds a dynamical property of effectively presented subshifts at Pi-zero-one.
artifacts:
  - research/artifacts/un-open-6-tarski-complexity-2026-09-13.md
---

**ESTABLISHED** (unreviewed; route `effective-subshift-invariant-measure-existence-is-pi01-proof`).

**Setting.**
- `Γ` is a finitely generated group with a finite symmetric generating set `S` and solvable word problem, so the balls
  `B_n` of the word metric are computable. `A` is a finite alphabet, and `Γ` acts on `A^Γ` by `(g·x)(h) = x(g⁻¹h)`.
- For an index `e`, `W_e` is the recursively enumerable set of finite patterns enumerated by program `e`, and
  `X_e = {x ∈ A^Γ : no translate of a pattern of W_e occurs in x}` (an effectively closed subshift; every closed
  subshift with an r.e. forbidden list arises this way).

**Claim.** The set `{e : X_e carries a Γ-invariant Borel probability measure}` is `Π⁰₁`. Concretely there is a
computable predicate `LP(e,n)` (feasibility of a finite rational linear program) such that `X_e` carries an invariant
probability measure iff `LP(e,n)` holds for every `n`.

**Model tests.**
- `Γ = Z`, `W_e = ∅`: the full shift; every `LP(e,n)` is feasible (uniform Bernoulli measure). Correct.
- `W_e` forbids every single letter: `X_e = ∅`; `LP(e,n)` is infeasible once one forbidden letter is enumerated. Correct.
- `Γ = F_2` and a subshift model of the boundary action `F_2 ↷ ∂F_2`: no invariant measure, so some `LP(e,n)` fails.
  Consistent with paradoxicality of the boundary action.

**Credit.** The argument is the standard compactness argument for pattern frequencies; statements of this kind are
folklore in effective symbolic dynamics (compare Hochman, Invent. Math. 176 (2009), on recursive properties of
multidimensional subshifts). No novelty is claimed for this node; it is the input for
`effective-free-group-kazhdan-lef-type-is-pi01`.

**Review (un-verify, 2026-09-13): PASS.** `LP(e,n)` is a finite rational feasibility problem, computable from `(e,n)`; measure ⇒ programs by cylinder masses; programs ⇒ measure by diagonal limits of consistent marginals, Kolmogorov extension, the summed level-`n` equations giving `μ(s·C) = μ(C)` for `C` at `B_m`, `m ≤ n−1`, and zero mass on every enumerated forbidden translate. Folklore credit (Hochman) appropriate. See `research/artifacts/un-review-2026-09-13-part9.md` §1.
