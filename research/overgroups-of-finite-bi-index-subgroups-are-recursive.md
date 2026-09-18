---
rg: 2
id: overgroups-of-finite-bi-index-subgroups-are-recursive
kind: claim
title: Every subgroup containing a finitely generated finite bi-index subgroup is recursive, so the centralizer test for permutation HNN realizations fails on finite bi-index edge groups with identity edge map
distinct_from:
  finite-bi-index-subgroups-have-decidable-membership: that decides membership in the finite bi-index subgroup itself; this decides membership in every overgroup of it, with no generating set of the overgroup given, and applies it to kill a reduction.
  permutation-hnn-realization-of-type-a-actor-is-a2: that proves the centralizer reduction C_Γ(π) ≤_m K; this shows the reduced set is recursive for a whole class of realizations, so the reduction cannot witness a non-recursive kernel there.
  type-a-hnn-realization-with-unsolvable-word-problem: that asks for a realization with unsolvable word problem; this closes one sufficient test for it on the class its "What to try next" item 1 proposes.
---

**ESTABLISHED** by `overgroups-of-finite-bi-index-subgroups-are-recursive-proof`
(elementary; not independently reviewed; no novelty claimed).

**(1) Overgroups.** Let `Γ` be a finitely generated group with solvable word
problem, and let `D <= Γ` be finitely generated with `|D \ Γ / D| < ∞`. Then every
subgroup `H` with `D <= H <= Γ` is recursive as a set of words. (The decision
procedure depends on `H` through finitely many double coset representatives, so it
is not uniform in `H`.)

**(2) The centralizer test dies on identity edge maps.** Let `Γ ↷ X`, `D_1, D_2`,
`ψ` and `π` be as in `permutation-hnn-realization-of-type-a-actor-is-a2`. Suppose
`D_1 = D_2 = D`, `ψ = id`, and `D` has finitely many double cosets in `Γ` (for
instance `D = Stab_Γ(x_0)` in a type (A) actor). Then `C_Γ(π)` is recursive.

So the sufficient test of `type-a-hnn-realization-with-unsolvable-word-problem`
(non-recursive `C_Γ(π)`) cannot succeed on "What to try next" item 1 of that node.
That includes the Mikhailova plan of placing `F_2 x F_2` inside `N_D(H)/H` for a
two-point stabilizer `H`: however large the centralizer, it is a finite union of
`D`-double cosets.

**(3) Inner edge maps reduce to (2) for the image, not for the test.** Suppose
`D_1` has finite bi-index and `ψ` is induced by some `δ in Γ` (`δ d δ^-1 = ψ(d)` as permutations, `d in D_1`), then
`π' = δ^-1 π` centralizes `D_1` and `<Γ, π'> = <Γ, π>`. So the image, and whether
the kernel is recursive, are those of the identity realization `(D_1, id, π')`, whose
centralizer test is dead by (2). The set `C_Γ(π)` itself need not contain `D_1`; it
only contains `C_(D_1)(δ)`, and it is not claimed recursive.

**What survives.**
- The word problem of `<Γ, π>` for such realizations is not decided here.
- The test survives when `C_Γ(π)` contains no finite bi-index subgroup, e.g. for
  edge maps `ψ ≠ id` whose fixed subgroup `{d in D_1 : ψ(d) = d}` has infinitely many
  double cosets, and for edge groups of infinite bi-index.
- A witness in item 1 needs a many-one reduction to the kernel whose reduced set is
  not a subgroup containing `D_1`.
