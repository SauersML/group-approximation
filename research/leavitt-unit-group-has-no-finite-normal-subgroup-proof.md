---
rg: 2
id: leavitt-unit-group-has-no-finite-normal-subgroup-proof
kind: route
title: No finite quotients plus the unit span plus the center theorem
target: leavitt-unit-group-has-no-finite-normal-subgroup
requires: [leavitt-gl-equals-el-and-perfect-unit-group, leavitt-unit-group-algebra-surjects-onto-leavitt, leavitt-center-is-coefficient-field]
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
  - GroupApproximation/Leavitt/ElementaryNoFiniteQuotients.lean
  - GroupApproximation/Leavitt/UnitAdditiveSpan.lean
  - GroupApproximation/Leavitt/LeavittSimplicity.lean
---

## Direct proof

Write `R = L_(F_2)(1,2)`, `G = R^x`.

**Step 1 — no nontrivial finite quotient.**
`elementaryGroup_finite_quotient_trivial` (`ElementaryNoFiniteQuotients.lean`)
proves that for `[Infinite R]`, strong two-sided division, and
`3 <= Fintype.card iota`, every group homomorphism `EL_iota(R) -> Q` with `Q`
finite is trivial.  The first prerequisite supplies
`G ~= GL_3(R) = EL_3(R)` through the three-leaf prefix code, which is exactly
three indices; `LeavittFamily.infinite` and
`LeavittSimplicity.exists_mul_mul_eq_one` supply the ring hypotheses.

**Step 2 — no proper finite-index subgroup.**  If `H <= G` had index
`n < infinity`, left translation on `G/H` would give `phi : G -> Sym(G/H)`
with finite target, hence trivial by Step 1, hence `gH = H` for every `g` and
`H = G`.

**Step 3 — `Z(G) = Z(R)\{0}`.**  If `c in Z(G)` then `c` commutes with every
element of `R^x`, and the second prerequisite is the unit-span theorem
`unitAdditiveSpan_eq_top` — the units of `R` span `R` additively, which is
precisely why the evaluation `F_2[R^x] ->> R` is onto — so `c` commutes with
all of `R`.  Hence `Z(G) = Z(R) n R^x`.

Conversely let `c in Z(R)`, `c != 0`.  Strong division gives `a, b` with
`a c b = 1`; centrality rewrites this as `c(ab) = 1` and as `(ab)c = 1`, so
`c in R^x`.  Therefore `Z(G) = Z(R)\{0}`, and `Z(R)` is a field.

**Step 4 — `Z(G) = 1`.**  The third prerequisite gives `Z(R) = F_2`, so
`Z(R)\{0} = {1}`.

**Step 5 — `Delta(G) = 1`.**  If `g` has a finite conjugacy class then
`C_G(g)` has finite index, so `C_G(g) = G` by Step 2, so `g in Z(G) = 1`.

**Step 6 — no nontrivial finite normal subgroup.**  Let `N` be normal and
finite.  Conjugation gives `G -> Aut(N)`, a homomorphism to a finite group,
trivial by Step 1.  So every element of `N` is centralized by every element of
`G`, i.e. `N <= Z(G) = 1`.

## Where the trust surface is

Steps 1, 2, 3, 5, 6 are internal, and Steps 1 and 3 rest on theorems
kernel-checked in this repository.  Step 4 is the only external input, and it
is isolated in `leavitt-center-is-coefficient-field`.  Without it the chain
still yields "every finite normal subgroup lies in `Z(R)^x`, a finite subgroup
of the multiplicative group of a field of characteristic two, hence cyclic of
odd order" — which is not `1` until one knows `Z(R)` carries no `F_4`.
