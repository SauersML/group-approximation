---
rg: 2
id: real-symplectic-solutions-kill-no-deligne-schur-class
kind: claim
title: A nonsingular equation over Sp4(Z) that is solvable in Sp4(R) kills no Schur class seen by Deligne's triple multiplier
distinct_from:
  projective-unitary-classes-vanish-on-schur-kernel: that makes multipliers pulled back from quotients of products of finite-dimensional unitary groups vanish on the Schur kernel, and such multipliers never see Deligne's class on Sp4(Z); this uses the non-compact host Sp4(R), which carries the triple cover itself, and prunes exactly the equations with a real symplectic solution.
  sp4-schur-kernel-meets-the-deligne-triple-class: that is the open existence of a killing equation; this is a necessary condition any witness must satisfy.
  amenable-t-shape-adjunctions-kill-no-schur-class: that prunes by the shape of the equation over torsion-free coefficient subgroups; this prunes by real symplectic solvability, with any coefficients and any shape.
---

**Statement.** Let `1 -> Z -> E -> Q -> 1` be central with multiplier
`alpha`, let `w in Q * <t>` be nonsingular with `Q -> (Q * <t>)/<<w>>`
injective, and write `K_2(Q, w)` for its Schur kernel. Suppose there are a
group `H`, a central extension `1 -> Z -> H^ -> H -> 1` and a homomorphism
`rho : Q -> H` whose pullback of `H^` is `E`, compatibly with `Z`.

(RS1) If the equation `w_rho(T) = 1`, obtained by applying `rho` to the
coefficients, has a solution `T in H`, then `alpha_H(K_2(Q, w)) = 0`.

(RS2) **Deligne.** Take `Q = Sp_4(Z)`, `H = Sp_4(R)`, `H^` its connected
three-fold cover and `E = E_3`, the inverse image of `Sp_4(Z)`
(`deligne-triple-cover-fd-central-invisibility`). Every nonsingular
`w in Sp_4(Z) * <t>` with a solution `T in Sp_4(R)` has
`alpha_H(K_2(Sp_4(Z), w)) = 0`. So a witness for
`sp4-schur-kernel-meets-the-deligne-triple-class` is an equation with no
real symplectic solution.

**Why it matters.** Finite quotients, finite-dimensional projective
representations and amenable packets are all blind to Deligne's class
(Attempt 4 of the target: "no invariant can prune it"). The real group
`Sp_4(R)` is not blind: it carries the triple cover. (RS2) is the first
pruning invariant for the direct search that sees the class, and it is
checkable numerically and certifiable by interval arithmetic.

**Scope.** (RS1) is elementary and uses only item 2 of
`central-extension-kl-schur-criterion`. The numerical census in
`research/artifacts/kl-deligne-real-solvability-census-2026-09-13.md` is
recorded separately and is not part of this claim.

DERIVATION
real-symplectic-solutions-kill-no-deligne-schur-class-proof
