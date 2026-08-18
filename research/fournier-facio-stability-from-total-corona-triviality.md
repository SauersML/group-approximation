---
rg: 2
id: fournier-facio-stability-from-total-corona-triviality
kind: route
title: Every corona representation of the group is trivial, so the correcting homomorphism is the trivial one
target: fournier-facio-group-matricially-stable
requires: [normal-kazhdan-defect-non-mf, fournier-facio-torsion-free-skeleton, defect-normally-generates-torsion-free-quotient]
artifacts:
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
  - GroupApproximation/Sofic/NormalKazhdanCompressionObstruction.lean
  - docs/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md
---

## Why sufficient

Let `G` be the Fournier-Facio group with the compression core
`C = (Gamma, t_1, c in J)` of `fournier-facio-torsion-free-skeleton`.  The
stability hypothesis is not attacked on its own terms at all; it falls out of
the obstruction that was already in hand, because that obstruction kills
*everything*.

**1. An asymptotic homomorphism is a corona representation.**  Let
`phi_n : G -> U(k_n)` be an operator-norm asymptotic homomorphism,
`‖phi_n(g) phi_n(h) - phi_n(gh)‖ -> 0` for all `g, h`.  The classes
`rho(g) = [phi_n(g)]` in the norm matrix corona
`NormMatrixCStarCorona` — the `ell_infty` product of the matrix algebras
modulo the ideal of sequences whose norm tends to zero, the quotient being
taken along the **cofinite** filter — satisfy `rho(g) rho(h) = rho(gh)`
exactly, because the defect lies in the null ideal, and each `rho(g)` is
unitary.  (`phi_n(1)` need not be `1`, but a unitary with
`phi_n(1)^2 - phi_n(1) -> 0` has `phi_n(1) -> 1`.)  So `rho` is a genuine
group homomorphism `G ->* unitary (NormMatrixCStarCorona X)` with
`X n = ` the model of dimension `k_n`.  Conversely `[u_n] = 1` in the corona
says precisely `‖u_n - 1‖ -> 0`.

**2. The killing theorem applies with `K = G`.**  By the established form of
`defect-normally-generates-torsion-free-quotient` the compression defect is
not merely large but the whole group: `C.defectNormal = <<pi(S)>>^G = G`.
Take `K = G` itself.  It is normal, nontrivial, contained in
`C.defectNormal`, and it has property (T), since `G` does — no inheritance
step is needed, which is exactly what the extreme form of that claim buys.
`normal-kazhdan-defect-non-mf` therefore applies in its elementwise form
(`KazhdanCompressionCore.normalKazhdan_le_normMatrixCStarCoronaKernel`:
`K <= rho.ker` for **every** `rho : E ->* unitary (NormMatrixCStarCorona X)`),
and gives `G <= rho.ker`: every homomorphism from `G` to the unitary group
of a norm matrix corona is trivial.

**3. The correction is the trivial homomorphism.**  Combining, for every `g`,
`[phi_n(g)] = rho(g) = 1`, that is `‖phi_n(g) - 1‖ -> 0`.  Put
`pi_n = 1 : G -> U(k_n)`, an honest group homomorphism for every `n`.  Then
`‖phi_n(g) - pi_n(g)‖ -> 0` for every `g in G`.  That is matricial stability
in Dadarlat's sense — quantified, as the definition demands, over *all*
asymptotic homomorphisms and not merely the separating ones.  This
establishes [[fournier-facio-group-matricially-stable]].

## What is actually proved is stronger, and that is the point

The conclusion is not "the correcting homomorphisms exist" but "the
correcting homomorphisms may be taken trivial": every operator-norm
asymptotic representation of `G` is **asymptotically trivial**.  Stability
here is degenerate — it holds because `G` has no nontrivial
finite-dimensional approximation of any kind, not because approximate
representations of `G` can be repaired.  Anyone reading
`fournier-facio-group-matricially-stable` as evidence that `G` behaves like
the uniformly stable higher-rank lattices would be reading it backwards.

## What this costs: the stability route is no longer independent

`torsion-free-non-mf-from-matricial-stability` was recorded as a genuine
alternative to `torsion-free-non-mf-from-normal-kazhdan-defect`, on the
ground that if the normal-Kazhdan obstruction had a gap the stability route
would still reach the root.  **That independence is gone.**  This route
proves the stability prerequisite *from* the normal-Kazhdan obstruction, so
the two routes into the root now share their analytic half, and a gap in
`normal-kazhdan-defect-non-mf` would take both down together.  The note is
recorded in that route's own body as well, so the graph does not report two
complete routes as two independent confirmations.

## Certification boundary

The analytic step is machine-checked and unconditional in this repository
(`normal-kazhdan-defect-non-mf-proof`).  The two group-theoretic inputs are
not formalized: the compression core is read off the published construction,
and `defectNormal = G` is a written Hull argument whose Lean boundary is
`DefectRoutingData`.  So this route inherits exactly the trust surface of the
primary route — no more, and no less.  Nothing here is a new analytic fact;
the content is the observation that the obstruction already in hand is total,
and that a total obstruction is a stability theorem read from the other side.
