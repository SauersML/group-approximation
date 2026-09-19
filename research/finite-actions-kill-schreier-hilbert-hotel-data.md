---
rg: 2
id: finite-actions-kill-schreier-hilbert-hotel-data
kind: claim
title: On every finite action of a finitely generated group, an automorphism-compressed subgroup has the same image as the subgroup, so Schreier Hilbert-hotel data never exist
distinct_from:
  schreier-hilbert-hotel-compression-data-exist: that asserts (HH) data exist; this proves they do not, for every Gamma, alpha, H, Gamma_0 and g.
  schreier-hilbert-hotel-data-give-matricial-compression-rings: that is the implication (HH) => R1-R5, which stays true; this shows its hypothesis is never met.
  finitely-generated-rf-automorphism-mapping-torus-is-rf: that uses Mal'cev periodicity on characteristic quotients to get residual finiteness of the torus; this uses periodicity of precomposition on Hom(Gamma, Sym(F)) for one finite action, with no characteristic quotient, and turns it into an orbit identity.
  lef-mapping-torus-iff-stage-liftable-automorphism: that is the LEF criterion for mapping tori; this is a statement about coset spaces of Gamma alone, and it needs no approximation of the extended action.
artifacts:
  - research/finite-actions-kill-schreier-hilbert-hotel-data-proof.md
  - research/schreier-hilbert-hotel-data-give-matricial-compression-rings.md
  - research/schreier-hilbert-hotel-compression-data-exist.md
---

**ESTABLISHED.** Proof: `finite-actions-kill-schreier-hilbert-hotel-data-proof` (elementary; lane
proof, not independently reviewed).

## Theorem

Let `Gamma` be a finitely generated group, `alpha in Aut(Gamma)`, and `Gamma_0 <= Gamma` a subgroup
with `A = alpha(Gamma_0) <= Gamma_0`.

- **(a) Periodicity lemma.** For every action `rho : Gamma -> Sym(F)` on a finite set,
  `rho(A) = rho(Gamma_0)`. In particular `A` and `Gamma_0` have the same orbits on `F`.
- **(b) Local transfer.** Let `X` be a transitive `Gamma`-set with base point `x_0` whose pointed
  Schreier graph is a limit of pointed finite `Gamma`-sets; equivalently `H = Stab(x_0)` is a Chabauty
  limit of finite-index subgroups (for instance `H` is profinitely closed). Suppose `Gamma_0` is
  finitely generated. If `y in Gamma_0 x_0` has a finite `A`-orbit, then `x_0 in A y`, so `y in A x_0`.
- **(c) (HH) is refuted.** No data as in `schreier-hilbert-hotel-compression-data-exist` exist. The
  hypotheses `alpha(H) = H`, (IS) and the finite presentation of anything are not even used.

## What dies

**Invariant:** the permutation `rho -> rho o alpha` of the finite set `Hom(Gamma, Sym(F))`. It has
finite order `k`, so `rho(alpha^k(Gamma_0)) = rho(Gamma_0)`, and the chain
`Gamma_0 >= A >= ... >= alpha^k(Gamma_0)` collapses in every finite image.

**Death step:** the finite `A`-orbit of `g x_0` is a closed piece of the Schreier graph. It is copied
exactly into a finite approximant, where `A` and `Gamma_0` have the same orbits. So the copy contains
the image of `x_0`, and injectivity on the ball puts `x_0` in `A g x_0`, contradicting
`g notin A H`.

**Class killed:** every Schreier Hilbert-hotel witness for `matricial-compression-ring-exists`,
through `matricial-compression-ring-via-schreier-hilbert-hotel`, for every host. This contains the dead
classes of Attempts 1-5 on `schreier-hilbert-hotel-compression-data-exist` (normal images, Noetherian
and free hosts, small stabilizers, inner twists, the Grigorchuk-Lysenok hotel) and the open candidate
`Z wr_(Z[1/2]) BS(1,2)` of its Attempt 6. The coset space is a Hilbert hotel for `A` inside
`Gamma_0 x_0`, and finite actions admit no Hilbert hotel for a compressed subgroup.

## What survives

- `matricial-compression-ring-exists` itself is untouched. Only the permutation (Bernoulli
  tensor-lamp) route to it dies.
- A repair of the ring reduction must replace the finite `Gamma`-sets `Gamma/H_n` of its Step 7 by
  models on which `Gamma` does **not** act by exact permutations of a finite set, for example
  approximate (sofic) actions. The lemma needs exact actions: it uses that `Hom(Gamma, Sym(F))` is a
  finite set permuted by `rho -> rho o alpha`. The ultraproduct embedding (R1) itself only gives
  approximate homomorphisms of `R_0`, so the lemma does not transfer to (R1)-(R5) directly.
- `exact-kazhdan-radical-kernel-cannot-be-lef` (EKL1) stays OPEN. Its announced refutation through
  (HH) is withdrawn.
