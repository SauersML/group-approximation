---
rg: 2
id: higman-group-algebras-embed-in-division-rings-proof
kind: route
title: Feed the characteristic-free Hughes-free vertex rings into the graph-of-rings embedding over the rank-two free edge
target: higman-group-algebras-embed-in-division-rings
requires:
  - fsp-graph-of-rings-and-linnell-extension-imports
  - higman-bs-amalgam-has-hughes-free-division-rings
  - higman-group-splits-as-amalgams-over-free-subgroups
artifacts:
  - research/artifacts/gk3-nonrf-hosts-2026-09-14.md
---

## Proof

**1. Division ring embedding.**
* [[higman-group-splits-as-amalgams-over-free-subgroups]] gives `H = G_1 *_(F_ac) G_2`, a graph of groups with
  two vertices and one edge.
* [[higman-bs-amalgam-has-hughes-free-division-rings]] shows `G_1` and `G_2` are locally indicable and that
  `k[G_1]`, `k[G_2]` have Hughes-free division rings, for every division ring `k`. The edge group `F_ac` is a
  subgroup, so it is locally indicable too.
* Item 6 of [[fsp-graph-of-rings-and-linnell-extension-imports]] then embeds `k[H]` in a division ring `D`.

This is the source's proof of Proposition 3.14, with its characteristic-zero vertex input replaced by the
characteristic-free one.

**2. Stable finiteness.** `M_n(k[H]) <= M_n(D)`, and `M_n(D)` is directly finite: it is Artinian, and `BA = I_n`
makes right multiplication by `A` an injective endomorphism of a finite-length module, hence surjective. So
`AB = I_n`. Direct finiteness passes to subrings with the same identity.

**3. Linear automata.** Let `tau` be an injective `F_q`-linear cellular automaton on `(F_q^n)^H`, given by a
matrix `A in M_n(F_q[H])` acting through its local rule.
* **The inverse is a linear automaton on the image.** `X = tau((F_q^n)^H)` is a closed linear shift-invariant
  subspace. `tau` is a continuous bijection from a compact space onto `X`, so its inverse `sigma : X -> (F_q^n)^H`
  is continuous, linear and `H`-equivariant. By uniform continuity there is a finite window `W` with
  `sigma(x)(1)` determined by `x|_W`.
* **The rule extends.** The rule `f : P -> F_q^n` is well defined on the subspace `P = {x|_W : x in X}` of
  `(F_q^n)^W`, and it is linear because `sigma` is. Extend it to a linear map `f~` on all of `(F_q^n)^W`.
* **A left inverse matrix.** `f~` is the local rule of a linear automaton `sigma~` on the full shift with
  `sigma~|_X = sigma`, so `sigma~ ∘ tau = id`. Linear automata correspond to matrices over `F_q[H]`, composition
  to multiplication, as in [[stable-finiteness-failure-refutes-surjunctivity]]. So there is
  `B in M_n(F_q[H])` with `BA = I_n` in the order convention of that correspondence.
* **Surjectivity.** By 2, `AB = I_n`, so `tau ∘ sigma~ = id` and `tau` is surjective.

**4. Refutation.** [[higman-group-algebra-not-stably-finite]] asks for `A, B in M_n(F_p[H])` with
`BA = I_n != AB`. Item 2 with `k = F_p` excludes this. QED

**Checks.**
* The order of multiplication in the matrix correspondence does not matter: direct finiteness of `M_n(k[H])` is
  symmetric in the two factors.
* Item 3 uses only compactness, linearity and finite-dimensional linear algebra. The same equivalence (stable
  finiteness of `K[G]` iff every injective linear cellular automaton on `V^G`, `V` finite-dimensional, is
  surjective) is published as Ceccherini-Silberstein--Coornaert, *Cellular Automata and Groups*, Corollary 8.15.6.
  It is quoted as Theorem 2.1 in Ceccherini-Silberstein--Coornaert--Phung, Groups Geom. Dyn. 19 (2025), 495--503,
  which was read on 2026-09-14.
* **Novelty.** The source's Proposition 3.14 (arXiv:2303.08165v4) is characteristic zero only, and a web search on
  2026-09-14 found no positive-characteristic division embedding or stable finiteness result for Higman's group.
  That is not a literature proof of novelty.
* Not independently re-derived by a second lane.
