---
rg: 2
id: subshift-crossed-product-ring-has-bass-stable-rank-at-most-two
kind: claim
title: Does the algebraic crossed product LC(X,K) ⋊ Z of an infinite minimal subshift have Bass stable rank at most 2?
distinct_from:
  vaserstein-local-stable-range-normal-subgroups: that is Vaserstein's theorem giving standard normal subgroups below the stable rank; this asks whether its hypothesis at n = 3 holds for the subshift ring.
artifacts:
  - research/artifacts/sk-stable-rank-b-stepanov-route-2026-09-13.md
---

**OPEN.** Let `X` be an infinite minimal subshift, `K` a field and `R = LC(X,K) ⋊_T Z`. Is `sr(R) ≤ 2`? Stronger: is
`sr(R) = 1`? That would be the algebraic analog of Putnam's theorem that `C(X) ⋊ Z` has stable rank one.

**Why it was asked.**
- Bass, Publ. Math. IHES 22 (1964), Theorem 4.2(e): "If H ⊂ GL(r,A) is normalised by E(r,A), then, for a unique ideal
  q, E(r,A,q) ⊂ H and the image of H in GL(r,A/q) lies in the center". It holds for r > max(n,2) when n defines a
  stable range for GL(A), i.e. when sr(A) ≤ n.
- Vaserstein, LNM 854 (1981), Theorems 1 and 4 (p. 456), as imported in `vaserstein-local-stable-range-normal-subgroups`.
- For a simple ring with centre a field, `sr(R) ≤ 2` would then give: every subgroup of `GL_3(R)` normalized by
  `E_3(R)` is central or contains `E_3(R)`.

**No longer needed for that purpose.** `subshift-elementary-group-simple-stepanov-proof` gets the same conclusion from
Stepanov's Theorem 4.4, a dimension count, and no stable rank. The question stays open as ring theory.

## Attempts
- **Transfer from C\*-algebras.** Putnam (see also Archey–Phillips, arXiv:1505.00725) proves topological stable rank one
  for `C(X) ⋊ Z`. Herman–Vaserstein equate topological and Bass stable rank only for C\*-algebras. Ara–Pardo
  (arXiv:math/0609354, p. 1): "if E is a graph such that no cycle has an exit and E contains some cycle, then the stable
  rank of C*(E) is 1 ... but the stable rank of L(E) is 2 by Theorem 2.8". The one-loop graph gives `K[x,x^{-1}]`. Dies
  at the approximation step, which has no algebraic analog.
- **Direct limits.** `sr` of a directed union is at most the liminf of the stages. `R` is finitely generated, so a
  directed union of subrings equals one stage. The C\*-algebraic A𝕋 structure is only approximate. Dies.
- **Corners over a tower base.** For a clopen base `Y` with minimal return time `h_min`, `R ≅ P M_H(C) P` with
  `C = e_Y R e_Y` (the induced system) and `P ≥ 1_C^{⊕h_min}`. A corner bound `sr ≤ ⌈(sr(C) − 1)/h_min⌉ + 1` would give
  `sr(R) ≤ 2` from any finite bound on `sr(C)`. But `C` is a ring of the same class, so the argument is circular without
  an a priori finite bound. The corner bound was not verified from a source either. Dies here.
- **Two colorings.** For two clopen bases whose seams are far apart, every element of propagation `w` lies in
  `R_(Y_1) + R_(Y_2)`, and both summands are locally matricial (`sr = 1`). This "dimension one" picture resembles Bass's
  `sr ≤ 2` for Dedekind rings, but no known theorem turns such a sum decomposition into a stable-rank bound. Dies at that
  step.
- **Exchange property.** If `R` were an exchange ring, separativity results of Ara–Goodearl–O'Meara–Pardo (Israel J.
  Math. 105 (1998)) would constrain `sr(R)`. That constraint was not verified from the source here. Single elements of
  `K[u^{±1}] ⊂ R` pass the exchange test by blockwise projections along a tower, but seam-crossing elements were not
  handled. Dies at the exchange property.
- **Evidence for `sr = 1`.** Pairs `(a, e_W)` with `a` left invertible off `W` complete to units, because bounded
  propagation keeps every cokernel vector within the maximal return time of `W`. No obstruction was found, and no proof.
