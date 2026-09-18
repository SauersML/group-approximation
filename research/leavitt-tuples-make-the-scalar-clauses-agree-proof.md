---
rg: 2
id: leavitt-tuples-make-the-scalar-clauses-agree-proof
kind: route
title: Refinement is an isomorphism of elementary groups sending scalars to scalars, and stably trivial scalars are elementary at all large ranks
target: leavitt-tuples-make-the-scalar-clauses-agree
requires:
  - leavitt-refinement-identifies-unstable-k2-levels
  - ring-gate-k1-clause-is-unstable
  - leavitt-resolvent-k-theory-is-shifted-rational-k-theory
---

**Item 1.**
- Let `T : R^N -> R^(N+d-1)` fix the first `N - 1` coordinates and send the last coordinate `x` to `(σ_1* x, ..., σ_d* x)`.
  Let `U` send `(y_1, ..., y_d)` in the last `d` coordinates to `Σ σ_i y_i`. Then `U T = I_N` and `T U = I_(N+d-1)`, so
  `α(A) = T A U` is a unital ring isomorphism.
- **Refinement.** Voronetsky's Proposition 1 applies to `M_(N+d-1)(R)`, with the standard family and the coarse family
  that merges the last `d` idempotents. Proposition 1 merges two adjacent idempotents, so it is applied `d - 1` times.
  The intermediate families stay Morita equivalent (Voronetsky, p. 3), and the smallest fine family has `N + 1 >= 4`
  members (gq-referee-b, C1). Item 1 needs only surjectivity, which Voronetsky gives for `n >= 3`. So it gives an isomorphism `D : St_N(R) -> St_(N+d-1)(R)` with `φ D = α φ`. This is the `d`-tuple form of the
  refinement in `leavitt-refinement-identifies-unstable-k2-levels`, item 1.
- `D` is onto, so `α(E_N(R)) = α(φ(St_N)) = φ(D(St_N)) = E_(N+d-1)(R)`.
- `α(λ I_N) = T λ U = λ T U = λ I_(N+d-1)`, because `λ` is central.
- Hence `λ I_N in E_N` if and only if `λ I_(N+d-1) in E_(N+d-1)`.

**Item 2.**
- Let `λ in ker ι`. Then `[λ ⊕ I_(M-1)] = 0` in `K_1(R)`. So `λ ⊕ I_(M-1) in E_M(R)` for all large `M`, since
  `E(R) = [GL(R), GL(R)]` is the kernel and the stabilizations are compatible.
- `λ I_M` is the product of the `M` conjugates of `λ ⊕ I_(M-1)` by permutation matrices. Signed permutation matrices lie
  in `E_M(R)`, and the sign conjugations fix diagonal matrices. So `λ I_M in E_M(R)` for all large `M`.
- Given `N >= 3`, choose a large `M ≡ N (mod d - 1)`. Item 1, applied `(M - N)/(d - 1)` times, gives `λ in Λ_N(R)`.
- The converse inclusion up to `N`-th powers is item 2 of `ring-gate-k1-clause-is-unstable`. A subgroup of a
  finitely generated abelian group is finitely generated, and `Λ_N -> ker ι`, `λ -> λ^N`, has kernel contained in
  `{±1}` (gq-referee-b, C2). So the two
  groups are finitely generated together.

**Item 3.**
- By item 2, a Leavitt-tuple design with `ker ι` not finitely generated has `Λ_N` not finitely generated. So it is not
  in loophole (i).
- For `R_L`, `K_1(R_L) = Z` on `[N+1]` and every rational scalar is `0`
  (`leavitt-resolvent-k-theory-is-shifted-rational-k-theory`). So `ker ι = Q^x`, and `Λ_N(R_L) = Q^x`.

**Item 4.** From a Leavitt `(1, d)`-tuple, `[1] = Σ [σ_i σ_i*] = d[1]`.
