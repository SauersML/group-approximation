---
rg: 2
id: field-crossed-product-rank-condition-survival-proof
kind: route
title: Følner counts, finite Galois quotients and the affiliated-operator ring of a measure-preserving crossed product give stably finite or dimension-counted images
target: field-crossed-product-rank-condition-survival-cases
requires: []
artifacts:
  - research/artifacts/twisted-linear-entropy-profiles-2026-09-17.md
---

Artifact Section 3, Proposition 3.1.

A failure of the rank condition is a finite identity `AB = I_d` (`A` of size `d x r`, `B` of size `r x d`,
`r < d`). The rank condition pulls back along unital ring homomorphisms into nonzero rings.

1. **(a)**
   - `K*G -> K*Q` is a unital ring homomorphism when `σ` and `α` are inflated from `Q`.
   - Over amenable `Q`, write `e_i = sum_j λ_{ij} v_j` with `λ_{ij}` supported in `S`. Then
     `⊕_{g∈F,i} K u_g e_i`, of dimension `d|F|`, lies in the span of the `r|FS|` vectors `u_h v_j`, `h ∈ FS`.
   - Right Følner sets give `d <= r`.
2. **(b)**
   - Coefficients algebraic over `F = K^G` have finite `G`-orbits, so they generate a finite `G`-stable
     `L ⊇ F`. `G` acts on `L` through a finite `Q`.
   - `L ⋊ G -> L ⋊ Q` is a unital ring homomorphism, and `L ⋊ Q` is finite dimensional over `F`, so the
     dimension count gives `r >= d`.
3. **(c)**
   - Put `X = Emb(K_0, C)` with the invariant measure. Then `π(a)(φ) = φ(a)` is an equivariant ring homomorphism
     `K_0 -> L^0(X)`.
   - `L^0(X) ⊆ U(M)`, the affiliated-operator ring of the finite von Neumann algebra `M = L^∞(X) ⋊ G`, and
     `u_g π(a) u_g^* = π(σ_g a)`. So `K_0 ⋊ G -> U(M)` is a unital ring homomorphism.
   - `M_n(U(M)) = U(M_n(M))` is directly finite, so `U(M)` is stably finite and has the rank condition. An
     epimorphism `R^r -> R^d` with `r < d` would split and give a one-sided inverse in `M_r(R)`.
4. **Examples.**
   - Bernoulli fields: iid uniform values. Nonzero polynomials vanish only on null sets.
   - Monomial actions: Haar measure on `T^n`.
5. **Möbius non-example.**
   - Every `PSL_2(Z)` orbit on `P^1(C)` is infinite, because point stabilizers in `PSL_2(C)` are solvable. So
     the fixed field of `Q(x)` is `Q`.
   - An invariant probability measure for `[[2,1],[1,1]]` sits on its algebraic fixed points `(1±√5)/2`, which
     are not embeddings of `Q(x)`.

Import: direct finiteness of the affiliated-operator algebra of a finite von Neumann algebra (Berberian, *The
regular ring of a finite AW\*-algebra*; P. Linnell, *Division rings and group von Neumann algebras*, Forum Math.
1993, Section 8), a standard fact.
