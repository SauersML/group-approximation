---
rg: 2
id: leavitt-tensor-powers-have-trivial-k-theory
kind: claim
title: Every tensor power of the binary Leavitt algebra has K_1 = K_2 = 0
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that imports vanishing for L ⊗ R with R regular supercoherent, which covers L and L ⊗ L; this asks for L^(⊗d) with d >= 3, where the coefficient algebra L^(⊗(d-1)) is not known to be regular supercoherent.
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

**OPEN.** For every `d >= 3`, with `L = L_(F_2)(1,2)`,
`K_1(L^(⊗d)) = K_2(L^(⊗d)) = 0`.

It is true for `d = 1, 2` (`ara-cortinas-leavitt-tensor-k-theory-vanishes`).
With `leavitt-tensor-hosts-acyclic-steinberg-and-fp`, it would make every
`(L^(⊗d))^x` finitely presented and simple. It would then settle
`char-two-linear-groups-satisfy-boone-higman`.

## Attempts

1. **Homotopy `K`-theory.** Ara--Brustenga--Cortiñas arXiv:0903.0056 Theorem
   8.6 holds for every coefficient ring, and gives `KH(A ⊗ L) = 0` for every
   `A`. So `KH(L^(⊗d)) = 0`.
   - What remains is `K = KH` in degrees `1, 2`, that is, `K_2`-regularity of
     `L^(⊗d)` (ABC Section 8, Vorst).
   - Not proved: no regularity statement for tensor products of Leavitt
     algebras was found.
2. **Regular supercoherence of `L^(⊗(d-1))`.** Ara--Cortiñas Proposition 6.2
   would finish. Their Lemma 6.1 has two ingredients.
   - Flatness of the universal localization `P(E) -> L(E)` transfers to
     `P(E) ⊗ S -> L(E) ⊗ S` by base change.
   - Regular coherence of `P(E)[t_1, ..., t_n]` transfers only once the free
     algebras `S[t_1, ..., t_n]<e,f>` are regular coherent, for
     `S = L^(⊗(d-2))`.
   *Dies at* that lemma: free algebras over a noncommutative regular coherent
   ring. It may be in Gersten, *K-theory of free rings* (Comm. Algebra 1974),
   or Waldhausen (Ann. of Math. 1978); neither was read.
3. **Direct swindle.** `φ(r) = e r e* + f r f*` induces multiplication by `2`
   on `K_*`, and fixes `B ⊗ 1`.
   *Dies*: this proves vanishing only on the image of `K_*(B)`, and
   surjectivity of that map is the fundamental-sequence statement that needs
   regularity.
4. **The exact obstruction is a twisted Nil group.** ABC Theorem 5.10 holds for
   every H-unital coefficient ring `A`, with no regularity. For the quiver with
   one vertex and two loops the homotopy cofibre term is zero, so
   `K(L ⊗ A) ≃ NK(L_0 ⊗ A; φ^-1)_+ ⊕ NK(L_0 ⊗ A; φ)_-`. Here `L_0` is the
   degree-zero ultramatricial part and `φ(x) = e x e*` is the corner
   isomorphism.
   - So the claim at `d` is exactly vanishing of these twisted Nil groups, in
     degrees `1, 2`, for `A = L^(⊗(d-1))`.
   - What is proved: `L ⊗ L` is `K`-regular. `(L ⊗ L)[t_1, ..., t_p]` is
     `L ⊗ L[t_1, ..., t_p]`, and `L[t_1, ..., t_p]` is regular supercoherent by
     Ara--Cortiñas Lemma 6.1, since its polynomial extensions are polynomial
     extensions of `L`. So Ara--Cortiñas Proposition 6.2 gives
     `K((L ⊗ L)[t_1, ..., t_p]) = 0 = K(L ⊗ L)`.
   - *Stops*: `K`-regularity of `A` controls untwisted Nil groups only. The
     twisted groups for the stage-shift corner map `φ` were not reduced to
     untwisted ones.
