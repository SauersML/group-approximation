---
rg: 2
id: type-i-k0-embedding-from-type-i-case
kind: route
title: Realise a singular subgroup as the boundary of a type I circle extension, which is stably finite and hence quasidiagonal by the type I case
target: type-i-qd-algebras-have-k0-embedding-property
requires:
  - bk-type-i-stably-finite-algebras-are-qd
  - brown-dadarlat-ext-trivial-class-gives-qd-extension
artifacts:
  - research/artifacts/bk-type-i-k0-embedding-equivalence-2026-09-16.md
---

Full proof: artifact §3, proofs of (a) ⇒ (c) and (c) ⇒ (b).  This is the easy
half of Brown--Dadarlat Proposition 4.6, with the extra observation that the
extension it builds is type I.

Let `A` be separable, QD and type I, and `G ⊆ K_0(A)` singular.

1. **UCT realisation (artifact (U1)).**  Verbatim from BD's proof of
   Proposition 4.6: "Since abelian C\*-algebras satisfy the UCT we can construct
   an extension `0 → K⊗A → E → ⊕_N C(T) → 0`, such that
   `∂(K_1(⊕_N C(T))) = ∂(⊕_N Z) = G`."  The same construction is recorded for
   Moutzouris' Proposition 3.2 in `moutzouris-k0-killing-is-local`.
2. **Type I.**  `E` is separable and type I, being an extension of a commutative
   algebra by the type I algebra `K⊗A` (standard; numbering not re-checked).
3. **Stably finite.**  `K⊗A` is QD, hence stably finite.  `⊕_N C(T)` is
   commutative, hence stably finite.  The subgroup `G` stays singular in
   `K_0(K⊗A)`.  By Spielberg's criterion (BD Proposition 4.1, in
   `brown-dadarlat-ext-trivial-class-gives-qd-extension`), `E` is stably finite.
4. **Quasidiagonal.**  By `bk-type-i-stably-finite-algebras-are-qd`, `E` is QD.
5. **The embedding.**  `ρ : A → E`, `a ↦ e_11 ⊗ a ∈ K⊗A ⊆ E`, is injective.
   Exactness of `K_1(⊕_N C(T)) → K_0(K⊗A) → K_0(E)` gives `ρ_*(G) = 0`.
