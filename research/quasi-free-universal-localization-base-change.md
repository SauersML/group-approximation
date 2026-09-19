---
rg: 2
id: quasi-free-universal-localization-base-change
kind: route
title: Base-change the bimodule resolution of A along A -> B, using the Bergman--Dicks facts B ⊗_A B = B and Tor_1^A(B, B) = 0
target: universal-localizations-of-quasi-free-algebras-are-quasi-free
requires: []
---

**Import.** A. Neeman, A. Ranicki, *Noncommutative localisation in algebraic K-theory I*, Geom. Topol. 8 (2004),
pp. 1385 ff., arXiv:math/0410620v1. Read on 2026-09-19 from the arXiv PDF. Setting (Section 0): "σ = {s_i : P_i → Q_i |
where P_i, Q_i are f.g. projective}", and Definition 0.2: "The initial object in the category of σ–inverting
homomorphisms is called the Cohn localisation or the universal localisation of A with respect to σ." Then, Section 8 (page
1421 of the journal pagination):

> **Lemma 8.6** We have:
> (i) The multiplication map µ : {σ^{-1}A} ⊗_A {σ^{-1}A} → {σ^{-1}A} is an isomorphism.
> (ii) Tor^A_1(σ^{-1}A, σ^{-1}A) = 0.
>
> Proof The results of Lemma 8.6 are not new. They first appeared in an article by Bergman and Dicks [3]. [...]
> The vanishing of Tor^A_1(σ^{-1}A, σ^{-1}A) is in [3, (95) on page 326].

Here [3] is G. M. Bergman, W. Dicks, *Universal derivations and universal ring constructions*, Pacific J. Math. 79
(1978) 293--337. No hypothesis on `A` or `σ` is made.

**Proof.** Write `B = σ^(-1) A`, and `⊗` for `⊗_k`.

1. Let `Ω = ker(m : A ⊗ A -> A)`. Since `pd_(A^e) A <= 1` and `A ⊗ A = A^e` is free, Schanuel gives that `Ω` is a
   projective `A^e`-module.
2. The sequence `0 -> Ω -> A ⊗ A -> A -> 0` splits as right `A`-modules, by `a ↦ 1 ⊗ a`. So `B ⊗_A -` keeps it
   exact: `0 -> B ⊗_A Ω -> B ⊗ A -> B -> 0`.
3. Apply `- ⊗_A B`. Since `B ⊗ A` is a free right `A`-module, `Tor_1^A(B ⊗ A, B) = 0`, and the long exact
   sequence reads
   `Tor_1^A(B, B) -> B ⊗_A Ω ⊗_A B -> B ⊗ B -> B ⊗_A B -> 0`.
4. By Lemma 8.6(ii) the left term is `0`. By Lemma 8.6(i) the last map is the multiplication `B ⊗ B -> B`. So
   `B ⊗_A Ω ⊗_A B ≅ Ω_B := ker(m_B : B ⊗ B -> B)`.
5. `B ⊗_A Ω ⊗_A B = B^e ⊗_(A^e) Ω`, and base change takes projective `A^e`-modules to projective `B^e`-modules.
   So `Ω_B` is projective, and `0 -> Ω_B -> B^e -> B -> 0` shows `pd_(B^e) B <= 1`. ∎
