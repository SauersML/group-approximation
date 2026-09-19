---
rg: 2
id: pointed-pre-injective-cover-pairs-admit-sections
kind: claim
title: A cover pair that is injective on the asymptotic class of one constant has a section, so over a surjunctive group every constant-point cover pair is non-pre-injective at every constant and CP is equivalent to its pre-injective fragment
distinct_from:
  proper-sft-domains-admit-no-dual-failures: that asks that strongly post-surjective maps on strongly irreducible proper SFTs be pre-injective; this shows that pre-injectivity at one constant already forces non-surjunctivity, so on constant-point strongly irreducible domains that claim and CP coincide.
  cover-pair-sections-force-fixed-point-surjectivity: that shows sections force fixed-point surjectivity, a necessary condition; this gives a sufficient condition for a section, read off one asymptotic class.
  cover-pair-sections-localize-to-the-symmetric-locus: that reduces a section to a seed exact on Sym_E; this builds the section outright, with no seed and no colouring, from uniqueness of pointed lifts.
  post-surjective-decoders-convert-strict-pairs-to-dual-failures: that is about decoders on the full shift; this is about cover pairs on proper subshift domains, where injectivity on one asymptotic class is the only input.
  constant-point-sft-domains-admit-no-post-surjective-covers: that is the target statement; this proves it for the pointed-pre-injective class and shows any counterexample must be non-pre-injective at every constant.
artifacts:
  - research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md
  - research/artifacts/pointed-pre-injective-sections-2026-09-18.md
---

**ESTABLISHED (unreviewed)** by [[pointed-pre-injective-cover-pairs-admit-sections-proof]]. Elementary.

**Setting.** `A` is a finite alphabet, `G` a group, action `(g.x)(h) = x(g^-1 h)`. `X ⊆ A^G` is a closed
`G`-invariant subshift (an SFT in the cover-pair case), and `F : X → A^G` is an automaton that is strongly
post-surjective with lifts in `X` with constant `Φ`: for `x ∈ X` and `z ~ F(x)` there is `x' ∈ X` with
`x' ~ x`, `F(x') = z` and `Δ(x, x') ⊆ Δ(F(x), z) Φ`. A *section* is a continuous equivariant
`s : A^G → X` with `F ∘ s = id`. For `p ∈ A^G` write `Fin_p(X) = {x ∈ X : x ~ p}`.

**Theorem P.** Let `c^G ∈ X` be a constant and put `d^G = F(c^G)`. If `F` is injective on `Fin_c(X)`, then
`(X, F)` has a section `s`, and `s` is a cellular automaton with memory `Φ^-1`. If moreover `X ≠ A^G`, then
`G` is not surjunctive.

**Theorem P' (periodic points).** Let `H ≤ G` have finite index and let `p ∈ X` be fixed by `H`. If `F` is
injective on `Fin_p(X)`, then there is a continuous `H`-equivariant `s : A^G → X` with `F ∘ s = id`. If moreover
`X ≠ A^G`, then `G` is not surjunctive.

**Theorem Q (sections are pointed prunings).** A cover pair `(X, F)` has a section iff there are a closed
invariant `X' ⊆ X` and a constant `c^G ∈ X'` such that `F|_(X')` is strongly post-surjective with lifts in `X'`
and injective on `Fin_c(X')`.
- ⇐ is Theorem P for `X'`.
- ⇒ takes `X' = s(A^G)`, with lift constant `M_s^-1`. The proof is in the artifact, Section 3.

**Corollaries.**
1. **(Surjunctive groups.)** Over a surjunctive `G`, every cover pair is non-injective on `Fin_p(X)` for every
   finite-orbit point `p ∈ X`. Hence it is not pre-injective. In particular every counterexample to
   `constant-point-sft-domains-admit-no-post-surjective-covers` at a surjunctive group has, at every constant
   `c^G ∈ X`, two distinct finite perturbations of `c^G` inside `X` with the same image.
2. **(CP equals its pre-injective fragment.)** Say `G` satisfies PSD_c if every constant-point cover pair over
   `G` is pre-injective, and PSD_c^SI if every strongly irreducible one is. Then

   ```text
   CP(G)  ⟺  PSD_c(G),        CP^SI(G)  ⟺  PSD_c^SI(G),
   ```

   where CP^SI restricts CP to strongly irreducible domains. So on constant-point strongly irreducible domains
   the route `gottschalk-via-proper-domain-duality` (through `proper-sft-domains-admit-no-dual-failures`) and the
   route `gottschalk-via-constant-point-domains` ask the same question.
3. **(Gottschalk as a pointed-injectivity statement.)** `G` is non-surjunctive iff there is a proper subshift
   `X ⊊ A^G` (not necessarily of finite type), a constant `c^G ∈ X` and a strongly post-surjective `F : X → A^G`
   with lifts in `X` that is injective on `Fin_c(X)`. The forward direction takes `X = τ(A^G)` and `F = τ^-1`
   for an injective non-surjective automaton `τ`.
4. **(Needs 36774ad3 and 06d50d0e.)** The de-colouring question has a positive answer on every constant-point
   pair that is injective on the class of some constant. Any negative instance, and any construction that must
   solve the `⟨e⟩`-coset lift, lives on pairs where finite perturbations of every constant collide.

**What this does not do.** It does not decide CP at any nonsofic group. It does not settle whether a surjunctive
group can carry a constant-point cover pair; by Corollary 1 such a pair must be non-pre-injective at all its
finite-orbit points. Corollary 3 needs a non-SFT domain; whether a sofic image can always be replaced by an SFT
domain with the same pointed injectivity is open.
