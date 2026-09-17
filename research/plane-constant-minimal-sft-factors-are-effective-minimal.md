---
rg: 2
id: plane-constant-minimal-sft-factors-are-effective-minimal
kind: claim
title: A plane-invariant equivariant factor of a minimal SFT over Λ_0 x Z^2 is an effectively closed minimal Λ_0-subshift with decidable language
distinct_from:
  effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts: that is the open converse, realizing an effective minimal subshift as such a factor; this is the elementary direction, that every such factor is effective and minimal.
  full-group-word-problem-iff-recursive-language: that relates the word problem of a derived full group to the language of a minimal Z-subshift; this shows that plane-invariant factors of minimal SFTs over products have decidable language, and says nothing about full groups.
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is the open existence statement (M2); this shows (M2) for Λ_0 is forced by any minimal SFT over Λ_0 x Z^2 whose Λ_0-freeness is witnessed by a plane-invariant free factor.
---

**ESTABLISHED (unreviewed).** Proof:
`plane-constant-minimal-sft-factors-are-effective-minimal-proof`.

**Setting.**
- `Λ_0` is a finitely generated group with solvable word problem.
- `Λ = Λ_0 x Z^2`, acting on `A^Λ` by `(g·x)(h) = x(hg)`.
- `X ⊆ A^Λ` is a nonempty subshift of finite type on which `Λ` acts minimally.
- `Φ : X -> B^{Λ_0}` is continuous, with `Φ((λ,0)·x) = λ·Φ(x)` and
  `Φ((1,z)·x) = Φ(x)` for all `λ ∈ Λ_0`, `z ∈ Z^2`, `x ∈ X`.

**Theorem.** `Y = Φ(X)` is a nonempty minimal `Λ_0`-subshift. It is effectively
closed, and its language is decidable.

**Corollary (the design class forces (M2)).** Suppose in addition that `Λ_0` is
infinite and finitely presented, and that `Λ_0` acts freely on `Y`. Then `Y`
witnesses `decidable-fp-groups-have-effective-minimal-free-subshifts` for
`Λ_0`.
- So a proof of (P1) through a minimal SFT over `Λ_0 x Z^2` whose
  `Λ_0`-freeness comes from a plane-invariant free factor contains a proof of
  (M2) for `Λ_0`.
- This covers Attempt 2 of `decidable-groups-embed-in-fp-groups-with-minimal-free-sft`
  (trivial factor, dies at freeness) and the Barbieri--Sablik-type
  simulation designs.
- No SFT trick at the product level avoids constructing an effective minimal
  free `Λ_0`-subshift first.

**Scope.** The theorem does not say that every minimal free SFT over
`Λ_0 x Z^2` has a free plane-invariant factor. A design whose `Λ_0`-freeness
varies along the `Z^2` coordinate is outside the corollary.
