---
rg: 2
id: unperforated-paradox-makes-steinberg-purely-infinite-proof
kind: route
title: Proof that almost unperforation pushes the paradox down to the unit, giving proper pure infiniteness by Larki and the MF-quotient threshold two
target: unperforated-paradox-makes-steinberg-purely-infinite
requires:
  - algebraic-tarski-for-steinberg-algebras
  - purely-infinite-steinberg-algebras-characterized
  - steinberg-algebra-simple-iff-minimal-effective
  - simple-dedekind-infinite-ring-elementary-full-mf-radical
artifacts:
  - research/artifacts/un-algebraic-tarski-2026-09-13.md
---

Full derivation in the artifact, Section 6 (unreviewed). `S` is almost unperforated if
`(m+1)x ≤ my` for some `m ≥ 1` implies `x ≤ y`.

**Exclusive and exhaustive.** By `algebraic-tarski-for-steinberg-algebras` step 3, an invariant
probability measure exists iff `θ` is completely non-paradoxical. So branch 2 is the case where
`(n+1)θ ≤ nθ` for some `n`.

**Lemma A.** If `(n+1)θ ≤ nθ` then `Nθ ≤ nθ` for every `N ≥ n`. Adding `θ` gives
`(n+2)θ ≤ (n+1)θ ≤ nθ`, and induction gives `(n+m)θ ≤ nθ`.

**Lemma B (the paradox descends to the unit).** With `S(𝒢)` almost unperforated, Lemma A at
`N = 2n+2` gives `(2n+2)θ ≤ nθ`, that is `(n+1)(2θ) ≤ n·θ`. Almost unperforation with `x = 2θ`,
`y = θ`, `m = n` gives `2θ ≤ θ`.

**Lemma C (every nonempty compact open is properly infinite).** From `2θ ≤ θ` induction gives
`jθ ≤ θ` for all `j ≥ 1`. Let `∅ ≠ V` be compact open. Minimality gives `θ ≤ m[V]` for some `m`, and
`[V] ≤ θ`. Then `(m+1)(2[V]) = (2m+2)[V] ≤ (2m+2)θ ≤ θ ≤ m[V]`, so almost unperforation with
`x = 2[V]`, `y = [V]` gives `2[V] ≤ [V]`.

**Transfer to the algebra.** Applying the bridge `ι : S(𝒢) → V(R)`, `[U] ↦ [1_U R]` (see
`algebraic-tarski-for-steinberg-algebras-proof`), every `1_V` is a properly infinite idempotent of
`R`.

**Proper pure infiniteness.** Minimality makes `𝒢` strongly effective: the only closed invariant
subsets of `X` are `∅` and `X`, and `𝒢` is effective. So
`purely-infinite-steinberg-algebras-characterized` (Larki Thm 3.4), implication (2) ⟹ (1), applies
with `𝓑` the compact open sets, and `R` is properly purely infinite. Simplicity of `R` is
`steinberg-algebra-simple-iff-minimal-effective`.

**No MF quotient.** Taking `V = X` in Lemma C, `2[1] ≤ [1]`, so there are `s, t ∈ R` with `ts = 1`
and `st ≠ 1`, i.e. `R` is not directly finite; `R` is countable because `k` is countable and `𝒢` is
second countable. Then `simple-dedekind-infinite-ring-elementary-full-mf-radical` applies, giving
triviality of every homomorphism `EL_n(R) → ` MF group from rank four, and from rank two on the
printed statement of the source corollary (tex l.1016).
