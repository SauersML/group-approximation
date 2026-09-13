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
  - full-defect-ring-non-mf-at-rank-two
  - invariant-measure-gives-rank-function-in-char-zero
artifacts:
  - research/artifacts/un-algebraic-tarski-2026-09-13.md
---

Full derivation in the artifact, Section 6 (unreviewed). `S` is almost unperforated if
`(m+1)x ≤ my` for some `m ≥ 1` implies `x ≤ y`.

**Exhaustive over every field; exclusive only in characteristic zero.** By
`algebraic-tarski-for-steinberg-algebras` step 3, if no invariant probability measure exists then
`(n+1)θ ≤ nθ` for some `n`, and Lemmas A–C below yield branch 2. The converse exclusion does NOT follow
from step 3: an invariant measure makes `θ` completely non-paradoxical in `S(𝒢)`, but `ι` is not known
to reflect paradox, so this does not by itself exclude the ring properties of branch 2. For `k ⊆ ℂ`,
`invariant-measure-gives-rank-function-in-char-zero` gives a faithful rank function, hence stable
finiteness (step 1), which contradicts "not directly finite"; so the branches are exclusive there. In
characteristic `p` exclusivity would need *invariant measure ⟹ stably finite*, which is open.

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

**No MF quotient, from rank two.** Taking `V = X` in Lemma C gives `2[1] ≤ [1]`, so `R ⊕ R` is
isomorphic to a direct summand of `R`: there are `s_1, s_2, t_1, t_2 ∈ R` with `t_i s_j = δ_ij 1`. With
`s = s_1`, `t = t_1` we get `ts = 1`, and `1 − st` is full because
`t_2 (1 − s_1 t_1) s_2 = t_2 s_2 − t_2 s_1 t_1 s_2 = 1`. In particular `st ≠ 1`, so `R` is not directly
finite. `R` is countable because `k` is countable and `𝒢` is second countable. So
`full-defect-ring-non-mf-at-rank-two` gives that every homomorphism from `EL_n(R)` to an MF group is
trivial for every `n ≥ 2`.

*Correction, 2026-09-13* (found by un-verify-3): the landing 991380d00d claimed exclusivity for every
field and cited only the rank-four node for a rank-two statement. Both are repaired above.
