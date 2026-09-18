---
rg: 2
id: once-punctured-mcg-continuous-asynchronous-proof
kind: route
title: Restrict Mosher's suffix-unique groupoid normal forms to closed paths, rename edges as group elements, invert, and apply the suffix-continuity lemma
target: once-punctured-mcgs-are-continuous-asynchronous-automatic
requires:
  - mosher-suffix-uniqueness-gives-continuous-inverse-normal-forms
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

Notation as in the target.
- `X` is Mosher's finite 2-complex, `D_B` its base vertex, and `𝒜_0` its set of edges
  (labelled elementary moves and relabelling moves).
- `𝓛_0 ⊆ 𝒜_0^*` is his normal form language for edge paths from `D_B`.
- `G = π_1(X, D_B) = Mod(S)`.

**Step 1 (group normal forms over edges).**
- `𝓛_B = {v ∈ 𝓛_0 : v ends at D_B}` is regular: intersect with the finite-state
  condition "the path ends at `D_B`".
- It contains exactly one word for each element of `G`, since `𝓛_0` has unique normal
  forms.
- Fix a finite symmetric generating set of `G` given by closed edge paths
  `γ = γ_1 ⋯ γ_r`.
- For `v ∈ 𝓛_B`, the normal form of `v̄ γ` is obtained by applying the groupoid steps
  `· γ_1, …, · γ_r` in turn.

**Step 2 (suffix-continuity for group generators).**
- By (S) and item 1 of `mosher-suffix-uniqueness-gives-continuous-inverse-normal-forms`,
  each groupoid step is suffix-continuous with `M = 3(N+1)`.
- Composing `r` steps, for every `N` there is `M` such that normal forms in `𝓛_B` with
  the same last `M` letters have images under `· γ` with the same last `N` letters.
- By item 2 of the lemma, `v ↦ v·γ` is computed by a composite backward process. Its
  state is a tuple of carries in `B_1` together with buffers of bounded length.

**Step 3 (renaming edges as group elements).**
- Choose for each vertex `D` of `X` an edge path `t_D` from `D_B` to `D`, with
  `t_{D_B}` empty. For an edge `e : D → D'` put `ρ(e) = [t_D e t_{D'}^{-1}] ∈ G`.
- For a closed path `e_1 ⋯ e_m` at `D_B`, the product `ρ(e_1) ⋯ ρ(e_m)` telescopes to
  `[e_1 ⋯ e_m]`.
- As in BBCMP, proof of Theorem 2.12, the `t_D` can be chosen so that `ρ` is injective
  on `𝒜_0`. This uses that `G` is infinite. Then `ρ_*` is a letter-to-letter injection.
- So `ρ_*(𝓛_B)` is a regular language of normal forms for `G` over the finite alphabet
  `ρ(𝒜_0)`. It has the same common-suffix lengths, so Step 2 holds for it verbatim.
- Add the inverses of the letters to the alphabet so that it is symmetric. The language
  does not change.
- Take the finite generating set of Step 1 to be exactly these letters `ρ(e)^{±1}`.
  Each is represented by the closed edge path `t_D e t_{D'}^{-1}` or its inverse, so
  Step 2 applies to every letter.

**Step 4 (inversion).** Apply item 3 of the lemma to `ρ_*(𝓛_B)`, with Step 2 in place of
item 1, as the only input used there.
- `𝓛^{inv} = inv(ρ_*(𝓛_B))` is a continuous normal form for the left action of `G`.
- Its left multiplier relations are deterministic rational, via the reversed composite
  backward process of Step 2.
- So `G` is continuous asynchronous automatic. This is item 1.

**Step 5 (the rational group).** BBCMP Corollary 1.9, as printed: every continuous
asynchronous automatic group embeds in the rational group of
Grigorchuk--Nekrashevych--Sushchanskii. This is item 2. □
