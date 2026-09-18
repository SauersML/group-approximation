---
rg: 2
id: cantor-integer-witnesses-avoid-measure-characters-proof
kind: route
title: Ultrafilter limits of almost-invariant measures are invariant Borel means, an equivariant probability section turns them into an invariant clopen probability that halving forbids, and Haar survives
target: cantor-integer-relative-t-witnesses-avoid-measure-characters
requires:
  - thompson-v-amenable-actions-are-free-off-fixed-points
  - thompson-v-character-simplex
---

Notation as in the claim.

**Step 0: the limit mean.** Fix a Borel set `B`. To show `μ_k(B) → 0` it suffices to show `lim_ω μ_k(B) = 0`
for every nonprincipal ultrafilter `ω` on `N`. Fix `ω` and put `m(B) = lim_ω μ_k(B)` on Borel sets of
`Â ∖ {0}`.
- `m` is a finitely additive probability.
- It is `V`-invariant, because `|μ_k(gB) − μ_k(B)| ≤ ‖(g^-1)_*μ_k − μ_k‖_TV → 0`.
- Likewise `∫ φ∘g^-1 dμ_k − ∫ φ dμ_k → 0` for bounded Borel `φ` with `|φ| ≤ 1`.

**Halving (H)** is imported from `thompson-v-amenable-actions-free-off-fixed-points-proof`: there is no
`V`-invariant finitely additive probability on clopen subsets of `C`. The tables `{0,10,11} → {00,01,1}` and
`{0,10,11} → {01,00,1}` give `ℓ[0] = 2ℓ[0]`, and the swap of `[0]` and `[1]` gives `ℓ[1] = 0`.

**(Tr)** is also imported from there: `V` is transitive on proper nonempty clopen sets.

**Item 1 (section principle).** Suppose `t = m(E) > 0` and put `ℓ(W) = t^-1 lim_ω ∫_E λ_χ(W) dμ_k(χ)`.
- `ℓ` is a finitely additive probability on clopen sets, since `ℓ(C) = t^-1 m(E) = 1`.
- Invariance: `λ_(g^-1 χ)(W) = ((g^-1)_*λ_χ)(W) = λ_χ(gW)`. Substituting `χ' = g^-1 χ` and using that `E`
  is invariant, `∫_E λ_χ(gW) dμ_k(χ) = ∫_E λ_(χ')(W) d((g^-1)_*μ_k)(χ')`. This differs from
  `∫_E λ_χ(W) dμ_k` by at most `‖(g^-1)_*μ_k − μ_k‖_TV`.
- So `ℓ(gW) = ℓ(W)`, which contradicts (H). Hence `m(E) = 0`.

**Item 2 (measure characters).**
- *Integer-valued differences are integer atoms.* Suppose `χ_σ = χ_(σ')` and put `τ = σ − σ'`. Then `τ(W) ∈ Z`
  for all clopen `W`. Clopens form a generating algebra and `|τ|` is regular. So each Borel `B` is a limit
  of clopens `W_n` with `|τ|(B Δ W_n) → 0`, and `τ(B) ∈ Z`.
  - If the non-atomic part `τ_c` were nonzero, take a Hahn-positive set `P` for `τ_c` with `τ_c(P) > 0`, with
    the countably many atoms of `τ` removed.
  - By Sierpiński's theorem, `τ = τ_c` takes every value in `[0, τ_c(P)]` on Borel subsets of `P`. That is a
    contradiction.
  - So `τ = Σ n_i δ_(x_i)` with `n_i ∈ Z`.
- *Canonical form.* Write `σ = σ_c + Σ a_x δ_x` and put `σ̃ = σ_c + Σ rep(a_x) δ_x`, where `rep(a) ∈ [−1/2, 1/2)`
  and `rep(a) ≡ a mod 1`.
  - `σ̃` is finite, because `|rep(a)| = dist(a, Z) ≤ |a|`.
  - `χ_(σ̃) = χ_σ`.
  - By the previous bullet `σ̃` depends only on `χ`. Two canonical measures with the same character differ
    by integer atoms, and those must vanish since canonical weights lie in `[−1/2, 1/2)`.
  - `χ ≠ 0` iff `σ̃ ≠ 0`.
  - Equivariance: `(g·χ_σ)(f) = ∫ f∘g dσ = ∫ f d(g_*σ)`, so `g·χ_σ = χ_(g_*σ)` and the canonical form of
    `g_*σ` is `g_*σ̃`.
- *Borel structure.* Let `P ⊆ M_+(C)^2` (weak* topology, Polish) be the set of pairs `(σ+, σ−)` such that:
  - they are mutually singular. This says that for every `n` there is a clopen `W` with `σ+(C∖W) < 1/n` and
    `σ−(W) < 1/n`, which is Borel since `σ ↦ σ(W)` is continuous for clopen `W`. Borel–Cantelli on
    `limsup W_n` gives the converse;
  - every atom of `σ+` has mass `< 1/2` and every atom of `σ−` has mass `≤ 1/2`. The largest atom is
    `lim_k max_(|w| = k) σ[w]`, a decreasing limit of continuous functions;
  - `χ_(σ+ − σ−) ≠ 0`.

  The map `Φ(σ+, σ−) = χ_(σ+ − σ−)` from `P` to `Â` is continuous and, by canonical uniqueness, injective, with
  image `M`. By Lusin–Souslin, `M` is Borel and `Φ^-1` is Borel.
- *Section.* `λ_χ = (σ+ + σ−)/(σ+ + σ−)(C)`, where `(σ+, σ−) = Φ^-1(χ)`, is a Borel equivariant section of
  probabilities on `C`. Item 1 gives `μ_k(M) → 0`.
- *The listed examples.*
  - An atomic character `Σ t_i δ_(x_i)` with `Σ |rep t_i| < ∞` is `χ_σ` with `σ = Σ rep(t_i) δ_(x_i)`.
  - The high-frequency family is `χ_(2^F λ)`.

**Item 3 (supports).** Let `S_U = N_(C∖U)` be the set of nonzero characters whose support lies in the proper
nonempty clopen `U`.
- *Union lemma.* If `χ` vanishes on `C(W_1,Z)` and on `C(W_2,Z)`, then it vanishes on `C(W_1 ∪ W_2, Z)`,
  because `f = f·1_(W_1) + f·1_(W_2 ∖ W_1)`.
- *Equivariance.* `g·S_U = S_(gU)`. If `f` is supported off `gU`, then `f∘g` is supported off `U`.
- By (Tr), `c = m(S_U)` does not depend on `U`.
- `S_[00]` and `S_[01]` both lie in `S_[0]`. They are disjoint: a character in both vanishes on
  `C((C∖[00]) ∪ (C∖[01]), Z) = A` by the union lemma, so it is `0`.
- Hence `2c ≤ c`, so `c = 0`. Every nonempty clopen `U ≠ C` has `N_U = S_(C∖U)`, and `N_C` is empty.

**Item 4 (fixed sets).**
- *No global fixed point.* If `χ` is `V`-invariant, then by (Tr) `χ(1_W) = c` on proper nonempty clopen sets.
  From `[0] = [00] ⊔ [01]` we get `c = 2c = 0`, and `χ(1_C) = χ(1_[0]) + χ(1_[1]) = 0`. Cylinders span `A`,
  so `χ = 0`. Hence `Fix(V) ∩ (Â ∖ {0}) = ∅`.
- *Transcription of item 2 of `thompson-v-amenable-actions-are-free-off-fixed-points`.* Its proof evaluates the
  mean only on the sets `{χ : Stab(χ) ∈ 𝓔}` for clopen `𝓔 ⊆ Sub(V)`. These are finite Boolean combinations
  of the closed sets `Fix(g)`, so they are Borel in `Â`, and the proof runs verbatim for the Borel mean `m`.
  - `ν_0(𝓔) = m{χ : Stab(χ) ∈ 𝓔}` is a conjugation-invariant finitely additive probability on the clopen
    algebra of the compact zero-dimensional space `Sub(V)`. It is therefore countably additive there and extends
    to an IRS `ν`.
  - By `thompson-v-character-simplex` and the lazy random-walk step of that proof,
    `ν = (1−b)δ_({e}) + bδ_V` with `b = ν{V} = m(Fix V) = 0`.
  - So `m(Fix g) = ν{K ∋ g} = 0` for `g ≠ e`.
- For finite `P`, `{χ : Stab(χ) ∩ P ≠ ∅} = ⋃_(p ∈ P) Fix(p)`.

**Item 5 (countable orbits).** On each orbit, pick a representative `χ_0` and a stabilizer-invariant `λ_(χ_0)`,
and transport it by `λ_(gχ_0) = g_*λ_(χ_0)`. This is well defined because the stabilizer fixes `λ_(χ_0)`. On
a countable set every map is Borel, so item 1 applies. An amenable stabilizer fixes a Borel probability on `C`
by Markov–Kakutani.

**Item 6 (Haar survives).**
- Automorphisms of a compact group preserve Haar measure, so `m_Â` is `V`-invariant.
- `A` is free abelian with basis `{1_C} ∪ {1_[w0]}`, so `Â ≅ T^N` and `m_Â{0} = 0`.
- `N_U = ann C(U,Z)` and `Fix(g) = ann{g·f − f}` are closed subgroups. A closed subgroup has positive Haar
  measure iff it is open, iff its annihilated group is finite.
  - `C(U,Z)` is infinite.
  - For `g ≠ e`, pick a clopen `W` with `gW ≠ W`. Then `1_(gW) − 1_W` has infinite order.
  - So both subgroups are Haar-null.
- *`M` is Haar-null.*
  - For `χ = χ_σ ∈ M` and each `k`, `Σ_(|w| = k) |rep χ([w])| ≤ Σ_w |σ̃[w]| ≤ ‖σ̃‖`, because `rep χ([w])` is
    the distance from `σ̃[w]` to `Z`. So this sum is bounded in `k`.
  - The level-`k` cone indicators are a basis of `C_k(Z) ≅ Z^(2^k)`. Restricting characters pushes `m_Â` to
    Haar measure on `T^(2^k)`, so the values `χ([w])` are i.i.d. uniform.
  - The sum therefore has mean `2^k/4` and variance `2^k/48`. It tends to infinity in probability, so
    `m_Â{sup_k Σ ≤ R} = 0` for every `R`.
- The constant sequence is almost invariant with defect `0`, so no statement of the form "almost-invariant
  sequences are asymptotically null on `E`" can hold for a set `E` of positive Haar measure. Relative (T) can
  only be reached through the hypothesis `μ_k → δ_0`.

**Remark (not used).** Kuhn's theorem (Math. Nachr. 166, 1994) adds that Zimmer-amenable parts of the measure
class `Σ 2^-k μ_k` are asymptotically null. Almost invariant Hellinger vectors on such a part would make the
trivial representation weakly contained in `λ_V`.
