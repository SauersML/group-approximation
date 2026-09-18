---
rg: 2
id: cantor-invariant-vectors-are-rigid-for-cantor-integer-maps-proof
kind: route
title: "Disjoint clopen sequences are exchangeable under a V-invariant law; merging two terms keeps the tail, so the de Finetti directing measure is idempotent, hence Haar(H); nontrivial H has mean 0 and trivial H forces χ = 0"
target: cantor-invariant-vectors-are-rigid-for-cantor-integer-maps
requires: []
---

Notation is as in the target. `Q` is the set of proper nonempty clopen subsets of `C`. For
`χ ∈ Â` and a clopen `U` write `χ(U) = χ(1_U) ∈ T`; then `χ(U ⊔ W) = χ(U)χ(W)`. External facts
used: de Finetti's theorem for exchangeable sequences in a compact metric space; the
Kawada–Itô theorem (an idempotent Borel probability on a compact group is Haar measure of a closed
subgroup); Bochner's theorem and Schoenberg's theorem.

## Step 1. Transitivity on ordered partitions

**Lemma 1.** For every `m ≥ 1`, `V` acts transitively on ordered partitions `(P_1, ..., P_m)` of
`C` into nonempty clopen sets.

*Proof.* Each `P_i` is a finite disjoint union of cones. Splitting a cone `[w]` into `[w0] ⊔ [w1]`
raises the count by one, so we may write `P_i` and `Q_i` as unions of the same number `a_i` of
cones. The map sending the `j`-th cone `[u]` of `P_i` to the `j`-th cone `[u']` of `Q_i` by
`uy ↦ u'y` is an element of `V` carrying `P_i` onto `Q_i` for every `i`. ∎

Call a sequence `S = (U_1, U_2, ...)` in `Q` *admissible* if its terms are pairwise disjoint and no
finite union of them is `C`. For admissible `S` put `X^S_i(χ) = χ(U_i)`.

**Lemma 2.** Let `μ` be `V`-invariant. For any two admissible sequences `S`, `S'`, the processes
`(X^S_i)_i` and `(X^{S'}_i)_i` have the same law under `μ`. In particular each is exchangeable.

*Proof.* For each `k`, `(U_1, ..., U_k, C ∖ ⋃_{i≤k} U_i)` is an ordered partition into `k + 1`
nonempty clopen sets, and likewise for `S'`. By Lemma 1 some `v ∈ V` maps the first onto the second,
so `(χ(U'_1), ..., χ(U'_k)) = ((v^{-1}·χ)(U_1), ..., (v^{-1}·χ)(U_k))` for the dual action. By
invariance these vectors have the same law. Finite-dimensional laws determine the law of the process.
A permutation of an admissible sequence is admissible, which gives exchangeability. ∎

## Step 2. The directing measure is idempotent

Fix an admissible `S`. By de Finetti, there is a random probability measure `ρ_S` on `T`,
measurable with respect to the tail σ-field of `(X^S_i)`, such that the `X^S_i` are conditionally
i.i.d. with law `ρ_S` given `ρ_S`. Concretely `ρ_S = lim_n (1/n) Σ_{i≤n} δ_{X^S_i}` weakly, `μ`-a.s.,
and the same limit is obtained along any fixed infinite subsequence of indices.

**Lemma 3.** `ρ_S * ρ_S = ρ_S` a.s. Hence `ρ_S = Haar(H_S)` for a closed subgroup `H_S ≤ T`.

*Proof.* `S^+ = (U_1 ⊔ U_2, U_3, U_4, ...)` is admissible, and its tail coincides with that of `S`,
so `ρ_{S^+} = ρ_S` pointwise. By Lemma 2 the pairs `(X^{S^+}_1, ρ_{S^+})` and `(X^S_1, ρ_S)` have the same
law, because `ρ` is the same Borel function of the respective processes. The first is
`(X^S_1 X^S_2, ρ_S)`. Conditionally on `ρ_S`, `X^S_1 X^S_2` has law `ρ_S * ρ_S` and `X^S_1` has law
`ρ_S`. Equality of joint laws gives equality of regular conditional laws a.s. Kawada–Itô finishes. ∎

## Step 3. One subgroup for all clopen sets

**Lemma 4.** If `S`, `S'` are admissible and the union of their terms (after deleting finitely many
from each) is again pairwise disjoint with no finite union equal to `C`, then `ρ_S = ρ_{S'}` a.s.

*Proof.* Interleave the tails into one admissible sequence `S''`. Both tails are infinite
subsequences of `S''`, so both empirical limits equal `ρ_{S''}` a.s. ∎

Fix the reference sequence `R = ([110^k1])_{k≥0}`, inside `[11]`, and let `H(χ) = H_R(χ)`.
For `U ∈ Q`, pick a word `w` with `|w| ≥ 2` and `[w] ⊆ C ∖ U`. This is possible because `C ∖ U` is a
nonempty clopen set, so it contains cones of every large depth. Put
`S(U) = (U, [w1], [w01], [w001], ...)`. It is admissible: the later terms lie in `[w]`, and no finite
union contains `w0^∞`.

**Lemma 5.** `ρ_{S(U)} = ρ_R` a.s., for every `U ∈ Q`.

*Proof.* The tail of `S(U)` lies in `[w]` and accumulates only at `w0^∞`. The tail of `R` lies in `[11]`
and accumulates only at `110^∞`. Choose a cone `[u]` disjoint from `[w]` and from `[11]`. It exists
because `[w] ∪ [11]` has Bernoulli measure at most `1/2`, as `|w| ≥ 2`. Let `E = ([u0^k1])_k`. The
terms of `E` together with the tail of `S(U)` are pairwise disjoint, and no finite union of them
contains `u0^∞`, so none is `C`. The same holds for `E` and `R`. By Lemma 4,
`ρ_{S(U)} = ρ_E = ρ_R`. ∎

## Step 4. Proof of the theorem and corollaries

Put `H(χ) = H_R(χ)`, a Borel function of `χ` by Lemma 3.

*Item 2.* For admissible `S`, apply Lemma 4 with an auxiliary sequence `E` as in Lemma 5. This gives
`ρ_S = ρ_R` a.s., and de Finetti then gives item 2.

*Item 1.* By Lemma 5 and item 2 applied to `S(U)`, `χ(U) = X^{S(U)}_1` has conditional law
`Haar(H(χ))` given `H(χ)`. So `χ(U) ∈ H(χ)` a.s. `Q` is countable, so a.s. this holds for all
`U ∈ Q` at once.

*Item 3.* The mean of `Haar(H)` is `1` if `H = {1}` and `0` otherwise, because a nontrivial closed
subgroup of `T` is `μ_k` (`k ≥ 2`) or `T`. Hence `Φ(1_U) = E[E[χ(U) | H]] = μ{H = {1}}`.
- If `H(χ) = {1}`, item 1 gives `χ(U) = 1` for all `U ∈ Q`. Since `1_C = 1_{[0]} + 1_{[1]}` and the
  `1_U` (`U ∈ Q`) generate `A`, this forces `χ = 0`.
- Conversely, `χ = 0` gives `ρ_R = δ_1`.

So `{H = {1}} = {χ = 0}` a.s., and `μ{χ(1_C) ≠ 1} ≤ μ{χ ≠ 0} = 1 − Φ(1_U)`.

*Rigid invariant vectors.* If `ξ` is `V`-invariant, then `μ_ξ` is `V`-invariant, because
`⟨π(v·f)ξ, ξ⟩ = ⟨π(v)π(f)π(v)^{-1}ξ, ξ⟩ = ⟨π(f)ξ, ξ⟩`. The spectral projection of `π|_A` onto the
point `{0} ⊂ Â` is `P_A`, so `‖P_Aξ‖² = μ_ξ{0} = Φ_ξ(1_U)`. Therefore
`‖ξ − P_Aξ‖² = 1 − Φ_ξ(1_U) = ‖π(1_U)ξ − ξ‖²/2`, the last equality because `Φ_ξ(1_U)` is real.
The `π(z)`-invariant vectors contain the range of `P_A`.

*Invariant cnd functions.* Let `N` be `V`-invariant cnd on `A`, and put `K = N(1_{[0]})`, which equals
`N(1_U)` for all `U ∈ Q` by Lemma 1. For `t > 0`, Schoenberg makes `e^{−tN}` positive definite and
`V`-invariant. Bochner gives a `V`-invariant probability `μ_t` on `Â`. Write `Z = χ(1_C)`. Then
`e^{−tN(n·1_C)} = ∫ Z^n dμ_t ≥ 1 − 2μ_t{Z ≠ 1} ≥ 1 − 2(1 − e^{−tK}) = 2e^{−tK} − 1`.
Hence `N(n·1_C) ≤ −t^{-1} log(2e^{−tK} − 1)` for all `n` and all small `t`. Letting `t → 0` gives
`sup_n N(n·1_C) ≤ 2K`.

For the cnd function on `G`: if `b` is the GNS cocycle of `N` on the Hilbert space `H_N`, then `V`
acts unitarily on `H_N` by `u_v b(f) = b(v·f)`, because `N` is `V`-invariant. Then `π(f,v) = π_A(f)u_v`
with `B(f,v) = b(f)` is an affine isometric action of `G`, and `ψ(f,v) = N(f)`. ∎

## Step 5. Why the exact argument cannot be made quantitative as it stands

The argument never distinguishes `z` from `A`. Its output is `‖ξ − P_Aξ‖² = ½‖π(1_U)ξ − ξ‖²`, which
is a relative-(T) inequality for the pair `(G, A)`, restricted to `V`-fixed vectors. Consider any
quantitative upgrade of the same form:

> (Q_A) for a fixed finite `F ⊂ V`, every unit `ξ` with `max_{v∈F} ‖π(v)ξ − ξ‖ ≤ ε` satisfies
> `‖ξ − P_Aξ‖ ≤ c‖π(1_{[0]})ξ − ξ‖ + ω(ε)`, where `ω(ε) → 0`.

This is false. `cantor-integer-maps-pair-lacks-relative-property-t` supplies unit vectors `ξ_k` with
`P_Aξ_k = 0`, `V`-defect `→ 0` and `‖π(1_{[0]})ξ_k − ξ_k‖ → 0`. Those two defects are the ones
controlled by the finite generating set `F ∪ {1_{[0]}}` of `G`.

So every attempt to prove central relative (T) by approximate exchangeability dies at the same step.
This covers finite de Finetti (Diaconis–Freedman), almost-idempotent measures and stability of
Kawada–Itô. The attempt dies wherever it would conclude that the approximate directing measure is
`δ_1`: that conclusion bounds `‖ξ − P_Aξ‖`, i.e. it proves (Q_A). A proof of
`cantor-integer-maps-central-direction-has-relative-t` along these lines must use an input that
separates `z = χ([0])χ([1])` from a general element of `A`, for example an estimate on the `π(z)`-spectral
measure alone. Here is what separates the two statements at the exact level.
- For `A`, the event `{H = {1}}` must be the whole `A`-fixed part.
- For `z`, the event `{χ(1_C) = 1}` also contains `{H = μ_k, χ(1_C) = 1}` and parts of `{H = T}`.
  So the central statement tolerates spectral mass on nontrivial `H` that the `A` statement does not.
