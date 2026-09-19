---
rg: 2
id: cantor-central-witnesses-have-active-cone-phases-proof
kind: route
title: "Expand the three-piece Möbius product over the partition C = [1] ⊔ [01] ⊔ [00], cancel the first and second order terms by transitivity of V on proper clopen sets, bound the product by Cauchy-Schwarz on two factors, and read the atoms off by Cesàro averaging in the frequency"
target: cantor-central-witnesses-have-active-cone-phases
requires:
  - cantor-cone-phase-atom-comparison-is-depth-uniform
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

Notation is that of the target. `T = R/Z` is written additively, `e(t) = exp(2πit)`,
`χ[U] = χ(1_U) ∈ T`, and `(h·χ)[U] = χ[h^{-1}U]` for `h ∈ V`. `μ` is the `A`-spectral law of the
unit vector `ξ` on the compact dual `Â`, so that

  `Φ(f) = ⟨π(f)ξ, ξ⟩ = ∫_Â e(χ(f)) dμ(χ)`  for `f ∈ A`,

and `Φ` is positive definite on `A` with `Φ(0) = 1`. Put `ε = max_{s∈S}‖π(s)ξ − ξ‖` for the
generating set `S = S_V ∪ {±1_{[0]}}` of artifact §3(c), and `u_M = Φ(M·1_{[0]})`.
`D(h) = sup_B |h_*μ(B) − μ(B)|` for Borel `B ⊆ Â`.

Two imports, both verbatim from `research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md`:

- §3(a): "`V` acts transitively on the proper nonempty clopen sets."
- §3(f), third bullet: "`‖μ_ξ − μ_η‖_TV ≤ ‖ξ − η‖(‖ξ‖ + ‖η‖)` by Cauchy–Schwarz on a Borel
  partition", together with "the spectral measure of `π(h)ξ` is `h_*μ_ξ`".

## 1. Transport

**Lemma 1.** For `h ∈ V`, `D(h) ≤ 2|h|_S ε`; and for every Borel `F : Â → C` with `|F| ≤ 1`,
`|∫F d(h_*μ) − ∫F dμ| ≤ 4|h|_S ε`.

*Proof.* Writing `h = s_1⋯s_n` with `n = |h|_S` and telescoping,
`‖π(h)ξ − ξ‖ ≤ Σ_i ‖π(s_i)ξ − ξ‖ ≤ nε`. The spectral measure of `π(h)ξ` is `h_*μ`, so the second
import gives `D(h) ≤ ‖π(h)ξ − ξ‖·2 ≤ 2nε`. The total variation *norm* of `h_*μ − μ` is
`2D(h)`, and `|∫F d(h_*μ − μ)| ≤ ∫|F| d|h_*μ − μ| ≤ 2D(h) ≤ 4nε`. ∎

**Lemma 2 (cone transport).** Let `U` be a proper nonempty clopen set and `h ∈ V` with
`h[0] = U`. Then for every `M ∈ Z`,

  `|Φ(M·1_U) − u_M| ≤ 4|h|_S ε`.

*Proof.* `χ[U] = χ[h[0]] = (h·χ)[0]`, so
`Φ(M·1_U) = ∫ e(M(h·χ)[0]) dμ(χ) = ∫ e(Mχ'[0]) d(h_*μ)(χ')`, and Lemma 1 applies to the
unimodular `F(χ') = e(Mχ'[0])`. ∎

**Lemma 3 (cheap deep cones).** There is a constant `c` (depending only on `S`) such that for
every finite word `w` there is `h_w ∈ V` mapping `[0]` canonically onto `[w]`, with
`|h_w|_S ≤ c(|w| + 1)`.

*Proof.* Let `k, k', b ∈ V` be fixed elements with `k[0] = [00]`, `k'[0] = [01]`, `b[0] = [1]`,
each acting canonically on `[0]` (`b` is the first-letter swap `0u ↦ 1u`, `1u ↦ 0u`; `k` is
`0u ↦ 00u`, `10u ↦ 01u`, `11u ↦ 1u`; `k'` is `0u ↦ 01u`, `10u ↦ 00u`, `11u ↦ 1u`). If `h` maps
`[0]` canonically onto `[v]`, i.e. `0u ↦ vu`, then `h∘k` maps `[0]` canonically onto `[v0]` and
`h∘k'` canonically onto `[v1]`, because `h(00u) = v0u` and `h(01u) = v1u`. Starting from
`h = id` (`v = 0`) this reaches every `[0w]` with `|h| ≤ max(|k|,|k'|)·|w|`, and composing with
`b` on the left (`b([0w]) = [1w]`, canonically) reaches every `[1w]`. Take
`c = max(|k|, |k'|, |b|)_S`. ∎

## 2. The three-piece Möbius identity

Fix the partition into three cones

  `U_1 = [1]`,  `U_2 = [01]`,  `U_3 = [00]`,  `U_1 ⊔ U_2 ⊔ U_3 = C`.

Its three pairwise unions are `U_1 ⊔ U_2 = C ∖ [00]`, `U_1 ⊔ U_3 = C ∖ [01]` and
`U_2 ⊔ U_3 = [0]`; all six sets are proper and nonempty. By §3(a) choose
`h_1, h_2, h_3, k_1, k_2, k_3 ∈ V` carrying `[0]` onto `U_1, U_2, U_3, U_2⊔U_3, U_1⊔U_3, U_1⊔U_2`
respectively, and set `L = max_i max(|h_i|_S, |k_i|_S)`. The constant of the target is `K = 40L`.

**Lemma 4.** For every `M ∈ Z`, with `ζ_i = e(M χ[U_i])`,

  `|E_μ[(1 − ζ_1)(1 − ζ_2)(1 − ζ_3)] − (1 − Φ(M·1_C))| ≤ 24Lε`.

*Proof.* Characters are finitely additive, so for disjoint clopen `U, W` one has
`χ[U] + χ[W] = χ[U ⊔ W]` and hence `E[∏_{i∈I}ζ_i] = Φ(M·1_{⊔_{i∈I}U_i})` for every
`I ⊆ {1,2,3}`. Expanding the product,

  `E[∏_i (1 − ζ_i)] = 1 − Σ_i Φ(M·1_{U_i}) + Σ_{i<j} Φ(M·1_{U_i ⊔ U_j}) − Φ(M·1_C)`.

By Lemma 2 each of the six displayed transforms is within `4Lε` of `u_M`, so the two middle sums
are each within `12Lε` of `3u_M` and cancel up to `24Lε`. ∎

**Lemma 5.** For every `M ∈ Z`,
`|E_μ[(1 − ζ_1)(1 − ζ_2)(1 − ζ_3)]| ≤ 4(1 − Re u_M) + 16Lε`.

*Proof.* `|1 − ζ_3| ≤ 2` pointwise, so the modulus is at most `2·E[|1−ζ_1||1−ζ_2|]`, and by
Cauchy–Schwarz this is at most `2(E|1−ζ_1|²)^{1/2}(E|1−ζ_2|²)^{1/2}`. Since `|ζ_i| = 1`,
`E|1 − ζ_i|² = 2 − 2Re E[ζ_i] = 2 − 2Re Φ(M·1_{U_i}) ≤ 2(1 − Re u_M) + 8Lε` by Lemma 2. Both
factors obey the same bound, so the product is at most `2(2(1 − Re u_M) + 8Lε)`. ∎

**Theorem.** `|1 − Φ(M·1_C)| ≤ 4(1 − Re Φ(M·1_{[0]})) + 40Lε` for every `M ∈ Z`.

*Proof.* Combine Lemmas 4 and 5. ∎

Nothing in the proof assumes anything about `μ` beyond its being the spectral law of a vector with
defect `ε`: no independence between cone phases, no moment condition, no equivariant extraction,
no exact invariance. In particular the estimate holds on scale-incoherent characters, where the
paradoxical push-forward of `extractable-character-spectra-carry-no-almost-invariant-vectors` has
nothing to act on.

## 3. Reading the atoms

**Lemma 6 (Wiener on `T`).** For a Borel probability `ρ` on `T` with `ρ̂(M) = ∫e(Mt)dρ(t)`,

  `lim_{M_0→∞} (1/M_0) Σ_{M=1}^{M_0} ρ̂(M) = ρ({0})`.

*Proof.* `(1/M_0)Σ_{M≤M_0} e(Mt) = 1` for `t = 0`, and for `t ≠ 0` it is
`e(t)(e(M_0t) − 1)/(M_0(e(t) − 1))`, of modulus at most `2/(M_0|e(t)−1|) → 0`. The averages are
bounded by `1`, so dominated convergence applies. ∎

**Corollary 1.** `μ{χ[C] = 0} ≥ 4·μ{χ[[0]] = 0} − 3 − 40Lε`, and for a proper nonempty clopen
`U` with `h[0] = U`, `μ{χ[C] = 0} ≥ 4·μ{χ[U] = 0} − 3 − 40Lε − 16|h|_S ε`.

*Proof.* `M ↦ Φ(M·1_C)` is the Fourier transform of the push-forward of `μ` under
`χ ↦ χ[C]`, and `M ↦ Φ(M·1_{[0]})` that of the push-forward under `χ ↦ χ[[0]]`. Since
`1 − Re Φ(M·1_C) ≤ |1 − Φ(M·1_C)|`, the Theorem gives

  `(1/M_0)Σ_{M≤M_0}(1 − Re Φ(M·1_C)) ≤ 4(1/M_0)Σ_{M≤M_0}(1 − Re Φ(M·1_{[0]})) + 40Lε`,

and Lemma 6 turns this into `1 − μ{χ[C] = 0} ≤ 4(1 − μ{χ[[0]] = 0}) + 40Lε`. For a general `U`,
Lemma 2 gives `1 − Re u_M ≤ 1 − Re Φ(M·1_U) + 4|h|_Sε`, whence
`1 − μ{χ[[0]] = 0} ≤ 1 − μ{χ[U] = 0} + 4|h|_S ε` after averaging. ∎

**Corollary 2 (class-kill).** If `π` has no nonzero `π(1_C)`-invariant vector, then
`μ{χ[C] = 0} = 0` and therefore, for every proper nonempty clopen `U` and `h ∈ V` with
`h[0] = U`,

  `μ{χ[U] ≠ 0} ≥ 1/4 − (10L + 4|h|_S)ε`.

*Proof.* The projection of `ξ` onto `ker(π(1_C) − 1)` has squared norm
`μ{χ : χ(1_C) = 1} = μ{χ[C] = 0}`, which is `0` by hypothesis; this is the first bullet of the
consequence list of `cantor-integer-maps-central-growth-criterion`. Now divide Corollary 1 by
`4`. ∎

With Lemma 3, `|h_w|_S ≤ c(|w|+1)`, so for every depth `d`,

  `E_μ #{w : |w| = d, χ[w] ≠ 0} ≥ 2^d (1/4 − (10L + 4c(d+1))ε)`,

which is `2^d(1/4 − o(1))` along any witnessing sequence as soon as `d = o(1/ε)`.

**Corollary 3 (near-positivity of the cone-phase transform).** Running §2 on the partition of the
*cone* `[0]` into the three cones `[00] ⊔ [010] ⊔ [011]` instead of the partition of `C` (the
pairwise unions are again proper nonempty clopen, and the total is `[0]`) gives
`|1 − u_M| ≤ 4(1 − Re u_M) + 40L'ε`, hence

  `|Im Φ(M·1_{[0]})| ≤ 4(1 − Re Φ(M·1_{[0]})) + 40L'ε`  for every `M ∈ Z`,

with `L'` the analogous word-length constant. So on every witness the cone-phase transform stays
in a fixed cone around the positive reals, with no `V`-ellipticity hypothesis.

## 4. Calibration

- **The known witness.** For the cone-product law of `cantor-integer-maps-pair-lacks-relative-property-t`,
  `χ_S = ∏_{w∈S}ξ_w` with `ξ(1_C) = 1`, one has `1_{[0]}∘ι_w = 1_{[0]}` for `w = ∅`, `= 1_C` for
  `w ∈ 0{0,1}^*`, and `= 0` for `w ∈ 1{0,1}^*`; so `χ_S[[0]] = 1{∅ ∈ S}·ξ[[0]]` and
  `μ{χ[[0]] = 0} = 1 − p → 1`, while `χ_S[C] = 1{∅∈S}·ξ[C] = 0` and `μ{χ[C] = 0} = 1`. Corollary 1
  reads `1 ≥ 4·1 − 3`, an equality: the constant `4` cannot be improved without further input, and
  the family is exactly on the boundary of the kill. This is the calibration the node
  demands, since that family *does* break relative (T) for the pair `(G, A)`.

  **(2026-09-18, referee — this bullet is wrong and is retained only as the record.)** The
  cone-product family sits at `(μ{χ[U]=0}, μ{χ[C]=0}) = (1,1)` in the limit `p_incl → 0`, and the
  line `p_C = c·p_U − (c−1)` passes through `(1,1)` for **every** constant `c`; for finite
  `p_incl` it reads `0 ≤ c·p_incl`, slack for every `c`. So the family is an equality for every
  `c` and certifies nothing about `c = 4`. Worse, `c = 4` is not optimal: by finite additivity
  `χ[C] = χ[[0]] + χ[[1]]`, so `{χ[[0]]=0} ∩ {χ[[1]]=0} ⊆ {χ[C]=0}` and inclusion–exclusion
  gives `μ{χ[C]=0} ≥ μ{χ[[0]]=0} + μ{χ[[1]]=0} − 1`; Lemma 2 applied to the single first-letter
  swap `b` gives `μ{χ[[1]]=0} ≥ μ{χ[[0]]=0} − 4|b|_S ε`, whence

    `μ{χ[C] = 0} ≥ 2·μ{χ[U] = 0} − 1 − O(ε)`,

  which dominates `4p − 3 − Kε` for every `p ≤ 1`. That two-line argument uses no Möbius
  expansion and no Cauchy–Schwarz — only Lemma 2 and Lemma 6 — so the **atom-level** corollary of
  this route is strictly subsumed, the honest kill boundary is `p > 1/2` rather than `p > 3/4`,
  and the activity bound a witness must satisfy is `μ{χ[U] ≠ 0} ≥ 1/2 − O(ε)`, not `1/4 − o(1)`.
  The *pointwise* Theorem is not subsumed: `|1 − Φ(M·1_C)| ≤ 4(1 − Re u_M) + 40Lε` is genuinely
  stronger than the two-piece triangle bound `2√(2(1 − Re u_M))` for small `1 − Re u_M`. The
  §5(a) remark "`n = 3` is optimal for this mechanism" inherits the same error and is likewise
  not supported.
- **Haar measure.** For `μ = ` Haar on `Â`, every `χ[U]` is uniform on `T`, so
  `μ{χ[U] = 0} = μ{χ[C] = 0} = 0` and Corollary 1 is vacuous. Consistent: Haar is exactly
  `V`-invariant and is killed on other grounds, not here.
- **`A` versus `z`.** The proof uses that `U_1 ⊔ U_2 ⊔ U_3 = C`, i.e. that the three cone phases
  sum to the *central* phase. The same expansion for a partition of a proper clopen set returns
  Corollary 3, a statement about `u_M` alone, and gives no information about `A`-invariant
  vectors. So the argument is of the type demanded in §5 of
  the `V`-invariant de Finetti kill: it separates `z = χ[[0]] + χ[[1]]` from a general element of
  `A`, and it does not prove the false almost-invariant analogue for `A`.

## 5. What this does not give, and one tool left behind

**(a) The gap.** Corollary 2 is empty once `μ{χ[U] = 0} ≤ 3/4`. Any compound Poisson law whose
Lévy measure charges `{χ[U] ≠ 0}` infinitely has `μ{χ[U] = 0} = 0`, and these are the canonical
`e^{−tN}` witnesses left open by `cantor-central-gaussian-scale-mixture-witnesses-die`. Raising
`4` in Lemma 5 is not the way: with `n` pieces the Möbius identity for odd `n` reads
`E∏_{i≤n}(1 − ζ_i) = 1 − Φ(M·1_C) + O(2^n Lε)` and the Hölder bound degrades to `2^{n−1}(1−Re u_M)`,
so `n = 3` is optimal for this mechanism.

**(b) Ruler partitions: `n`-fold exchangeability at cost `poly(n)` instead of `2^n`.** For `n ≥ 2`
put

  `P_n = { [1], [01], [0²1], …, [0^{n−2}1], [0^{n−1}] }`,

a partition of `C` into `n` cones. Every permutation of `P_n` is realized by an element of `V`
whose domain and range partitions are `P_n`, i.e. by an element with `n` pieces of depth `< n`,
whereas permuting the `2^d` cones of the depth-`d` partition needs `2^d` pieces. Every union of
parts is clopen, and proper unless it is all of `C`. Consequently the phases `(χ[P])_{P ∈ P_n}` of
any witness are `δ`-exchangeable in total variation with `δ = poly(n)·ε` (using the caret-count
estimate for the word length of an `n`-piece element of `V` — Birget, Burillo–Cleary–Stein–Taback;
recalled, not re-read, and only the polynomial growth is used), and every proper partial sum
`Σ_{P ∈ I} χ[P]` has the law of a single cone phase up to `poly(n)ε`, while the full sum is
`χ[C]`.

This removes the obstruction that blocks approximate de Finetti arguments on the depth-`d`
partition, where exchangeability of `n` cones costs invariance defect `2^n ε`. With ruler
partitions one may take `n → ∞` with `poly(n)ε → 0`.

**(c) Where the ruler route nevertheless dies.** De Finetti plus the merge relation forces the
directing measure to be idempotent, hence `Haar(H)`; the almost invariance `Re Φ(1_U) ≥ 1 − ε²/2`
forces `H = {0}` with probability near `1`; and the conclusion is then "`χ[P] = 0` for every
`P ∈ P_n`", which by `Σ_{P∈P_n} χ[P] = χ[C]` would give an atom at `χ[C] = 0`. The step that
fails is the last one, and it fails for a reason that is not quantitative slack: an approximate
argument can only conclude that each `χ[P]` is *small*, and the negation of the target asks only
that `χ[C]` be *nonzero*, not large. Summing `n` phases that are small but nonzero leaves `χ[C]`
nonzero. Any proof along these lines must therefore produce an exact-vanishing conclusion, which
is what the Cesàro average in Lemma 6 does and what a finite-`n` de Finetti estimate cannot do.
This is a sharper form of the recorded obstruction to approximate de Finetti proofs: the blocker
is not the cost of exchangeability (ruler partitions make it polynomial) but the exactness of the
event `{χ[C] = 0}`.

## 6. Referee record (2026-09-18, three lenses; two refuted the target as stated)

The route is kept as an attempt. What survives, what fails, and why the prerequisite was added.

**What all three lenses verified.** Lemmas 1–6, the pointwise Theorem
`|1 − Φ(M·1_C)| ≤ 4(1 − Re Φ(M·1_{[0]})) + 40Lε`, Corollary 1 in the form actually displayed
above (with the `16|h|_S ε` term), Corollary 2 and Corollary 3. Both imports are quoted verbatim
from `research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md`: §3(a) "`V` acts
transitively on the proper nonempty clopen sets" and the §3(f) third bullet
(`‖μ_ξ − μ_η‖_TV ≤ ‖ξ−η‖(‖ξ‖+‖η‖)`, and the spectral measure of `π(h)ξ` is `h_*μ_ξ`), and §3(c)
matches the generating set. Lemma 4's expansion is exact by finite additivity and all six
auxiliary sets `[1], [01], [00], C∖[00], C∖[01], [0]` are proper nonempty clopen (`C` itself is
not, which is exactly why the three first-order and three second-order terms cancel and the
central term survives). Lemma 3's `h·k`, `h·k'` are genuine `V`-elements with complete prefix
codes `{0,10,11} → {00,01,1}`. The first bullet of `cantor-integer-maps-central-growth-criterion`
used in Corollary 2 matches and is re-derived there.

**Load-bearing hypothesis (third lens, PASS on its own question).** Lemma 2 is where the
argument breaks for end-fixing / level-preserving tree-automorphism groups: those preserve the
Bernoulli measure `λ` and cannot carry `[0]` to `[00]`, so §3(a) transitivity on *all* proper
nonempty clopen sets — including sets of different `λ`-measure, i.e. the non-unimodularity of `V`
— is genuinely used, six times. Witness in the degenerate setting: `μ = δ_χ` with
`χ[U] = t·λ(U)` is exactly invariant under level-preserving automorphisms, has `ε = O(t)` from
the `A`-generators alone, `χ[C] = t ≠ 0`, and at `M ~ 1/(100t)` gives `|1 − Φ(M1_C)| ~ 0.063`
against `4(1 − Re Φ(M1_{[0]})) ~ 0.002 + O(t)`, violating the pointwise inequality. Monoids are
excluded too: Lemma 1 needs `π(h)` unitary and `h^{-1}`, and adjoining the partial map `x ↦ 0x`
makes `Φ(M1_C) ≈ u_M` and collapses the Theorem into the vacuous Corollary 3.

**Defect 1 (harmless, corrected here).** Lemma 2 writes "`χ[U] = χ[h[0]] = (h·χ)[0]`", which
contradicts the setting line `(h·χ)[U] = χ[h^{-1}U]`. The convention forced by
`⟨π(f)π(h)ξ, π(h)ξ⟩ = Φ(h^{-1}·f)` is `(h·χ)[U] = χ[hU]`; read as `χ[U] = (h^{-1}·χ)[[0]]` the
step is right, and since `|h^{-1}|_S = |h|_S` the estimate `|Φ(M·1_U) − u_M| ≤ 4|h|_S ε` stands,
uniformly in `M`. Nothing downstream changes.

**Defect 2 (fatal to the calibration).** §4, first bullet: see the inline correction there. The
constant `4` is not sharp at the atom level; `2p − 1 − O(ε)` follows from Lemma 2 and Lemma 6
alone and dominates `4p − 3 − Kε` everywhere. The sentences "the constant `4` cannot be improved
without further input" and "the calibration is exact" are false, and §5(a)'s "`n = 3` is optimal
for this mechanism" is unsupported.

**Defect 3 (why the prerequisite was added).** The target's headline and title state the atom
comparison "for every proper clopen `U`" with `K` absolute. Corollary 1 as proved carries the
extra `16|h|_S ε`, which grows with the depth of `U`; `K = 40L` is also a multiple of a *max* of
six word lengths, not a *sum*. The uniform-in-`U` statement with an absolute constant is
therefore not proved here, and the route now requires
`cantor-cone-phase-atom-comparison-is-depth-uniform`, which is exactly that missing step.

**Defect 4 (non-load-bearing).** §5(b)'s ruler-partition `poly(n)` word-length estimate is
"recalled, not re-read"; it sits in the explicitly non-load-bearing "what this does not give"
section.
