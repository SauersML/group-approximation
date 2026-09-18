---
rg: 2
id: cantor-central-witnesses-have-active-cone-phases
kind: claim
title: "Class-kill for central non-rigidity of C(C,Z) ⋊ V: every witness law obeys μ{χ[C] = 0} ≥ 4·μ{χ[U] = 0} − 3 − Kε for every proper clopen U, so a witness against relative (T) for <1_C> must have a nonzero phase on a fixed cone with probability at least 1/4; sparse random-character laws, including the cone-product laws that break relative (T) for the whole of C(C,Z), are excluded"
distinct_from:
  cantor-integer-maps-central-direction-has-relative-t: that is the full relative (T) statement for the centre; this is one unconditional inequality satisfied by every almost invariant law, which excludes the witnesses whose cone phases vanish with probability above 3/4 and says nothing about the rest
  cantor-central-witnesses-have-long-range-dependence: that bounds μ{χ[C] ≠ 0} by the invariance defect plus a conditional TV-dependence term, and is strong exactly when a pair of cone phases is nearly independent; this has no dependence term and no independence hypothesis at all, and is strong exactly when the cone-phase law has a large atom at 0, which is the opposite regime
  cantor-central-gaussian-scale-mixture-witnesses-die: that kills wrapped Gaussian laws by quadratic inclusion-exclusion of the covariance; this uses multiplicative inclusion-exclusion over a three-piece partition of C and applies to every law, Gaussian or not, with no moment assumption
  extractable-character-spectra-carry-no-almost-invariant-vectors: that kills the spectral parts carried by characters with an equivariant Borel extraction to Prob(C) by a paradoxical push-forward; this constrains the atom at 0 of the cone-phase law of an arbitrary spectral measure, including scale-incoherent characters, where no extraction exists
  cantor-integer-maps-pair-lacks-relative-property-t: that constructs the almost invariant cone-product laws that break relative (T) for the pair (G, C(C,Z)); this shows that exact family, and every family sharing its sparseness, can never be pushed onto the centre, and the inequality is an equality on it
  cantor-integer-maps-central-growth-criterion: that is the equivalence between central growth and almost invariant vectors with no 1_C-invariant vector; this is a quantitative constraint on the spectral laws that the criterion produces
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

**OPEN** as stated (demoted 2026-09-18 after an adversarial referee pass; see Attempts). Three
lenses read `cantor-central-witnesses-have-active-cone-phases-proof`; two refuted the node as
stated. Precisely:

- The **Theorem** below, **Corollary 1 in the `|h|_S`-dependent form**, **Corollary 2** and
  **Corollary 3** are verified by all three lenses and stand.
- The **title's quantifier** — the same inequality "for every proper clopen `U`" with a single
  absolute `K` — is *not* proved: what the route gives carries an extra `16|h|_S ε` that grows
  with the depth of `U`. That missing step is now
  `cantor-cone-phase-atom-comparison-is-depth-uniform`, required by the route.
- The **sharpness and calibration content is false.** By finite additivity
  `χ[C] = χ[[0]] + χ[[1]]`, so inclusion–exclusion plus transport along the single first-letter
  swap gives `μ{χ[C] = 0} ≥ 2·μ{χ[U] = 0} − 1 − O(ε)` from the same two imports, with no Möbius
  expansion and no Cauchy–Schwarz. That dominates `4p − 3 − Kε` for every `p ≤ 1`. So the honest
  class boundary is `p > 1/2`, not `p > 3/4`, the honest activity bound is
  `μ{χ[U] ≠ 0} ≥ 1/2 − O(ε)`, not `1/4 − o(1)`, and the band `p ∈ (1/2, 3/4]` that this node
  advertised as surviving is already empty. The *pointwise* Theorem is not subsumed — it beats
  the two-piece triangle bound `2√(2(1 − Re u_M))` — but the atom-level corollary is.

The false sentences are corrected in place below and marked; nothing here is asserted as
established.

**Setting.** `C = {0,1}^N`, `A = C(C,Z)`, `G = A ⋊ V` with `(h·f)(x) = f(h^{-1}x)`, `z = 1_C`.
Write `T = R/Z` additively, `e(t) = exp(2πit)`, and `Â = Hom(A,T)`, so a character is the
finitely additive `T`-valued set function `U ↦ χ[U] := χ(1_U)` on the clopen algebra, with
`(h·χ)[U] = χ[h^{-1}U]`. Fix the generating set `S = S_V ∪ {±1_{[0]}}` of artifact §3(c). For a
unitary representation `π` of `G` and a unit vector `ξ` put `ε = max_{s∈S} ‖π(s)ξ − ξ‖`,
`Φ(f) = ⟨π(f)ξ, ξ⟩ = ∫ e(χ(f)) dμ(χ)`, where `μ = μ_ξ` is the `A`-spectral law of `ξ` on `Â`.

**Theorem (pointwise phase inequality).** There is an absolute constant `K` (a sum of six word
lengths in `S`) such that for every `π`, every unit vector `ξ` and every `M ∈ Z`,

  `|1 − Φ(M·1_C)| ≤ 4·(1 − Re Φ(M·1_{[0]})) + K·ε`.

**Corollary 1 (atom comparison).** Averaging over `M` and applying Wiener's theorem on `T`,

  `μ{χ[C] = 0} ≥ 4·μ{χ[[0]] = 0} − 3 − K·ε`,

and, for an arbitrary proper nonempty clopen `U` with `h ∈ V` carrying `[0]` to `U`,

  `μ{χ[C] = 0} ≥ 4·μ{χ[U] = 0} − 3 − K·ε − 16·|h|_S·ε`.

**Corollary 2 (class-kill).** Let `π` have no nonzero `π(1_C)`-invariant vector, so that
`μ{χ[C] = 0} = 0` by `cantor-integer-maps-central-growth-criterion`. Then for every proper
nonempty clopen `U` and every `h ∈ V` with `h[0] = U`,

  `μ{χ[U] ≠ 0} ≥ 1/4 − (K + 16|h|_S)·ε/4`.

So along any sequence witnessing failure of relative (T) for `(G, Z·1_C)` (`ε → 0`), the phase of
every cone of depth `o(1/ε)` is nonzero with probability at least `1/4 − o(1)`; equivalently, at
every depth `d` with `d = o(1/ε)` the expected number of cones `[w]`, `|w| = d`, with `χ[w] ≠ 0`
is at least `2^d(1/4 − o(1))`. A central witness is macroscopically active at every scale.

**Consequence for the flagship.** Failure of relative (T) for `(G, Z·1_C)` is a necessary
prerequisite for Problem B(Z) and hence for the Haagerup property of `2V` and of every `nV`
(`cantor-integer-maps-central-growth-criterion`). So any positive answer to Zaremsky Problem 2.7
must produce almost invariant laws that are macroscopically active at every scale: no construction
whose random character is rarely nonzero on a fixed cone can work. Every published mechanism for
producing such laws on a group of this shape — Brothier's Theorem A, Cornulier–Stalder–Valette,
and the cone products of `cantor-integer-maps-pair-lacks-relative-property-t` — is of exactly that
rare-activity kind.

**Class killed.** Every witness law whose cone phase vanishes with probability above `3/4`:
*sparse* random characters. (**Referee, 2026-09-18:** the correct threshold from the same
imports is `1/2`, not `3/4` — the band `(1/2, 3/4]` is already dead by the two-piece argument in
the header, so this section understates what its own tools kill and the mechanism it credits is
not the one doing the work.) This includes

- the random cone-product laws `χ_S = ∏_{w∈S} ξ_w` of
  `cantor-integer-maps-pair-lacks-relative-property-t`, with inclusion probability `p → 0`: there
  `χ_S[U] = 1{∅ ∈ S}·ξ[U]` for `U = [0]`, so `μ{χ[[0]] = 0} = 1 − p → 1`. These are the only
  known laws that are `V`-almost invariant, tend to `δ_0` and have no `A`-invariant vector, and
  they break relative (T) for the pair `(G, A)`. ~~The inequality is an equality on them
  (`μ{χ[C] = 0} = 1` and `μ{χ[[0]] = 0} = 1`), so the bound is sharp~~ — **false (referee,
  2026-09-18):** the family sits at `(1,1)` in the limit `p → 0`, and the line
  `p_C = c·p_U − (c−1)` passes through `(1,1)` for *every* `c`, so it certifies nothing about
  `c = 4`; and `c = 2` is in fact achievable, see the header;
- the Poissonian and Bernoulli laws of Brothier's Theorem A and of Cornulier–Stalder–Valette,
  and every transplant of them, whose activity per cone tends to `0`;
- every compound Poisson law `e^{−tN}` with *finite* Lévy measure, as `t → 0`.

**Where every member dies.** ~~At the three-piece Möbius identity.~~ **Misattributed (referee,
2026-09-18):** every member of the killed class already dies at the *two-piece* identity
`χ[C] = χ[[0]] + χ[[1]]`. The three-piece expansion below is what produces the *pointwise*
Theorem, which is genuinely stronger than the two-piece triangle bound; it is not what kills the
class. For the partition
`C = [1] ⊔ [01] ⊔ [00]` into three cones, all of whose pairwise unions are again proper clopen and
hence `V`-equivalent to `[0]`, the three first-order and the three second-order terms cancel:

  `E ∏_{i=1}^{3}(1 − e(M χ[U_i])) = 1 − Φ(M·1_C) + O(ε)`,

while Cauchy–Schwarz on two of the three factors bounds the left side by
`4(1 − Re Φ(M·1_{[0]})) + O(ε)`. A sparse law makes the right side `o(1)` for every `M`, hence
`Φ(M·1_C) ≈ 1` for every `M`, hence an atom of mass near `1` at `χ[C] = 0`, hence a nonzero
`π(1_C)`-invariant vector.

**Invariant.** `p = μ{χ[U] = 0}`, the atom at `0` of the cone-phase law, equivalently the Cesàro
limit of `Re Φ(M·1_U)`. It is the same for every proper clopen `U` up to `O(|h|_S ε)`, by
transitivity of `V` on proper clopen sets — *not* up to an absolute `O(ε)`; that is
`cantor-cone-phase-atom-comparison-is-depth-uniform`, and it is open. No prior kill on this node
reads `p`: the dependence kill reads a TV-dependence, the Gaussian kill reads a covariance, the
extraction kill reads an equivariant location map, the de Finetti kill reads exact invariance.
(**Referee, 2026-09-18:** `p` is read by the two-piece argument in the header as well, which is
elementary, so "no prior kill reads it" overstates the novelty of the invariant.)

**What it leaves.** ~~Diffuse witnesses: laws with `μ{χ[U] = 0} ≤ 3/4`~~ — **wrong frontier
(referee, 2026-09-18): the surviving band is `μ{χ[U] = 0} ≤ 1/2`,** since `(1/2, 3/4]` is killed
by the two-piece argument; downstream lanes must not be pointed at `(1/2, 3/4]`. In particular
every
compound Poisson law whose Lévy measure gives infinite mass to `{χ[U] ≠ 0}` (there `p = 0` and the
inequality is vacuous). These are exactly the canonical `e^{−tN}` witnesses named as the surviving
class in `cantor-central-gaussian-scale-mixture-witnesses-die`, and they remain open. The
inequality also gives no information when `μ{χ[C] = 0} = 0` is imposed and `p` is already small,
so it does not decide `cantor-integer-maps-central-direction-has-relative-t`.

Route (kept as an attempt): `cantor-central-witnesses-have-active-cone-phases-proof`.

## Attempts

- **2026-09-18 (e2-w2-nv-relative-t, then adversarial referee pass; outcome: refuted as stated,
  returned to OPEN).** The route expands the three-piece Möbius product over
  `C = [1] ⊔ [01] ⊔ [00]`, cancels the first- and second-order terms by transitivity of `V` on
  proper nonempty clopen sets, bounds the product by Cauchy–Schwarz on two factors, and reads the
  atoms off by Cesàro averaging in the frequency. Three lenses read it; one passed, two refuted.
  - **Verified by all three lenses.** Lemmas 1–6; the pointwise Theorem
    `|1 − Φ(M·1_C)| ≤ 4(1 − Re Φ(M·1_{[0]})) + 40Lε`; Corollary 1 in the `|h|_S`-dependent form;
    Corollary 2; Corollary 3. Both artifact imports (§3(a) transitivity, §3(f) third bullet) are
    verbatim, §3(c) matches, and the growth-criterion bullet used in Corollary 2 is
    independently re-derived there. Lemma 2 is genuinely load-bearing: it fails for end-fixing /
    level-preserving tree automorphisms, which preserve the Bernoulli measure and cannot carry
    `[0]` to `[00]`, and an explicit `μ = δ_χ`, `χ[U] = t·λ(U)` violates the pointwise inequality
    in that degenerate setting. So the non-unimodularity of `V` is used, six times.
  - **Refuting reason 1 — the sharpness and calibration content is false.** The cone-product
    family of `cantor-integer-maps-pair-lacks-relative-property-t` sits at `(1,1)` as
    `p_incl → 0`, and `p_C = c·p_U − (c−1)` passes through `(1,1)` for *every* `c`; for finite
    `p_incl` it reads `0 ≤ c·p_incl`, slack for every `c`. So it calibrates nothing. Moreover
    `c = 4` is not optimal: finite additivity `χ[C] = χ[[0]] + χ[[1]]` gives
    `{χ[[0]]=0} ∩ {χ[[1]]=0} ⊆ {χ[C]=0}`, inclusion–exclusion gives
    `μ{χ[C]=0} ≥ μ{χ[[0]]=0} + μ{χ[[1]]=0} − 1`, and Lemma 2 applied to the single first-letter
    swap `b` gives `μ{χ[[1]]=0} ≥ μ{χ[[0]]=0} − 4|b|_S ε`, so
    `μ{χ[C] = 0} ≥ 2·μ{χ[U] = 0} − 1 − O(ε)`, which dominates `4p − 3 − Kε` for every `p ≤ 1`.
    Two of the route's own imports, no Möbius identity, no Cauchy–Schwarz, no Wiener theorem.
    Hence "the constant `4` cannot be improved without further input", "the calibration is
    exact", the kill boundary `3/4`, the activity bound `1/4 − o(1)`, the frontier
    "what it leaves: `p ≤ 3/4`", "where every member dies: the three-piece Möbius identity" and
    §5(a)'s "`n = 3` is optimal for this mechanism" are all wrong. The honest boundary is `1/2`.
  - **Refuting reason 2 — quantifier mismatch.** The title states the atom comparison "for every
    proper clopen `U`" with `K` absolute ("a sum of six word lengths in `S`"), but Corollary 1 as
    proved carries an extra `16|h|_S ε` growing with the depth of `U`, and `K = 40L` is a
    multiple of a *max* of six word lengths, not a sum. The uniform-in-`U` form is not proved;
    it is now `cantor-cone-phase-atom-comparison-is-depth-uniform`, required by the route.
  - **What survives and is worth keeping.** The pointwise Theorem is *not* subsumed: for small
    `1 − Re u_M` it beats the two-piece triangle bound `2√(2(1 − Re u_M))`. Corollary 3
    (near-positivity of the cone-phase transform, `|Im Φ(M·1_U)| ≤ 4(1 − Re Φ(M·1_U)) + O(ε)`
    with no `V`-ellipticity hypothesis) is untouched by either refutation. The ruler-partition
    tool of §5(b) and the recorded dead end of §5(c) are unaffected.
  - One lens (the citation lens) passed, finding only the Lemma 2 inverse slip
    (`χ[U] = (h^{-1}·χ)[[0]]`, absorbed since `|h^{-1}|_S = |h|_S`) and §5(b)'s "recalled, not
    re-read" word-length estimate, and itself recorded the same two-piece union bound as a
    strictly stronger consistency check.
