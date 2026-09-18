---
rg: 2
id: kazhdan-central-aperiodic-parts-in-2v-carry-no-measure
kind: claim
title: For an infinite-order central element z of a Kazhdan subgroup K of 2V, the aperiodic set of z is a nonempty closed K-invariant set with no K-invariant measure, on which z never returns into its own reading bricks
distinct_from:
  kazhdan-central-elements-of-2v-have-slope-free-periodic-points: that shows every periodic point of z has slope zero; this derives the structure of the remaining aperiodic part, which is where a counterexample to finite center would have to live.
  kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures: that is the measure criterion for all of K; this applies its item 1 to the aperiodic set of a central element.
  brin-thompson-aperiodic-elements-have-logarithmic-movement: that gives logarithmic excursions at every non-periodic point of any element; this adds centrality in a Kazhdan group, which makes the excursion data K-quasi-invariant and forbids comparable returns.
requires:
  - kazhdan-central-elements-of-2v-have-slope-free-periodic-points
  - kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures
  - brin-thompson-aperiodic-elements-have-logarithmic-movement
---

**ESTABLISHED** (lane proof, elementary from the required nodes; not reviewed; no
priority claimed).

**Setting.** `K ≤ 2V` has property (T), `z ∈ Z(K)`, and `s(g,x) ∈ Z²` is the slope
cocycle. Put `S_t(x) = s(z^t, x)`, `L(g)` for the table length, and
`Per(z)` for the set of `z`-periodic points.

1. **Periodic points form an open set, and `z` has finite order iff the aperiodic
   set is empty.**
   - At a point `x` of period `p`, the slope of `z^p` is `0`
     (`kazhdan-central-elements-of-2v-have-slope-free-periodic-points`). A prefix
     replacement with equal lengths that fixes `x` is the identity on its brick, so
     `z^p` is the identity near `x`. Hence `Per(z)` is open.
   - Put `Y = C² \ Per(z)`. It is closed, and it is invariant under `z` and under
     `K`, because `z` is central.
   - If `Y = ∅`, compactness gives a finite cover of `C²` by bricks on which fixed
     powers of `z` are the identity, so `z` has finite order.
2. **No invariant measure.** No nonempty closed `K`-invariant subset of `Y` carries
   a `K`-invariant Borel probability measure. Suppose `ν` were one.
   - By item 1 of `kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures`,
     some `x ∈ Y` has a clopen neighbourhood `O` fixed pointwise by a finite-index
     `K_1 ≤ K`.
   - Some power `z^j`, `j ≥ 1`, lies in `K_1`, so `z^j` is the identity on `O`.
     Then `x` is periodic, a contradiction.
3. **No comparable returns.** Let `x ∈ Y`, `t ≥ 1`, and let `B = Π w_jC` be a brick
   containing `x` on which `z^t` is a prefix replacement onto `Π v_jC`. Then
   `z^t B ∩ B = ∅`.
   - Otherwise each pair `w_j, v_j` is comparable, and `z^t` has a fixed point in
     `B` with slope `(|v_j| − |w_j|)_j`. That slope must be `0`, so `v_j = w_j`,
     `z^t` is the identity on `B`, and `x` is periodic.
   - In particular `z^t x` leaves the depth-`ℓ_t(x)` brick of `x`, where
     `ℓ^j_t(x) ≤ L(z) + max_{s<t}(−S^j_s(x))^+`. This bound is the reading-length
     recursion of `brin-thompson-aperiodic-elements-have-logarithmic-movement`.
   - So along the return times of any recurrent point of `Y`, some coordinate's
     exponent sum makes unbounded negative excursions.
4. **Quasi-invariance of excursion data.** For `g ∈ K`, all `t` and all `x`:
   `|S_t(gx) − S_t(x)| = |s(g, z^t x) − s(g, x)| ≤ 2L(g)`. This follows from
   `s(z^t g, x) = s(g z^t, x)`.
   - Consequently every asymptotic profile of `t ↦ S_t(x)` is `K`- and
     `z`-invariant. Examples are the drift `lim S_t/t` where it exists, the `limsup`
     and `liminf` of `S^j_t/t` and of `S^j_t/log t`, and the excursion exponents
     of item 3.
   - The drift of every `z`-invariant measure is `K`-invariant (the drift lemma of
     `kazhdan-subgroups-of-brin-thompson-groups-have-finite-center`).

**Gap left (why this does not yet prove finite center).** A contradiction needs one
of three things:
- **(a) A commensurated set.** A `K`-commensurated subset of an orbit `Kx ⊂ Y`
  that is infinite and co-infinite, which (T) forbids. It could be built from a
  quasi-invariant function with finite bands. The functions of item 4 are
  quasi-invariant, but they are bounded at each fixed time, so they do not give
  finite bands.
- **(b) A closing lemma.** A return of some `x ∈ Y` within its reading scale,
  which item 3 forbids. Recurrence alone gives returns, but not at the scale
  `2^{-ℓ_t}`.
- **(c) An invariant measure on `Y` by other means.** For example, by
  constructing a `K`-invariant mean on excursion data.

None is available. The model case to test is an infinite Kazhdan group commuting with
a minimal element of 2V, such as the SMART moving-tape map. Nothing known excludes it.
