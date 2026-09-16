---
rg: 2
id: radu-mark-is-bounded-by-every-vertical-elliptic-element
kind: claim
title: In every almost action of Radu's BMW lattice the mark (xz)^4 is at most four times the support of any nontrivial vertically elliptic element, up to a defect term of order word length times fixing radius
distinct_from:
  radu-mark-survives-only-if-horizontal-group-embeds: that is the exact statement that a kernel element fixing a vertex of T_v kills the mark; this is the metric version, valid in every almost action, with explicit constants in the word length and the fixing radius.
  radu-mark-is-controlled-by-one-commutator: that bounds the mark by the commutator [y(xz)^2y, xz] and the square defects; this bounds it by the support of any nontrivial element of <a,b,c>, and uses that lemma as its last step.
  radu-commutator-collapse: that asserts that the commutator collapses in every almost action; this bounds the mark by elliptic supports, and its calibration shows that the mark can collapse while every elliptic element stays macroscopic, so it does not reduce that claim to an elliptic collapse.
artifacts:
  - experiments/titz-witzel-kernel-sofic-2026-09-16/elliptic_support_check.py
  - experiments/titz-witzel-kernel-sofic-2026-09-16/elliptic_support_check_output.txt
---

**ESTABLISHED (unreviewed).** Let `G` be a group with a bi-invariant metric `d`, and let
`a,b,c,x,y,z ∈ G` satisfy `a^2 = ... = z^2 = 1`. Let `e1,...,e6` be the defects `d(w,1)` of
`axax, ayay, azbz, bxbx, bycy, cxcz`, put `ε = max e_i` and `δ = xz`.

Let `Γ_R`, `C = <a,b,c> ≅ C_2 * C_2 * C_2`, the vertical tree `T_v = Γ_R/C` and its base vertex
`o = C` be as in `radu-mark-survives-only-if-horizontal-group-embeds`. For a reduced word `γ` in
`a,b,c` of length `L >= 1`, let `r = r(γ)` be the largest `r` such that `γ` fixes the ball
`B(o,r)` of `T_v` pointwise. It is finite because `Γ_R` acts faithfully on `T_v` (item 2 there).
Write `γ_G` for the value of the word `γ` in `G`.

1. **Finite bound.**

   ```text
   d(δ^4, 1) <= 4 d(γ_G, 1) + (4L(r+4) + 48) ε.                         (EB1)
   ```

2. **Exact bound.** If `π : Γ_R → G` is a homomorphism, then

   ```text
   d(π((xz)^4), 1) <= 4 d(π(g), 1)                                       (EB2)
   ```

   for every `g ≠ 1` fixing a vertex of `T_v`, that is, every `g ∈ hCh^(−1) ∖ {1}`, `h ∈ Γ_R`.

3. **Fixing radius.** Write `#l(γ)` for the number of occurrences of the letter `l` in `γ`.
   * (a) `r = 0` iff `#c(γ)` is odd, and `r = 1` iff `#c(γ)` is even and `#b(γ)` is odd. If `L`
     is odd and `#b(γ)`, `#c(γ)` are both even, then `r = 2`. So `r <= 2` for every odd `L`,
     and then the constant in `(EB1)` is at most `24L + 48`.
   * (b) In general `r <= 3N_+(L) + 1 <= 9·2^L`, where `N_+(L)` is the number of reduced words
     of length at most `L` in `a,b,c` with an even number of `c`.
   * (c) *Observed, not proved.* Over all `3·2^(L−1)` reduced words of each length
     `L = 1,...,17`, `r <= max(2, L−1)`. The maxima of `r` are
     `2,1,2,3,2,4,2,5,2,8,2,8,2,10,2,10,2`; for instance `r((ab)^2) = 3` and
     `r(cbcbacbcba) = 8`.

**Consequences.**

* **(C1) Elliptic elements stay macroscopic under a kept mark.** Let `(a_n,...,z_n)` be
  involutions on finite sets whose square defects tend to zero in normalized Hamming distance,
  with `liminf d_H(δ_n^4, 1) >= m > 0`. For every fixed word representing a nontrivial
  `T_v`-elliptic element `g` of `Γ_R`, `liminf d_H(g_n, 1) >= m/4`.
* **(C2) Weighted girth of a marked solution.** If `d(δ^4,1) >= m > 0`, then `a,b,c ∈ G`
  satisfy no relation `γ` (a nontrivial reduced word with `γ_G = 1`) with
  `4L(r(γ)+4) + 48 < m/ε` (with `m/0 = ∞`). In particular they satisfy no relation of odd length
  `L < m/(24ε) − 2`, and none with an odd number of `c` and length `L < m/(16ε) − 3`.
* **(C3) Metric ultraproducts.** If `π : Γ_R → S_U` is a homomorphism into a metric ultraproduct
  of finite symmetric groups and `d(π((xz)^4),1) = m > 0`, then `π` is injective on every vertex
  stabilizer `hCh^(−1)`, and its image is `m/4`-uniformly discrete, hence closed in `S_U`. So the
  closure of `π(hCh^(−1))` in `S_U` is `π(hCh^(−1))` itself. A metric substitute for the
  profinite closure in Caprace's inclusion (the step recorded under `radu-commutator-collapse`)
  therefore cannot come from closing up the images of vertex stabilizers.

**Calibration.**

* **(K1) Only vertical ellipticity works.** `w = [δ^2, yδ^2y]` is a nontrivial reduced word of
  length 20 in `x,y,z`. It lies in `Λ_v = ker(Γ_R → Aut T_h)`
  (`radu-horizontal-projection-kills-delta-squared`), so it acts trivially on `T_h` and, as a
  nontrivial even-length element of `V`, hyperbolically on `T_v`. It dies in
  `G_2 = Γ_R/γ_2(Λ_v)`, which keeps the mark
  (`radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`, item 4). With the discrete metric
  on `G_2`, no bound `d(δ^4,1) <= const · d(w,1)` holds. So `(EB2)` has no analogue for
  `T_h`-elliptic or `T_v`-hyperbolic elements.
* **(K2) The converse fails.** `Q = Γ_R/Λ_v` is residually finite, and `C ∩ Λ_v = 1`. Let
  `Γ_R` act by left translation on finite quotients `F_j` of `Q` whose kernels shrink to `1`.
  These are exact actions, so all defects are 0. The mark `(xz)^4 ∈ Λ_v` acts trivially, but every
  fixed `g ∈ C ∖ {1}` eventually acts freely, so `d_H(g,1) = 1`. A collapse of the mark therefore
  does not force any elliptic element to collapse. Any proof of `radu-commutator-collapse`
  through an elliptic collapse must use the mark hypothesis, or some other property that fails
  for actions pulled back from `Q`.
* **(K3) Why `(EB1)` gives no collapse in finite models.** In a finite almost action,
  `C → Sym(X_n)` is an exact homomorphism with finite image `C_n`. So relations `γ_n` exist,
  with `L_n <= 2⌈log_2 |C_n|⌉ + 2`. But item 3(b) bounds `r_n` only exponentially in `L_n`, and a
  nonzero `ε_n` is at least `1/|X_n|`. The cost `L_n(r_n+4)ε_n` is therefore not controlled, and
  what survives is the girth condition `(C2)`.

**Scope.** This is Radu's mechanism (arXiv:1712.01091, Proposition `33nonrf`) with metric
bookkeeping. `(EB2)` is the quantitative form of item 3 of
`radu-mark-survives-only-if-horizontal-group-embeds`. It was not found in the sources read (Radu
§5; Titz Mite–Witzel arXiv:2509.05054v2, 3.4–3.6). The wider literature search is recorded in
notes/titz-witzel-kernel-sofic-swarm-2026-09-16.md. No novelty is claimed.

**Data.** The artifact script works in exact normal-form arithmetic of `Γ_R`. For every reduced
`γ` of length at most 17 it checks:
* item 3(a), 3(b) and the observation 3(c);
* the bookkeeping of Step 1 of the proof;
* the commutation of `k'` with `u`.

It also evaluates `(EB1)` and its intermediate steps on 120 perturbed permutation actions. There
are 940 instances with `ε > 0`, and the minimum slack is `71.7 ε`. The output ends `ALL_OK`.

Proof in `radu-mark-is-bounded-by-every-vertical-elliptic-element-proof`.
