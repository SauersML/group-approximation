---
rg: 2
id: cone-half-compressions-have-graded-rigid-commutants
kind: claim
title: A compression inside one Cuntz-cone half never changes the commutant in the whole matrix ring, because the compressed span is degree-dense, so no half configuration carries a rigid compression defect and exact compression certificates for the cone head bound are dead
distinct_from:
  compression-defects-die-in-rigid-targets: that kills the intrinsic defect after mapping to a finite or linear target; this kills it inside the non-linear, non-residually-finite group GL_20(L_(F_2)(1,2)) itself, for subgroups and compressors supported on one graded cone, with no target map.
  compression-gates-need-strict-unit-centralizer-chains: that shows a compressing automorphism with a unit root forces a strictly ascending chain of unit centralizers; this proves that for compressors of nonnegative degree acting on subspaces with finite-dimensional graded pieces the commutant chain is constant, so no such chain can start.
  depth-monotone-leavitt-subalgebras-are-stably-finite: that proves stable finiteness of depth-monotone subalgebras, which kills corner-type commutants one corner at a time; this uses only the Z-grading and finite-dimensionality of graded pieces, and kills every commutant, corner type or not.
  leavitt-cuntz-cone-halves-have-rf-amalgam-cover: that builds the residually finite amalgam cover and its Z-grading picture of the halves; this uses that grading to show that exact compressions in a half are invisible to every commutant in the whole group.
artifacts:
  - research/cone-half-compressions-graded-rigid-commutants-proof.md
  - experiments/cone-half-graded-rigidity-2026-09-17/check_graded_rigidity.py
  - experiments/cone-half-graded-rigidity-2026-09-17/output.txt
---

**ESTABLISHED** (route `cone-half-compressions-graded-rigid-commutants-proof`; lane swarm-0917-w18-w18-nh-follow,
reframing; unreviewed).

**Setting.** `R = L_(F_2)(1,2)` is Z-graded with `deg s_i = 1` and `deg t_i = -1`. Let `q = s_1 t_1`, and let
`R_+ = <s_1, s_2, q>` and `R_- = <t_1, t_2, q>` be the Cuntz cones. Put `Delta = St_20(R) = GL_20(R)`
(`leavitt-steinberg-map-iso-from-rank-three`), `Delta_+- = E_20(R_+-)` and `M = M_20(R)`. For `X ⊆ M`, `X'` is its
commutant in `M`. For a subgroup `L`, `C_Delta(L) = (F_2 L)' ∩ Delta`.

**Theorem A (graded rigidity of compressed commutants).** Let `R = ⊕_(j ∈ Z) R_j` be any Z-graded algebra over a
field `k`. Let `V ⊆ R_(>=0)` be a graded subspace with `dim_k V_j < ∞` for every `j`, and let `n >= 1`. Suppose:
- `u ∈ GL_n(R)` satisfies `u, u^-1 ∈ M_n(R_(>=0))`;
- `A ⊆ M_n(V)` is a `k`-subspace with `u A u^-1 ⊆ A`.

Then `(u A u^-1)' = A'` in `M_n(R)`. The same holds with `R_(<=0)` in place of `R_(>=0)`.

**Theorem B (the cone halves).** In `R = L_(F_2)(1,2)` we have `R_+ = span{s_μ, s_μ q}`. This is a graded
subalgebra of `R_(>=0)` with `dim (R_+)_j = 2^(j+1)`. Take:
- any subgroup `L <= GL_20(R_+)`, with or without property (T);
- any `u ∈ GL_20(R_(>=0))`, for example any `u ∈ Delta_+`, with `u L u^-1 <= L`.

Then `C_Delta(u L u^-1) = C_Delta(L)`. So `[u c u^-1, l] = 1` for every `c ∈ C_Delta(L)` and every `l ∈ L`. The
mirror statement holds for `R_-` and `R_(<=0)`, and so does the statement for any conjugate `g Delta_+- g^-1`.

**Corollary C.** The algebraic statement (HEC) is **false**. (HEC) asks for a Kazhdan `L <= Delta_+`, a compressor
`u ∈ Delta_+` with `u L u^-1 <= L`, and `c ∈ C_Delta(L)`, `l ∈ L` with `[u c u^-1, l] ≠ 1`. It is stated in the
w18-ptl-pull node `leavitt-cone-half-carries-rigid-compression-defect`, not landed at the time of writing.

In particular the proposed next test there, a strict compression of `E_3(F_2[s_1])` inside `Delta_+`, cannot give a
defect whatever the compressor.

## Class killed: exact rigid-compression-defect certificates for (QC)

**Members.** Every proof of the cone head bound `(QC)` of `leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`
of the following shape:
- choose a compression pair `(L, u)` in the cone cover `Gamma = Delta_+ *_(Delta_0) Delta_-`, with `L` Kazhdan and
  `u L u^-1 <= L` exact in `Gamma`;
- use a Hilbert-Schmidt or Kazhdan transfer to make `rho([u c u^-1, l])` small whenever the centralizing relators
  `[c, L]` are small;
- conclude smallness of the head from `[u c u^-1, l] ≠ 1` in the simple group `Delta`.

This covers the reduction `(QC) <= (HEC)` of the w18-ptl-pull node `cone-half-compression-defects-force-head-bound`.
It also covers every variant with a different Kazhdan subgroup, a non-Kazhdan `L`, or a compressor taken from the
larger depth-graded unit group `GL_20(R_(>=0))`.

- **Invariant.** The Z-grading of `R`, for which each cone `R_+-` sits in one sign of degree with *finite-dimensional*
  graded pieces, together with the valuation filtration `F_k = {x ∈ M : every entry has all components in degree >= k}`.
- **Death step.** The required strict inequality `C_Delta(u L u^-1) ≠ C_Delta(L)`. Four facts kill it:
  - the leading-term map `x ↦ u_0 x_j u_0^-1` is injective;
  - the graded pieces are finite-dimensional, so `gr(u A u^-1) = gr(A)`;
  - hence `u A u^-1` is dense in `A` for the filtration;
  - commutation with a fixed `y ∈ M` of degree range `[-m, m]` is continuous (`[y, F_k] ⊆ F_(k-m)`), and
    `∩_k F_k = 0`.
- **Why it is the whole class.** Bass-Serre localization (item 1 of `cone-half-compression-defects-force-head-bound`,
  and the FA fact in `leavitt-cone-cover-far-cross-relators-are-uniformly-small`, both w18) puts every exact Kazhdan
  compression pair of `Gamma` inside one common conjugate of a half. Theorem B then kills its defect in `Delta`. Any
  other lift of the compressor relation holds only modulo `K`, and in the Hilbert-Schmidt setting that is exactly the
  approximate regime already known to be lossy.

**Relation to the earlier constraints.** Theorem B strictly contains two of the constraints in
`leavitt-cone-half-carries-rigid-compression-defect`:
- **(C4)**, corner-type commutants die by stable finiteness. Here no hypothesis on the shape of `C_M(L)` is needed.
- **(C0)/(C1)**, with nothing assumed about the order of `u` or strictness.

It also explains **(C2)**, profinite invisibility, at the level of the grading. The compression `u A u^-1 ⊆ A` is
invisible to every degree truncation `M_20(R_+) -> M_20(R_+ / (R_+)_(>=k))`, since those quotients are
finite-dimensional. Invisibility modulo every truncation is exactly degree-density.

**What survives for (QC).** An exact algebraic configuration inside one half cannot certify `(QC)`. A proof of
`(QC)` in genuine representations of `Gamma` must therefore use relations that hold in `Gamma` only modulo `K`,
through approximate relators or rounding. This is the regime of `(HR)` and of the mixed-block coherence target (MW)
of `leavitt-cone-cover-far-cross-relators-are-uniformly-small`. The mixed Kun-Thom compressor
`s_11 t_1 + s_12 t_21 + s_2 t_22` has components in degrees `1, 0, -1`, so it escapes Theorem A. It is also exactly
the compressor that Bass-Serre localization forbids in `Gamma`.

## Attempts

Established; the proof is `cone-half-compressions-graded-rigid-commutants-proof`. The checker
`experiments/cone-half-graded-rigidity-2026-09-17/check_graded_rigidity.py` verifies several facts in the Leavitt
normal form:
- `R_+` is closed and graded, with `dim (R_+)_j = 2^(j+1)` for `j <= 4`;
- `u_0 (u^-1)_0 = 1` for 40 random `u ∈ E_3(R_+)`;
- the leading-term lemma holds in all 40 trials.

The output is in `output.txt`. The checker is a sanity check only; the proof does not depend on it.
