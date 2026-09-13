---
rg: 2
id: compression-defects-die-in-rigid-targets
kind: claim
title: Every homomorphism into a finite group or a linear group kills the intrinsic compression defect of every subgroup, with no property (T)
distinct_from:
  unsquared-defect-finite-model-invisible: that is one specific defect of one specific group; this is the target-agnostic lemma for every subgroup of every group.
  a-t-menable-groups-have-no-rigid-compression-defect: that concerns a-T-menable source groups; this concerns rigid targets (finite or linear) for arbitrary source groups.
  compression-defect-dies-in-finite-dimensions: that is the older Lean-certified theorem that every finite-dimensional representation over every field kills the defect (with compressors generated as a group, a larger defect), which already contains the linear case here and, through the regular representation, the finite case; this adds only the target-agnostic Lemma C through a rigid support and a Zariski-closure proof.
  locally-residually-finite-targets-kill-compression-defects: that kills the defect of a finitely generated subgroup in every locally residually finite target by cardinality, which already contains the finite case here for finitely generated L; this states the finite case for every L through the same counting and places it under one support lemma with the linear case.
  zariski-envelope-compression-rigidity: that proves that compression preserves the Zariski envelope of the image in every complex finite-dimensional representation, the rigidity used in the linear case here; this uses that rigidity over an arbitrary field only to kill the defect.
artifacts:
  - research/artifacts/un-open-8-target-agnostic-compression-2026-09-13.md
---

**ESTABLISHED, unreviewed.** For `L <= G` let
`D_G(L) = << [ucu^-1, l] : uLu^-1 <= L, c in C_G(L), l in L >>_G` (tex eq. (intrinsic-defect), l.167).

**Lemma C.** Let `ψ: G -> H` be a homomorphism, `u` a compressor of `L`, `c in C_G(L)`, `l in L`. If some
`S <= H` contains `ψ(L)`, every element of `H` commuting with `ψ(L)` commutes with `S`, and
`ψ(u)Sψ(u)^-1 = S`, then `ψ([ucu^-1, l]) = 1`.

**Theorem.** If `H` is finite, or `H = GL_d(K)` for a field `K`, then `ψ(D_G(L)) = 1` for every `L <= G`.
In particular every finite group and every linear group has `D_G(L) = 1` for all `L`.

- Finite `H`: `S = ψ(L)`, rigid by counting.
- Linear `H`: `S` is the Zariski closure of `ψ(L)` in `GL_d(K̄)`, rigid by dimension and component count.
- Contrast: at MF targets the same lemma needs (T) for `L` and gives only Hilbert–Schmidt invisibility (tex Cor
  l.581). For tracial targets no rigid support is known.

Model test: in `GL_2(Q)`, the integer unitriangular `L` with `u = diag(2,1)` is a proper compression, and the
defect is trivial, as it must be.

**Review (un-verify, 2026-09-13): PASS.** Lemma C, the finite case by counting, and the linear case (the Zariski closure is a closed subgroup; its conjugate is a closed subgroup of equal dimension and component count, hence equal) re-derived; `D_G(L)` matches tex eq. `intrinsic-defect` (l.167) verbatim. See `research/artifacts/un-review-2026-09-13-part8.md` §3.

**Credit and scope (un-verify, 2026-09-13, subsumption correction).** The Theorem is already contained in older established nodes: `compression-defect-dies-in-finite-dimensions` (Lean `compressionCentralizerDefect_le_ker`: every homomorphism `H → GL_k(V)`, every field `k`, `dim V < ∞`, kills the defect, even with compressors generated as a group) gives the linear case, and the finite case through the regular representation `H ↪ GL_(|H|)(k)`; `locally-residually-finite-targets-kill-compression-defects` gives the finite case by the same counting when `L` is finitely generated; the Zariski rigidity is `zariski-envelope-compression-rigidity` (complex case). What is genuinely new here is Lemma C, the target-agnostic formulation (any target with a rigid support `S ⊇ ψ(L)` whose commutant is the commutant of `ψ(L)` and which is stable under `ψ(u)`), and the Zariski-closure proof over arbitrary fields. See `research/artifacts/un-review-2026-09-13-part8.md` §5.
