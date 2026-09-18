---
rg: 2
id: labbe-shift-is-quantum-rigid-iff-rigid-at-scale-two
kind: claim
title: Labbé's 19-tile Wang shift is quantum rigid iff it is rigid at scale 2 (commutation at sup-distance 4, the 229 legal 5x5 patterns); one non-commuting scale-2 operator tiling refutes rigidity at every scale
requires:
  - recognizable-morphisms-collapse-quantum-rigidity-to-one-scale
  - labbe-substitution-is-primitive-and-recognizable
  - morphism-towers-double-covariant-tiling-scales
  - minimal-aperiodic-wang-shift-exists
distinct_from:
  labbe-wang-shift-crossed-product-is-finitely-presented: that is the open rigidity question itself; this fixes the one scale at which it is decided.
  labbe-torus-tiling-algebra-has-scale-one-module: that decides exact matriciality (finite-dimensional periodic modules) at scale 1; this decides quantum rigidity (all operator families, any dimension) at scale 2.
  self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale: that excludes Labbé (letter-dependent shapes); this is the Labbé case.
artifacts:
  - research/artifacts/gq-bh-g2-labbe-morphic-scale-collapse.md
  - research/artifacts/gq-bh-g2-labbe-recognizability-radius.md
---

**ESTABLISHED (2026-09-18).** This is a lane proof by bh-g2-labbe, unreviewed. The recognizability radius is an
exact computation.

## Statement

Let `Ω_U` be Labbé's minimal aperiodic 19-tile Wang shift and `k` any field. The following are equivalent:
1. `Ω_U` is quantum rigid, i.e. `LC(Ω_U, k) ⋊ Z^2` is finitely presented
   (`sft-crossed-product-fp-iff-quantum-rigid`);
2. `Ω_U` is `2`-rigid (next paragraph);
3. `Ω_U` is `D`-rigid for every `D >= 2`.

`2`-rigid means: every family of idempotent partitions `(E_a(z))_(a ∈ U)` on a `k`-space of any dimension commutes,
provided that
- the `E(z)`, `E(z')` commute for `|z − z'|_∞ <= 4`, and
- products over each `5×5` box vanish on the non-occurring patterns (229 of the `19^25` patterns occur).

Equivalently, the idempotent commutator ideal satisfies `J_2(Ω_U) = 0`.

**Contrapositive.** A single non-commuting scale-2 family over `k` gives non-commuting families at scales
`2^j · 2` for all `j`. Then `LC(Ω_U,k) ⋊ Z^2` is not finitely presented. If `char k ∉ {3, 5}`, `D([[Ω_U]])` is not
finitely presented either (`zd-derived-full-group-fp-forces-quantum-rigidity`).

**Walls.** If `labbe-shift-is-wall-rigid` holds, `Ω_U` is `2`-wall-rigid: any two tilings have a difference set
that is connected under sup-steps `<= 4`. This is consistent with the partition data
(`experiments/labbe-sturmian-product-factor-2026-09-16/partitionU_data.txt`, torus side `φ^2`, unit translation):
- the horizontal fault lines `y ∈ {0, φ}` are hit in two adjacent rows, since `φ − φ^2 = −1`;
- the vertical lines `x ∈ {0, 1, φ}` are hit in three adjacent columns;
- the anti-diagonal lines `x + y ∈ {0, 1}` are hit in two adjacent anti-diagonals;
- all `(1, −φ)`-segments lie on the leaf through `0`, forming one leaf interval of length `φ^3`, and the whole orbit
  of a point on that leaf lies on it. The resulting difference set is the digital strip `{n : φn_2 − n_1 ∈ J}` with
  `|J| = φ^2`, which is `1`-connected.

## Proof

Apply `recognizable-morphisms-collapse-quantum-rigidity-to-one-scale` to `ω^2`, where `ω = α∘β∘γ`.
- **(H1).** `ω^2(L(Ω_U)) ⊆ L(Ω_U)`, and it is a 2-dimensional morphism: TA Theorem C
  (`research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md` §6).
- **(H2).** Every `ω^2`-image has sides `>= 2` (exact; TA §7 check 5 and the recognizability artifact).
- **(H3) at `R = 3`.** 420 legal `7×7` windows, no conflict (`gq-bh-g2-labbe-recognizability-radius.md`).
- **Radius.** `r = 1` (Wang tiles).

So `D_* = max(1, 1, 2) = 2`. The least possible `R` for `ω^2` is `3`, since `R = 2` has conflicts. Using `ω` alone
fails (H2).

## Where this leaves the Labbé questions

- **Crossed-product finite presentation.** `labbe-wang-shift-crossed-product-is-finitely-presented` is now a
  question about one explicit finite presentation, the scale-2 presentation `A_2 = C_2 ⋊ Z^2`:
  - generators: 19 idempotents at the origin and 2 translations;
  - relations: partition of unity, commutation within sup-distance `4`, and vanishing of the non-occurring `5×5`
    patterns.

  The question is whether `A_2 → LC(Ω_U,k) ⋊ Z^2` is injective.
- **Constraints on a proof.** A proof must be contextual: by `determinism-closure-certifies-quantum-rigidity`, no
  determinism argument works at any scale. It may use any larger scale, since `J_2 = 0 ⟺ J_D = 0`.
- **Constraints on a refutation.** A refutation needs one non-commuting scale-2 family, in any dimension. A
  finite-dimensional periodic one would also settle exact matriciality (`labbe-torus-tiling-algebra-has-scale-one-module`).

## Lesson for general BH

For gate E2 (quantum rigidity) of Track A, the calibration shift is now a single finite object. Labbé rigidity is
decided by one finitely presented algebra at commutation radius `4`. That is the same kind of statement as the
constant-shape scale collapse, now for the letter-dependent shapes that toral-rotation codings force. The two
remaining ways forward are:
- a contextual proof at scale 2, which must cross the four fault normals at resonant separations;
- a scale-2 operator tiling.

No renormalization or level induction can shortcut either: scale is invariant.

## Attempt on J_2 (2026-09-18, bh-g2-labbe)

See `labbe-scale-two-commutation-crosses-faults-at-distance-five`.
- **Certified.** Commutation at 26 of the 40 offsets at distance 5, via context splits plus the determinism steps they
  unlock.
- **Frontier.** The diagonal offsets `(±5,±5)`, `(±5,±4)`, `(±4,±5)`, `±(3,−5)`.
- **Excluded.** At the resonant `(6,0)`, any certificate supported in a `7 × 11` window.

A Gröbner run cannot terminate on `C_2` (one commutation orbit per displacement), so the window framework replaces it.
