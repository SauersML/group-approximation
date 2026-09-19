---
rg: 2
id: polygonal-anzai-codings-lift-only-finitely-many-rotations
kind: claim
title: In a subshift that is an almost 1-1 extension of the Anzai skew product (x,y) ↦ (x+α, y+x) with polygonal singular set, only finitely many fibre rotations lift to automorphisms, because rotations preserve slopes while the dynamics shears them; so the targets T1/T2 need singular sets containing pieces of unboundedly many tilts (hierarchical, simulation-type codings), and T1 would also give a minimal zero-entropy free Z^d-SFT with a free group of automorphisms
requires:
  - profinite-skew-layers-collapse-into-the-equicontinuous-factor
  - ra-forces-amenable-commutants-of-uniquely-ergodic-rigid-rows
  - quantum-rigid-subshifts-are-determined-by-thick-collars
distinct_from:
  profinite-skew-layers-collapse-into-the-equicontinuous-factor: that shows lifted fibre translations must commensurate the singular set Z_1; this shows that for tame (polygonal) Z_1 over a twisted base the commensurating rotations form a finite group, identifying the twist-versus-symmetry tension that T1 must overcome.
  ra-forces-amenable-commutants-of-uniquely-ergodic-rigid-rows: that shows T1, if built, refutes (RA_free); this rules out the geometric codings as a way to build it, and records its zero-entropy consequence.
---

**ESTABLISHED** (lane bh-invent-16, 2026-09-19; lane proof, elementary; not reviewed; no priority
claimed). It is a calibration for targets T1 and T2 (Line I). The circle fibre is abelian, so this says
nothing directly about (RA_free). It shows which codings cannot work.

## Setting

- `Z = T^2`, with `T(x, y) = (x + α, y + x)`, `α` irrational. This is Anzai's skew product: minimal,
  distal and not equicontinuous.
- The fibre rotations `R_t(x, y) = (x, y + t)` commute with `T`.
- `Y` is a Z-subshift with a factor map `ρ : Y → Z` that is almost 1-1.
- `Z_1 = {z : some y, y' ∈ ρ^(-1)(z) have y(0) ≠ y'(0)}`, as in item 4 of
  `profinite-skew-layers-collapse-into-the-equicontinuous-factor`.
- `Z_1` is **polygonal**: a finite union of closed line segments in `T^2`.
- `G_lift` is the set of `t` such that `R_t` lifts to an automorphism of `Y`. It is a subgroup of the
  circle.

## Statement

1. `G_lift` is finite.
2. **Mechanism.** Fibre rotations preserve slopes, while `T^n` adds `n` to the slope of every
   non-vertical segment. The singular set `Z_sing = ⋃_n T^n Z_1` therefore meets each slope window in a
   compact set, and a compact set invariant under an infinite (hence dense) group of fibre rotations
   would contain whole fibres.
3. **Consequence for T1 and T2.** Take a twisted skew product `M ×_c K` with lifted fibre translations
   dense in `K`. By the same mechanism, whenever the derivative cocycle shears tangent planes properly,
   the singular set must contain pieces of unboundedly many tilts in every tilt window. Geometric codings
   (polygonal or cut-and-project, bounded tilt) are then excluded. What remains are wild, hierarchical
   boundaries, which is what fixed-point simulation produces. This is a design constraint, proved here only
   in the abelian, polygonal case of item 1.
4. **Zero-entropy consequence.** If T1 exists, then some minimal, free, zero-entropy `Z^2`-SFT has an
   automorphism group containing `F_2`.
   - Rigid subshifts over amenable groups have zero entropy
     (`quantum-rigid-subshifts-are-determined-by-thick-collars`).
   - So T1 would answer a `Z^2`, minimal, finite-type form of the question behind the Cyr–Kra amenability
     theorems. Cyr and Kra prove amenability of `Aut` for `Z`-subshifts of complexity `o(n^2/log^2 n)`
     (arXiv:1708.06253, abstract read), in the negative direction for rigid rows.

## Proof of 1

- *Segments and slopes.* Write `Z_1` as finitely many segments, and let `Sl` be the finite set of their
  slopes (`∞` for vertical). Since `T^n(x, y) = (x + nα, y + nx + n(n−1)α/2)` is affine, `T^n` maps a
  segment of slope `s` to a segment of slope `s + n`, and vertical segments to vertical segments.
- *Local coincidence.* Let `t ∈ G_lift`. By item 4 of the collapse node,
  `R_t(Z_1) ⊆ ⋃_(|n| ≤ R) T^n Z_1`. A segment inside a finite union of segments coincides, on a dense
  open subset of itself, with pieces of segments of the same slope.
- *Slope windows are compact.* For `a ∈ R`, let `S_a` be the union of the segments of `Z_sing` with slope
  in `[a, a+1)`.
  - Only the `n` with `(Sl − n) ∩ [a, a+1) ≠ ∅` contribute, and there are at most `|Sl|` of them.
  - So `S_a` is a finite union of segments, and it is compact.
  - `R_t` preserves slopes and `Z_sing`. By local coincidence and closure, `R_t(S_a) ⊆ S_a`, and likewise
    for `−t`.
- *Infinite `G_lift` forces full fibres.* If `G_lift` is infinite, its closure is the whole circle, so
  `S_a` is invariant under every fibre rotation. It is then a union of full fibres `{x} × T`. But a finite
  union of non-vertical segments meets each fibre in finitely many points. So `S_a = ∅` for every `a`.
- *Conclusion.* Then `Z_1` is vertical, so every cell boundary is vertical, and the coding
  `y ↦ y(0) = f(ρ y)` depends only on `x`. The same holds for all coordinates, since `T^n` preserves
  verticality. So `ρ` is injective on no fibre over the base circle, contradicting almost 1-1.

  Hence `G_lift` is finite. ∎

## Lesson for general BH

**Twist and symmetry pull in opposite directions.** A twisted, non-equicontinuous base is exactly what
Line I needs: that is where infinite fibres over the MEF come from. But a twisted base shears every tame
boundary piece, while fibre symmetries preserve the shape of each piece. A geometric coding can therefore
host only finitely many fibre symmetries.

A dense commutant, and with it the time-lift counterexample to (RA_free), needs singular sets that already
contain every sheared copy of themselves: self-similar, hierarchical boundaries. So T1 is a
fixed-point-simulation problem, the same mechanism that gives rigidity. It would at the same time be a
minimal zero-entropy `Z^2`-SFT with a free group of automorphisms.
