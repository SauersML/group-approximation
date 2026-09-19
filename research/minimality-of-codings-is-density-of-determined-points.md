---
rg: 2
id: minimality-of-codings-is-density-of-determined-points
kind: claim
title: An extension of a minimal base with some one-point fibres is minimal iff the points over one-point fibres are dense; for skeleton-varying E1 designs this is the exact minimality condition, product time flows cannot be sheared along the input group, and downhill then needs central letters
distinct_from:
  relational-spine-couplings-are-splittable-or-not-minimal: that proves minimality of one end-flow clock by hand; this isolates the general criterion behind it, valid for every extension of every minimal system.
  strongly-proximal-geometries-are-disjoint-from-measured-inputs: its Theorem 3 says injective codings over a minimal product skeleton-times-input force the input to be of finite type; this says what minimality needs once fibres are allowed to be non-trivial.
  e2-for-plane-lifts-is-clustered-floating-freedom: its Theorem C kills transport-coupled lifts over Lambda_0-constant skeletons; this states the minimality condition for the replacement design (b), where the skeleton varies along the acting group.
---

**ESTABLISHED (lane bh-g2-fixedpoint-b, 2026-09-18; elementary lane proofs, not reviewed; no
priority claimed).** Written for design (b) of the (★′) build.

## Theorem 1 (the criterion)

Let `Λ` be a countable group, `Z` a compact metrizable `Λ`-space, and `π : Z → J` a factor map onto
a **minimal** `J`. Let `J_det = {j ∈ J : π^(-1)(j) is one point}`. It is invariant. If
`J_det ≠ ∅`, then

```text
Z is minimal   ⟺   π^(-1)(J_det) is dense in Z.
```

*Proof.*
- **(⟸)** Take `z ∈ Z` and `j_0 ∈ J_det`, with `π^(-1)(j_0) = {z_0}`.
  - `J` is minimal, so `g_k π(z) → j_0` for some sequence `g_k`.
  - Every limit point of `g_k z` lies in `π^(-1)(j_0) = {z_0}`, by continuity. By compactness,
    `g_k z → z_0`.
  - So the orbit closure of `z` contains `π^(-1)(J_det)`, and hence its closure, which is `Z`.
- **(⟹)** `π^(-1)(J_det)` is nonempty and invariant, so it is dense in a minimal `Z`. ∎

**What `J` is for a simulation.** Take `J = (τ, φ)(Z)`, the joint image in skeleton × input. Then
`J_det` is the set of skeleton–input pairs whose computation is fully determined. The free points
over `J ∖ J_det` are the floating locus.
- By Theorem 3 of `strongly-proximal-geometries-are-disjoint-from-measured-inputs`, if `J = T × Y`
  is a minimal product and every fibre is a point, then `Y` is an SFT.
- So for a non-SFT input either free points exist, or `J` is a proper joining. The skeleton then
  reads the input, and `T × Y` is not minimal.
- Theorem 1 says what free points need: they must be **limits of determined points**. This is
  *boundary completeness*. The end-flow clock of `relational-spine-couplings-are-splittable-or-not-minimal`
  is an instance, where the determined points are those with no spine.

## Theorem 2 (product time flows cannot vary along Λ_0)

Let `Λ = Λ_0 × F_m`, with the end shift `X_∂(F_m)` carried in every plane `{λ} × F_m`. No
nontrivial translation shear couples the flows of adjacent planes by a local rule.
- **Left shear `x(λs, v') = x(λ, g^(-1) v')`.** Its offset `v' ↦ g^(-1) v'` is not a fixed
  right-multiplication, so it is not a rule of bounded radius unless `g = 1`.
- **Right shear `x(λs, v' w) = x(λ, v')`, with `w ≠ 1`.** Write `R(x)(u) = x(u w^(-1))`. `R`
  commutes with the `F_m`-action.
  - *All or nothing.* `{x ∈ X_∂ : R(x) ∈ X_∂}` is closed and invariant, and `X_∂` is minimal. So
    either every coupled pair of planes violates the end-shift rule, or `R` maps `X_∂` to itself.
  - *If it maps `X_∂` to itself.* Then `R` is an equivariant continuous self-map of `∂F_m`. The
    boundary action is minimal and strongly proximal, so `R` is the identity: `x(u w^(-1)) = x(u)`
    for all `x` and `u`.
  - *That fails.* Choose `t ∈ S` different from the first letter of `w` and from the inverse of its
    last letter, which is possible since `|S| >= 4`. Take `ξ = u t^(+∞)`. Then `x(u) = t`, while the
    ray from `u w^(-1)` to `ξ` runs through `u` and starts with the first letter of `w`.

So in `Λ_0 × F_m` the time flows cannot be made to vary along `Λ_0` by translating one plane's
flow into the next. Other local couplings are not ruled out here. Plane-constant skeletons are the
case killed for transport couplings by Theorem C of `e2-for-plane-lifts-is-clustered-floating-freedom`.
**Design (b) therefore has to put its tree inside `Λ_0`,** for example the Bass–Serre tree of the
free `Z` factor of `(Λ_1 × Z) * Z`. This is the carrier principle.

## Theorem 3 (downhill in design (b), and what it needs)

Put the flow on a tree inside `Λ_0`, and let the seeded, time-graded layers read the input. The
abstract downhill lemma of `downhill-centrality-needs-no-data-rigidity` (part A) applies with
`δ_b = d_T`, given its hypotheses.
- **(F1) Flow commutation** holds when the flow layer's marginals form a family for a rigid shift.
  An example is a rigid end or seed SFT of the tree direction; v6 supplies `C_Z` gluings of this
  kind.
- **(F2) Flow–data commutation is no longer free.** The flow is not constant along the input
  direction, so the product-constancy argument is unavailable.
  - (F2) holds once the input letters are central.
  - They are central, whatever the input, in crossing-wire table designs: Theorem A of
    `e2-for-plane-lifts-is-clustered-floating-freedom`, via copied table wires that cross.
  - With bounded reading instead, (F2) needs the input itself to be rigid
    (`downhill-centrality-needs-no-data-rigidity`, part B).
- **(F3), (F4)** are the one-predecessor rule and the tree potential. They are design
  obligations of the seeded layer.

Then the flow is central, and E2 reduces to relative rigidity at infinite depth
(`causal-depth-localizes-quantum-noncommutativity`).

## Exactly what makes design (b) minimal

For a seeded coding `Z` with skeleton–input joining `J`, assume (M2). Then `Z` is minimal if and
only if (M1) and (M3) hold:
- **(M1)** `J` is minimal. This is a property of how the skeleton reads the input. It is not
  automatic for a proper joining: it must be checked, or arranged by taking `J` to be a minimal
  joining.
- **(M2)** `J_det ≠ ∅`: some skeleton–input pair has every computation seeded at finite depth.
- **(M3) Boundary completeness.** Every completion over a pair with an infinite-depth site is a limit
  of completions over `J_det`.

The "if" is Theorem 1. For the "only if", `J` is minimal because it is a factor of `Z`, and (M3)
is the density in Theorem 1.

**Known behaviour of (M3).**
- It holds for functional seeded phases with one transitive time cycle.
- It fails for relational couplings and for non-transitive cycles, by
  `relational-spine-couplings-are-splittable-or-not-minimal`.
- It fails for every transport-coupled design over a `Λ_0`-constant skeleton, because a parallel
  section is an invariant factor (Theorem C there).
- For genuine computations, (M3) says: every unseeded run that the local rules allow on an
  infinite-depth region is a limit of seeded runs. There must be no junk at infinite depth. This is
  BSS obstacle (a), stated as an exact condition.

## Lesson for general BH

Minimality of a simulating SFT is never a mystery once the determined configurations are known. It
is exactly the density of determined configurations, over a minimal skeleton–input joining.
- **The E1 obligation is boundary completeness.** Whatever the rules allow where computation reaches
  back forever must already be a limit of seeded computation.
- **The skeleton must vary inside the acting group.** Product time flows cannot be sheared, and
  plane-constant skeletons fall to Theorem C.
- **In design (b), E2 is downhill centrality plus central letters.** The table-crossing mechanism
  gives the central letters. The two gates meet at the same infinite-depth locus: E1 wants it to be
  seed-approximable, and E2 wants it unsplittable.
