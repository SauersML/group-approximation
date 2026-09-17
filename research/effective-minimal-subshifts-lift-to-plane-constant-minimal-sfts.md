---
rg: 2
id: effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts
kind: claim
title: Over a finitely presented group with solvable word problem, every effectively closed minimal subshift is a plane-invariant factor of a minimal SFT on the product with Z^2 whose Z^2-subaction is free
distinct_from:
  decidable-fp-groups-have-effective-minimal-free-subshifts: that asks that an effective minimal free subshift exist; this takes one as input and realizes it inside a minimal shift of finite type one Z^2 factor up.
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that is the existence statement (P1) for minimal free SFTs over overgroups; this is the simulation step that turns an effective minimal free subshift into one, with a fixed overgroup Λ_0 x Z^2.
  fp-subshift-full-group-subgroups-extend-to-sft: that extends a subgroup of a subshift full group to an SFT neighbourhood of the subshift; this realizes the subshift as a factor of a minimal SFT over a larger group.
---

**OPEN.** Premise (M1) of route
`minimal-free-sft-via-plane-constant-minimal-simulation`.

**Statement.** Let `Λ_0` be an infinite finitely presented group with solvable
word problem, and let `Y ⊆ B^{Λ_0}` be a nonempty, effectively closed, minimal
subshift. Put `Λ = Λ_0 x Z^2`. Then there are:
- a finite alphabet `A`;
- a nonempty subshift of finite type `X ⊆ A^Λ` on which `Λ` acts minimally;
- a continuous map `Φ : X -> Y`,

such that:
1. **Equivariance:** `Φ((λ,0)·x) = λ·Φ(x)` for all `λ ∈ Λ_0`.
2. **Plane invariance:** `Φ((1,z)·x) = Φ(x)` for all `z ∈ Z^2`.
3. **Z^2-freeness:** `(1,z)·x = x` for some `x ∈ X` forces `z = 0`.

**Where it comes from.** The case `Λ_0 = Z^d` without clause 2, in dimension
`d+1` rather than `d+2`, is Durand--Romashchenko. The abstract of arXiv:1802.01461
(fetched 2026-09-17; the body was not re-read) says:

> "every effective minimal (quasiperiodic) shift of dimension d can be
> represented as a projection of a subdynamics of a minimal (respectively,
> quasiperiodic) shift of finite type of dimension d+1."

The non-minimal analogue over `Z^2 ⋊ H` is Barbieri--Sablik's simulation
theorem (context only, not re-read). In simulation theorems of this kind the
simulated configuration is copied constantly along the computation directions,
which is exactly clause 2 (also context only).

**What it would need.**
- *Z^2-constant hierarchy layer.* A Robinson- or Mozes-type layer, constant
  along `Λ_0`. It gives clause 3 and computation zones of every level in every
  plane `{λ} x Z^2`.
- *Constant copy of `Y`.* A letter layer copying `y ∈ Y` constantly along each
  plane. It gives clauses 1 and 2.
- *Local reading of `Y`.* Zone computations that read `y` on growing
  `Λ_0`-balls by synchronized communication between the planes `λ` and `λs`,
  which carry the same hierarchy, and reject forbidden patterns of `Y`.
  Solvable word problem makes the balls computable.
- *Durand--Romashchenko minimality control.* The content of each zone must be
  determined by the `Y`-data it reads plus a bounded amount of freely recurring
  data.
  - `Y` is minimal, so it has decidable language and a computable recurrence
    function (`decidable-fp-groups-have-effective-minimal-free-subshifts`,
    equivalent forms).
  - Every window pattern then recurs, because the hierarchy is the same in
    every plane and `Y`-patterns recur syndetically in `Λ_0`.

**How it could fail.**
- *Unbounded reading pressure.* A cell of plane `μ` is read by the
  verifications centred at `μf^{-1}` for all `f` in the growing shapes. Over
  `Z^d` the shapes grow polynomially and DR's bookkeeping absorbs this. For
  `Λ_0` of exponential growth, the number of reading requests through a fixed
  cell of a level-`k` zone grows exponentially in the radius being verified.
  - The zone has polynomially many cells, so the verification radius at level
    `k` must be only logarithmic in the zone size.
  - This is compatible with recurrence but has to be checked against DR's
    minimality bookkeeping.
- *Content at `(λ,z)` depends on more than the local data.* Minimality of `X`
  needs a joint recurrence in `Λ_0` and `Z^2` of zone contents. If a zone's
  verification state depends on `y` on a `Λ_0`-region that is not syndetically
  repeated together with the hierarchy position, minimality fails.

**Consistency check.** With clauses 1–3 and a free `Y`, lemma
`plane-constant-minimal-sft-factors-are-effective-minimal` shows `Y` must
already have been effective and minimal. So (M1) asks for nothing beyond what
its hypothesis supplies.

## Attempts

**Attempt 1 (2026-09-17): product of `Y` with a minimal free `Z^2`-SFT.** Let
`T` be Labbé's minimal free Wang shift (`minimal-aperiodic-wang-shift-exists`).
Take `X_0 = { x : x(λ,z) = (y(λ), t(z)), y ∈ Y, t ∈ T }`, the product of `Y`
constant along planes with `T` constant along `Λ_0`.
- `X_0` is minimal, since the product group acts by the product of minimal
  actions.
- It satisfies clauses 1–3.
- *Dies at finite type.* If `X_0` were an SFT over `Λ_0 x Z^2`, the projection
  `x ↦ y` restricted to the slice `Λ_0 x {0}` would make `Y` defined by the
  finitely many forbidden `Y`-patterns inside the rule window. So `Y` would be a
  `Λ_0`-SFT, which is (P1) for `Λ_0` itself.
- So the `Y`-layer must be verified by computation in the planes, not by local
  rules. This is exactly the simulation that (M1) asks for.
