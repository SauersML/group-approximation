---
rg: 2
id: injective-plane-lift-codings-force-finite-type
kind: claim
title: A minimal SFT over Λ_0 x Z^2 lifting Y plane-invariantly, in which the Y-coordinate together with some Λ_0-invariant Z^2-factor determines the point, forces Y to be a Λ_0-SFT
distinct_from:
  effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts: that is the open existence statement (M1); this kills every M1 design whose points are determined by their Y-coordinate plus a Λ_0-invariant factor, which covers its Attempt 1 and every unique-completion simulation.
  plane-constant-minimal-sft-factors-are-effective-minimal: that shows any plane-invariant factor of a minimal SFT is effective and minimal; this shows that if the factor map is injective modulo a Λ_0-invariant factor, then Y is even of finite type.
  durand-romashchenko-minimal-sft-simulation: that constructs almost 1-1 simulations over Z^d; this explains why their non-injective (floating) locus cannot be removed in any plane-constant analogue.
---

**ESTABLISHED (unreviewed).** Proof:
`injective-plane-lift-codings-force-finite-type-proof`.

**Setting.**
- `Λ_0` is a countable group, `Λ = Λ_0 x Z^2`.
- `X ⊆ A^Λ` is a nonempty minimal subshift of finite type.
- `Φ : X -> Y ⊆ B^{Λ_0}` is continuous and onto, with `Φ((λ,0)·x) = λ·Φ(x)`
  and `Φ((1,z)·x) = Φ(x)` (clauses 1 and 2 of
  `effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts`).
- `τ : X -> T` is continuous and onto a compact metric `Z^2`-system, with
  `τ((λ,0)·x) = τ(x)` and `τ((1,z)·x) = z·τ(x)`.

**Theorem.** If `x ↦ (τ(x), Φ(x))` is injective on `X`, then `Y` is a
`Λ_0`-subshift of finite type.

**What it kills.** Call an M1 design *uniquely completed* if the point of `X`
is recovered from `y = Φ(x)` together with data that is constant along `Λ_0`:
a `Λ_0`-constant hierarchy (Robinson, Mozes, Labbé, any `Z^2`-SFT), plus
zone contents computed deterministically from the hierarchy and `y`. Every
such design dies whenever `Y` is not an SFT, which is the only interesting
case (an SFT `Y` is already (P1) for `Λ_0`).
- *Invariant:* finite type, which is a conjugacy invariant over any group.
- *Step where every member dies:* the injectivity of `(τ,Φ)`, which makes `X`
  conjugate to the literal product of `T` and `Y`, whose finite type restricts
  to the slice `Λ_0 x {0}`.
- *Consequence for M1:* every solution must carry a *floating locus*: for
  every `Λ_0`-invariant factor `τ`, two distinct points with the same `τ` and
  the same `Y`-coordinate. In Durand--Romashchenko these are the
  non-injectivity points of the almost 1-1 structure (letters carried by
  infinite chains of fathers). This claim shows they are structurally
  necessary, and not an artifact of their bookkeeping.

**Scope.** Minimality of `X` is used only to make the image of `(τ,Φ)` all of
`T x Y`. Clause 3 (freeness) is not used.
