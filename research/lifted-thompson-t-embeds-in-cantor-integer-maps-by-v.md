---
rg: 2
id: lifted-thompson-t-embeds-in-cantor-integer-maps-by-v
kind: claim
title: "The lift T-bar of Thompson's T embeds in C(C,Z) ⋊ T ≤ C(C,Z) ⋊ V ≤ 2V, with the central translation going to the constant function 1_C"
distinct_from:
  tbar-embeds-in-laurent-leavitt-unit-group: that sends T-bar into the Laurent-extended Leavitt unit group, with the translation going to the Laurent variable t; this sends T-bar into the group C(C,Z) ⋊ V ≤ 2V, with the translation going to 1_C, the element whose relative (T) is the open cantor-integer-maps-central-direction-has-relative-t. The winding labels are the same.
  cantor-maps-by-v-embed-in-next-brin-thompson-group: that embeds C(C,Γ) ⋊ V in (n+1)V; this puts the specific finitely presented central extension T-bar inside C(C,Z) ⋊ V, with the centre on Z·1_C
  va-singular-point-germ-groups-are-t-bar: that finds T-bar as a germ group of VA at singular points; this embeds T-bar as a subgroup of C(C,Z) ⋊ V and hence of 2V
---

**ESTABLISHED** by `lifted-thompson-t-embeds-in-cantor-integer-maps-by-v-proof`. Lane proof, not
independently reviewed. The construction uses the same winding labels as
`tbar-embeds-in-laurent-leavitt-unit-group-proof`. No priority is claimed.

## Setting

- `C = {0,1}^N`. Thompson's `T ≤ V` acts on `C` through the doubled circle. A cone `[β]`
  corresponds to the half-open dyadic interval `I_β = [0.β, 0.β + 2^(-|β|))` of `[0,1)`.
- `T̄` is the group of homeomorphisms of `R` that commute with `z(x) = x + 1` and descend to
  elements of `T` on `R/Z`. Write `ā ∈ T` for the image of `a ∈ T̄`.
- `A = C(C,Z)` is the group of locally constant integer functions. `V` acts on it by
  `(h·f)(y) = f(h^(-1) y)`, and the product in `A ⋊ V` is
  `(f,g)(f',g') = (f + g·f', gg')`.

## Statement

For `a ∈ T̄`, let `n_a : C → Z` be the winding label. On a cone `[β]` of a dyadic subdivision
adapted to `ā`, it takes the constant value `⌊a(x)⌋` for `x ∈ I_β`. Then

```text
Φ(a) = (n_a ∘ ā^(-1), ā)
```

is an injective homomorphism `T̄ → C(C,Z) ⋊ T`, and `Φ(z) = (1_C, id)`.

The group `C(C,Z) ⋊ T` sits inside `C(C,Z) ⋊ V`, which is inside `2V` by
`cantor-maps-by-v-embed-in-next-brin-thompson-group` with `n = 1` and `Γ = Z ≤ V`. So
`T̄ ≤ 2V ≤ nV` for every `n ≥ 2`, and the centre `⟨z⟩` goes to `Z·1_C`.

## Consequences

1. **Necessary condition for the goal.** If some `nV` with `n ≥ 2` has the Haagerup property,
   so does `T̄`. This is the route `lifted-thompson-t-a-t-menable-from-cantor-integer-maps` to
   `lifted-thompson-t-is-a-t-menable`.
2. **One-dimensional reduction of the central direction.** A cnd function on `C(C,Z) ⋊ V`
   restricts through `Φ` to a cnd function on `T̄`, and its value on `M·1_C` is its value on
   `z^M`. So relative (T) for `(T̄, ⟨z⟩)` implies
   `cantor-integer-maps-central-direction-has-relative-t`, and hence refutes the goal. This is
   the route `cantor-integer-maps-central-direction-via-lifted-thompson-t`.
3. **The open central-extension problem sits inside the goal.** `T̄` is a central extension of
   the Haagerup group `T` by `Z`. Its Euler class is bounded, because Poincaré's rotation number
   restricts to a homogeneous quasimorphism of `T̄` with `rot(z) = 1`. Its rational class is
   recalled as nonzero (Ghys–Sergiescu), but that is not verified here. Whether the
   Haagerup property lifts through central extensions is open in general (see
   `lifted-thompson-t-is-a-t-menable`). So any proof that `2V` is Haagerup must settle one
   instance of that open problem, namely `T̄`.
