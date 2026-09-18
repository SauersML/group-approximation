---
rg: 2
id: pp-circle-divisible-subgroups-act-freely-proof
kind: route
target: pp-circle-divisible-subgroups-act-freely
requires: []
---

Direct proof. Not independently reviewed. Notation as in the target.

## Step 0. Two facts about `Λ`

- **(U) Unique continuation.** An element of `Λ` that is the identity on a
  nonempty open interval is the identity. A projective map fixing three points
  of `RP^1`, and an affine map fixing two points of `R`, is the identity.
- **(F) Finitely many fixed points on a piece.** Let `λ ∈ Λ` act nontrivially
  and let `I` be a closed arc. In case (P), `λ` has at most two fixed points on
  `RP^1`. In case (L), let `I~` be a lift of `I`, of length at most `1`. The
  points of `I~` fixed mod `1` solve `λ(x) - x ∈ Z` for an affine function `λ(x) - x`.
  If that function is constant and an integer, `λ` is an integer translation
  and fixes all of `I`. Otherwise each integer value is taken at most once, and
  only finitely many values are taken on `I~`.

So for `g ∈ PP_Λ(S^1)` the fixed set `Fix(g)` is a finite union of closed arcs
and points: on each closed piece `g` either fixes the whole piece or has finitely
many fixed points on it.

## Step 1. Freeness (item 1)

Let `g ∈ D`, `g ≠ 1`, and suppose `Fix(g) ≠ ∅`. By Step 0, `S^1 \ Fix(g)` has
finitely many components `J_1, ..., J_m`, with `m ≥ 1` because `g ≠ 1`. These are
the gaps of `g`.

*`D` fixes the endpoints of every gap.* Every `d ∈ D` commutes with `g`, so it
preserves `Fix(g)` and permutes the gaps. This gives a homomorphism
`D -> Sym(m)`. Its image is a finite divisible group, which is trivial: if `x`
lies in a finite group of order `M`, write `x = y^M`, which is `1`. So each
`d ∈ D` maps each gap `J_i` onto itself. An orientation-preserving homeomorphism
of `S^1` that maps an open arc onto itself fixes its endpoints. This includes
the case where the arc is `S^1` minus one point.

*Germ homomorphism.* Let `a` be an endpoint of a gap `J`, with `J` lying on the
positive side of `a`. For `d ∈ D`, `d(a) = a`, and there are `ε_d > 0` and a
unique `ρ(d) ∈ Λ` with `d = ρ(d)` on `[a, a + ε_d)`. In case (L) this holds for
the lift of `d` that fixes a chosen lift `a~` of `a`. Existence holds because
`B_d` is finite, and uniqueness by (U). Since `d'` fixes `a` and preserves
orientation, it maps a small `[a, a + ε)` into `[a, a + ε_d)`, so
`ρ(d d') = ρ(d) ρ(d')`. So `ρ : D -> Stab_Λ(a)` is a homomorphism.

*Conclusion.* `ρ(D)` is a divisible abelian subgroup of `Λ`, so `ρ(D) = 1` by
(D). In particular `g` is the identity on some `[a, a + ε)`, so `g` has fixed
points in `J`. That contradicts the definition of a gap. Hence `Fix(g) = ∅`.

## Step 2. Rotation numbers (items 2, 3, 5)

*Invariant-measure formula.* Let `A ≤ Homeo_+(S^1)` preserve a Borel probability
measure `μ`, and let `μ~` be its periodic lift to `R`. For a lift `f` of an
element of `A`, put `τ_μ(f) = μ~([x, f(x)))`, taken negative when `f(x) < x`.

- `f` preserves `μ~`. So `τ_μ(f)` does not depend on `x`:
  `μ~([x, f x)) - μ~([y, f y)) = μ~([x, y)) - μ~([f x, f y)) = 0`.
- `τ_μ(f h) = μ~([x, h x)) + μ~([h x, f h x)) = τ_μ(h) + τ_μ(f)`.
- `μ~([x, f^n x)) = n τ_μ(f)` and `μ~([x, x + k)) = k`. So `τ_μ(f)` is the
  translation number `lim f^n(x)/n`.

Hence `rot = τ_μ mod 1` is a homomorphism `A -> R/Z`. Every amenable `A`
preserves such a `μ`; in particular every abelian group does.

- **Item 2.** `D` is abelian, so `rot|_D` is a homomorphism. A circle
  homeomorphism has rotation number `0` exactly when it has a fixed point. By
  item 1 the kernel is trivial.
- **Item 3.** Let `h ∈ N_Γ(D)` and `d ∈ D`. Rotation number is a conjugacy
  invariant in `Homeo_+(S^1)`, so `rot(h d h^-1) = rot(d)`. Both elements lie
  in `D`, so item 2 gives `h d h^-1 = d`.
- **Item 5.** `rot` maps `D` injectively into `Q/Z`.

## Step 3. Amenable subgroups (item 4)

`A` amenable preserves some `μ`, so `rot|_A` is a homomorphism to the abelian
group `R/Z` and kills `[A, A] ⊇ D`. By item 2, `D = 1`. ∎
