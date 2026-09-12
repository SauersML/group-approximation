import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.FinalOddMapComparison

/-!
# Kronecker pairing and the cohomology top-class action (Prompt 14)

This file connects the **mod-two homology generator action** to the **mod-two
cohomology top-class action** used by the final odd-map comparison, through the
Kronecker (evaluation) pairing

```text
⟨·, ·⟩ : Hⁿ(X; F₂) × Hₙ(X; F₂) → F₂,   ⟨c, x⟩ := (kroneckerMap X n).hom c x.
```

The mathematical content is the naturality identity `⟨f^* c, x⟩ = ⟨c, f_* x⟩`
(already proved as `kroneckerMap_naturality_apply`), which forces the scalar by
which `f^*` acts on a cohomology class `c` to equal the scalar by which `f_*`
acts on any homology class `x` paired nontrivially with `c`.

## Main declarations

* `kronecker_pairing_self_naturality` — the element form of Kronecker naturality
  for a self-map `f : X ⟶ X`, paired against a homology class:
  `⟨f^* c, x⟩ = ⟨c, f_* x⟩`. (Unconditional.)
* `cohomology_scalar_eq_homology_scalar` — **scalar equality** of the homology
  action and the cohomology action: if `f^* c = t • c`, `f_* x = s • x`, and
  `⟨c, x⟩ ≠ 0`, then `t = s`. (Unconditional, pure Kronecker pairing.)
* `exists_kronecker_pairing_ne_zero` — over `F₂` a nonzero cohomology class pairs
  nontrivially with some homology class (from `kroneckerMap_injective`).
* `cohomologyTopClass_action_eq_degree` /
  `cohomologyTopClass_action_eq_degree_of_ne` — **specialisation** to the sphere:
  given the top `F₂`-homology scalar action `ModTwoTopHomologyScalar e`, every
  nonzero top cohomology class scaling by `t` has `t = (degreeOfIso e f : ZMod 2)`.
  This is exactly the move *from the top cohomology action to the integer degree*.
* `modTwoTopClassComparison_of_topHomologyScalar_pairing` — an alternate, fully
  Kronecker-pairing proof of the existing reduction
  `ModTwoTopHomologyScalar e → ModTwoTopClassComparison e`, obtained by
  specialising the scalar equality to `t = 1`.
-/

open CategoryTheory

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable {X : TopCat.{0}}

/-- **Element form of Kronecker naturality for a self-map.** For `f : X ⟶ X` and
classes `c ∈ Hⁿ(X; F₂)`, `x ∈ Hₙ(X; F₂)`:

```text
⟨f^* c, x⟩ = ⟨c, f_* x⟩.
```

This is `kroneckerMap_naturality_apply` evaluated at the homology class `x`. -/
theorem kronecker_pairing_self_naturality (f : X ⟶ X) (n : ℕ)
    (c : cohomologyZMod2 X n) (x : homologyZMod2 X n) :
    ((kroneckerMap X n).hom ((cohPullback f n).hom c)) x
      = ((kroneckerMap X n).hom c) ((homologyPushZMod2 f n).hom x) := by
  rw [kroneckerMap_naturality_apply f n c]
  rfl

/-- **Scalar equality of the homology action and the cohomology action.** Let
`f : X ⟶ X` act on a cohomology class `c` by the scalar `t` (`f^* c = t • c`) and
on a homology class `x` by the scalar `s` (`f_* x = s • x`). If the Kronecker
pairing `⟨c, x⟩` is nonzero, then the two scalars coincide: `t = s`.

This is the precise statement that *the cohomology top-class action and the
homology generator action agree* whenever the pairing detects the class. The
proof is pure Kronecker naturality: `⟨f^* c, x⟩ = ⟨c, f_* x⟩` becomes
`t · ⟨c, x⟩ = s · ⟨c, x⟩`, and `⟨c, x⟩ ≠ 0` cancels in the field `F₂`. -/
theorem cohomology_scalar_eq_homology_scalar {n : ℕ}
    (f : X ⟶ X) (c : cohomologyZMod2 X n) (x : homologyZMod2 X n)
    (s t : ZMod 2)
    (hcoh : (cohPullback f n).hom c = t • c)
    (hhom : (homologyPushZMod2 f n).hom x = s • x)
    (hpair : ((kroneckerMap X n).hom c) x ≠ 0) :
    t = s := by
  have key := kronecker_pairing_self_naturality f n c x
  rw [hcoh, hhom] at key
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at key
  have hcancel : ∀ a b p : ZMod 2, p ≠ 0 → a * p = b * p → a = b := by decide
  exact hcancel t s _ hpair key

/-- **A nonzero `F₂`-cohomology class pairs nontrivially.** Over the field `F₂`
the Kronecker classifier is injective (`kroneckerMap_injective`), so a nonzero
class `c ∈ Hⁿ(X; F₂)` has a nonzero Kronecker functional, hence pairs nontrivially
with some homology class. -/
theorem exists_kronecker_pairing_ne_zero {n : ℕ} (c : cohomologyZMod2 X n)
    (hc : c ≠ 0) :
    ∃ x : homologyZMod2 X n, ((kroneckerMap X n).hom c) x ≠ 0 := by
  have hne : (kroneckerMap X n).hom c ≠ 0 := by
    intro h
    exact hc (kroneckerMap_injective X n (by rw [h, map_zero]))
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hne
  exact ⟨x, by simpa using hx⟩

/-- **The cohomology top-class action equals the integer degree.** Given the top
`F₂`-homology scalar action `ModTwoTopHomologyScalar e` (the remaining
topological input: `f_*` on `Hₙ(Sⁿ; F₂)` is multiplication by
`(degreeOfIso e f : ZMod 2)`), if a top cohomology class `c` is scaled by `f^*`
by the scalar `t` (`f^* c = t • c`) and pairs nontrivially with a homology class
`x`, then `t = (degreeOfIso e f : ZMod 2)`.

This realises the acceptance criterion of Prompt 14: it moves the comparison
*from the top cohomology action to the integer degree mod two*. -/
theorem cohomologyTopClass_action_eq_degree {n : ℕ}
    (e : SphereTopHomologyIso n) (h : ModTwoTopHomologyScalar e)
    (f : C(Sphere n, Sphere n))
    (c : sphereCohomology n n) (x : homologyZMod2 (TopCat.of (Sphere n)) n)
    (t : ZMod 2)
    (hcoh : spherePullback f n c = t • c)
    (hpair : ((kroneckerMap (TopCat.of (Sphere n)) n).hom c) x ≠ 0) :
    t = (degreeOfIso e f : ZMod 2) :=
  cohomology_scalar_eq_homology_scalar (TopCat.ofHom f) c x
    (degreeOfIso e f : ZMod 2) t hcoh (h f x) hpair

/-- **The cohomology top-class action equals the integer degree (nonzero
class).** Same as `cohomologyTopClass_action_eq_degree`, but the nontrivial
pairing is supplied automatically from `c ≠ 0` via `exists_kronecker_pairing_ne_zero`.
Thus, under `ModTwoTopHomologyScalar e`, the scalar by which `f^*` acts on **any**
nonzero top cohomology class is exactly `(degreeOfIso e f : ZMod 2)`. -/
theorem cohomologyTopClass_action_eq_degree_of_ne {n : ℕ}
    (e : SphereTopHomologyIso n) (h : ModTwoTopHomologyScalar e)
    (f : C(Sphere n, Sphere n)) (c : sphereCohomology n n) (t : ZMod 2)
    (hcoh : spherePullback f n c = t • c) (hc : c ≠ 0) :
    t = (degreeOfIso e f : ZMod 2) := by
  obtain ⟨x, hx⟩ := exists_kronecker_pairing_ne_zero c hc
  exact cohomologyTopClass_action_eq_degree e h f c x t hcoh hx

/-- **Alternate, Kronecker-pairing proof of the comparison reduction.** This
rederives the existing `modTwoTopClassComparison_of_topHomologyScalar` from the
scalar-equality machinery above: a fixed nonzero top class is the case `t = 1` of
`cohomologyTopClass_action_eq_degree_of_ne`, giving `1 = (degreeOfIso e f : ZMod 2)`. -/
theorem modTwoTopClassComparison_of_topHomologyScalar_pairing {n : ℕ}
    (e : SphereTopHomologyIso n) (h : ModTwoTopHomologyScalar e) :
    ModTwoTopClassComparison e := by
  intro f c hfix hc
  have hcoh : spherePullback f n c = (1 : ZMod 2) • c := by rw [one_smul]; exact hfix
  exact (cohomologyTopClass_action_eq_degree_of_ne e h f c 1 hcoh hc).symm

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

