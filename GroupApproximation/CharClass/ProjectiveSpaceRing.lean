import GroupApproximation.CharClass.ProjectiveSpaceCohomology

/-!
# `H^*(ℂP^n; F₂) = F₂[h]/(h^{n+1})`

Knowing the additive groups (`CharClass/ProjectiveSpaceCohomology.lean`) leaves
exactly one thing to prove about the ring: that the degree-2 generator `h` has
`h^n ≠ 0`.  Everything else is formal — each `H^{2m}` is one-dimensional, so a
nonzero element *is* a basis, and `h^{n+1}` lies in `H^{2n+2} = 0`.

The input is the **Gysin sequence** of the circle bundle `S(taut) → ℂP^n`, whose
total space is the sphere `S^{2n+1}`:

```text
⋯ → H^{k-2}(X) --⌣e--> H^k(X) --π*--> H^k(S) --δ--> H^{k-1}(X) --⌣e--> H^{k+1}(X) → ⋯
```

Where the sphere is acyclic, cupping with `e` is therefore an isomorphism
`H^{k-2}(X) ≅ H^k(X)`, and starting from `1 ∈ H^0` this walks `h^m` up the even
degrees without ever hitting zero.

As in `ProjectiveSpaceCohomology.lean`, the sequence enters as a `structure`, so
that everything here is a theorem about any space carrying one; the construction
of the sequence (from the Mayer–Vietoris of `P(L ⊕ 1) = E(L) ∪ (P(L⊕1) ∖ Z)`
together with Leray–Hirsch for `P(L ⊕ 1)`) is separate.

## Main declarations

* `cupPowE e m : H^{2m}(X)` — the `m`-th cup power of a degree-2 class.  It needs
  no degree transport: `2 * (m+1)` and `2 * m + 2` are definitionally equal.
* `GysinSequence` — the sequence, in element form.
* `GysinSequence.bijective_cupRight` — `⌣ e` is bijective where the sphere vanishes.
* `cupPowE_ne_zero` — `h^m ≠ 0` for `m ≤ n`: the ring generator has the expected order.
* `cupPowE_eq_zero_of_gt`, `eq_zero_or_eq_cupPowE` — `h^{n+1} = 0`, and `h^m` is a
  basis of `H^{2m}`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

/-! ## 1. Lines over `F₂` -/

/-- A one-dimensional `F₂`-vector space has exactly two elements, so any nonzero
element is a basis in the crudest possible sense. -/
theorem eq_zero_or_eq_of_line {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] ZMod 2) {x : M} (hx : x ≠ 0) (a : M) : a = 0 ∨ a = x := by
  have hex : e x = 1 := by
    have : e x ≠ 0 := fun h => hx (by simpa using congrArg e.symm h)
    revert this
    generalize e x = z
    revert z
    decide
  have hcase : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hcase (e a) with h | h
  · left
    simpa using congrArg e.symm h
  · right
    have : e a = e x := by rw [h, hex]
    exact e.injective this

/-- **The generator of a line over `F₂`.**  A one-dimensional `F₂`-vector space
has a *unique* nonzero element, so "the generator" needs no choice beyond
producing one, and `eq_lineGen_of_ne_zero` says any two constructions agree. -/
def lineGen {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (e : M ≃ₗ[ZMod 2] ZMod 2) : M :=
  e.symm 1

theorem lineGen_ne_zero {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] ZMod 2) : lineGen e ≠ 0 := by
  intro h
  have h1 : e (lineGen e) = 0 := by rw [h, map_zero]
  rw [lineGen, LinearEquiv.apply_symm_apply] at h1
  exact one_ne_zero h1

theorem eq_lineGen_of_ne_zero {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] ZMod 2) {x : M} (hx : x ≠ 0) : x = lineGen e :=
  (eq_zero_or_eq_of_line e (lineGen_ne_zero e) x).resolve_left hx

/-- Two presentations of the same line have the same generator. -/
theorem lineGen_eq {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (e e' : M ≃ₗ[ZMod 2] ZMod 2) : lineGen e = lineGen e' :=
  eq_lineGen_of_ne_zero e' (lineGen_ne_zero e)

/-! ## 2. Cup powers of a degree-two class -/

/-- The `m`-th cup power of a degree-2 class.  No degree transport appears:
`Nat.mul` recurses on its second argument, so `2 * (m + 1)` reduces to `2 * m + 2`,
and `2 * 0` reduces to `0`. -/
def cupPowE {X : TopCat.{0}} (e : Hmod2 X 2) : (m : ℕ) → Hmod2 X (2 * m)
  | 0 => one X
  | (m + 1) => cup (cupPowE e m) e

@[simp] theorem cupPowE_zero {X : TopCat.{0}} (e : Hmod2 X 2) :
    cupPowE e 0 = one X := rfl

@[simp] theorem cupPowE_succ {X : TopCat.{0}} (e : Hmod2 X 2) (m : ℕ) :
    cupPowE e (m + 1) = cup (cupPowE e m) e := rfl

/-- Cupping on the right with a fixed degree-2 class, as an additive map
`H^n(X) → H^{n+2}(X)`. -/
def cupRightE {X : TopCat.{0}} (e : Hmod2 X 2) (n : ℕ) : Hmod2 X n →+ Hmod2 X (n + 2) where
  toFun y := cup y e
  map_zero' := zero_cup e
  map_add' a b := cup_add_left a b e

@[simp] theorem cupRightE_apply {X : TopCat.{0}} (e : Hmod2 X 2) (n : ℕ) (y : Hmod2 X n) :
    cupRightE e n y = cup y e := rfl

theorem cupRightE_cupPowE {X : TopCat.{0}} (e : Hmod2 X 2) (m : ℕ) :
    cupRightE e (2 * m) (cupPowE e m) = cupPowE e (m + 1) := rfl

/-- **Cup powers commute with pullback.** -/
theorem pull_cupPowE {X Y : TopCat.{0}} (f : X ⟶ Y) (e : Hmod2 Y 2) (m : ℕ) :
    pull f (2 * m) (cupPowE e m) = cupPowE (pull f 2 e) m := by
  induction m with
  | zero => exact pull_one f
  | succ m ih =>
    show pull f (2 * m + 2) (cup (cupPowE e m) e) = cup (cupPowE (pull f 2 e) m) (pull f 2 e)
    rw [pull_cup, ih]

/-! ## 3. The Gysin sequence -/

/-- **The mod-2 Gysin sequence of a circle bundle `S → X` with Euler class `e`,**
in element form.  `π` is the pullback to the total space and `δ` the connecting
map; the three `exact_*` fields are exactness at `H^*(X)` (kernel of `π` is the
image of `⌣ e`), at `H^*(S)`, and at `H^*(X)` again (kernel of `⌣ e` is the image
of `δ`). -/
structure GysinSequence (X S : TopCat.{0}) (e : Hmod2 X 2) where
  /-- Pullback to the total space of the circle bundle. -/
  π : (n : ℕ) → Hmod2 X n →+ Hmod2 S n
  /-- The connecting map, dropping the degree by one. -/
  δ : (n : ℕ) → Hmod2 S (n + 1) →+ Hmod2 X n
  /-- Exactness at `H^{n+2}(X)`. -/
  exact_X : ∀ (n : ℕ) (x : Hmod2 X (n + 2)),
      π (n + 2) x = 0 ↔ ∃ y : Hmod2 X n, cupRightE e n y = x
  /-- Exactness at `H^{n+1}(S)`. -/
  exact_S : ∀ (n : ℕ) (s : Hmod2 S (n + 1)),
      δ n s = 0 ↔ ∃ x : Hmod2 X (n + 1), π (n + 1) x = s
  /-- Exactness at `H^n(X)`. -/
  exact_ker : ∀ (n : ℕ) (y : Hmod2 X n),
      cupRightE e n y = 0 ↔ ∃ s : Hmod2 S (n + 1), δ n s = y

namespace GysinSequence

variable {X S : TopCat.{0}} {e : Hmod2 X 2}

/-- **Where the sphere bundle is acyclic, cupping with the Euler class is an
isomorphism** `H^n(X) ≅ H^{n+2}(X)`. -/
theorem bijective_cupRight (g : GysinSequence X S e) (n : ℕ)
    (hS1 : ∀ s : Hmod2 S (n + 1), s = 0)
    (hS2 : ∀ s : Hmod2 S (n + 2), s = 0) :
    Function.Bijective (cupRightE e n) := by
  have hzero : ∀ y : Hmod2 X n, cupRightE e n y = 0 → y = 0 := by
    intro y hy
    obtain ⟨s, hs⟩ := (g.exact_ker n y).mp hy
    rw [← hs, hS1 s, map_zero]
  constructor
  · intro a b hab
    have h := hzero (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp h
  · intro x
    exact (g.exact_X n x).mp (hS2 (g.π (n + 2) x))

end GysinSequence

/-! ## 4. The ring of complex projective space -/

/-- **The generator has the expected order.**  If `X` has the cohomology of
`ℂP^N`, and carries a Gysin sequence whose total space has the cohomology of
`S^{2N+1}`, then `h^m ≠ 0` for every `m ≤ N`.

The induction is one application of `bijective_cupRight` per step: the two
vanishing hypotheses hold because `2m+1` and `2m+2` are neither `0` nor `2N+1`
once `m < N`. -/
theorem cupPowE_ne_zero {X S : TopCat.{0}} {e : Hmod2 X 2} (g : GysinSequence X S e)
    (N : ℕ) (hS : HasSphereCohomology S (2 * N + 1))
    (hone : (one X) ≠ 0) {m : ℕ} (hm : m ≤ N) : cupPowE e m ≠ 0 := by
  induction m with
  | zero => simpa using hone
  | succ m ih =>
    have hmN : m < N := by omega
    have hbij := g.bijective_cupRight (2 * m)
      (fun s => hS.2.2 (2 * m + 1) (by omega) (by omega) s)
      (fun s => hS.2.2 (2 * m + 2) (by omega) (by omega) s)
    intro hcontra
    have hzero : cupPowE e m = 0 := by
      refine hbij.1 ?_
      rw [cupRightE_cupPowE, hcontra, map_zero]
    exact ih (by omega) hzero

/-- **The relation.**  `h^m = 0` as soon as `m > N`, because it lives in a group
that has already vanished. -/
theorem cupPowE_eq_zero_of_gt {X : TopCat.{0}} (e : Hmod2 X 2) (N : ℕ)
    (hX : HasCPCohomology X N) {m : ℕ} (hm : N < m) : cupPowE e m = 0 :=
  hX.2 (2 * m) (fun n hn => by omega) _

/-- **The generator is a basis in every even degree it survives.**  Combined with
`cupPowE_ne_zero` this is the statement `H^*(ℂP^N; F₂) = F₂[h]/(h^{N+1})`: each
`H^{2m}` with `m ≤ N` is `{0, h^m}`, and `h^{N+1} = 0`. -/
theorem eq_zero_or_eq_cupPowE {X S : TopCat.{0}} {e : Hmod2 X 2} (g : GysinSequence X S e)
    (N : ℕ) (hX : HasCPCohomology X N) (hS : HasSphereCohomology S (2 * N + 1))
    (hone : (one X) ≠ 0) {m : ℕ} (hm : m ≤ N) (a : Hmod2 X (2 * m)) :
    a = 0 ∨ a = cupPowE e m :=
  eq_zero_or_eq_of_line (hX.1 m hm).some (cupPowE_ne_zero g N hS hone hm) a

end

end CharClass
end GroupApproximation
