import GroupApproximation.CharClass.ProjectiveSpaceCohomology
import GroupApproximation.CharClass.CoeffLine

/-!
# `H^*(ℂP^n; K) = K[h]/(h^{n+1})`

Knowing the graded modules (`CharClass/ProjectiveSpaceCohomology.lean`) leaves
exactly one thing to prove about the ring: that the degree-2 generator `h` has
`h^n ≠ 0`.  Everything else is formal — each `H^{2m}` is one-dimensional, so a
nonzero element spans it, and `h^{n+1}` lies in `H^{2n+2} = 0`.

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

## The coefficient parameter, and the one place characteristic two was used

Cup powers, the Gysin sequence and `cupPowE_ne_zero` are generic in a commutative
ring `K`; the coefficient is implicit throughout, because the Euler class
`e : Hmod K X 2` determines it, so every `F₂` call site is byte-unchanged.

The characteristic-two step was **"a one-dimensional `F₂`-space has exactly two
elements"**, which turned `H^{2m} ≅ K` into the sharp statement `a = 0 ∨ a = h^m`.
Over `K` the sharp statement is `a = c • h^m` for a scalar `c`
(`exists_smul_cupPowE`), and for `a ≠ 0` the scalar is nonzero — `sp-coeff`'s
`CoeffLine`, which is what this file imports for it.  That import also **retires
this file's `lineGen`**: `CoeffLine.lineGen` is the same declaration
(`e.symm 1`) in the same namespace, written independently, and only the fact that
`CoeffLine` was a leaf kept the two from clashing.  The `F₂`-only consequences
that `CoeffLine` does not carry — that a line over `F₂` has a *unique* nonzero
element, so `lineGen` needs no choice — stay here.

## Main declarations

* `cupPowE e m : H^{2m}(X)` — the `m`-th cup power of a degree-2 class.  It needs
  no degree transport: `2 * (m+1)` and `2 * m + 2` are definitionally equal.
* `GysinSequence` — the sequence, in element form.
* `GysinSequence.bijective_cupRight` — `⌣ e` is bijective where the sphere vanishes.
* `cupPowE_ne_zero` — `h^m ≠ 0` for `m ≤ n`: the ring generator has the expected order.
* `cupPowE_eq_zero_of_gt` — `h^{n+1} = 0`.
* `exists_smul_cupPowE` — `h^m` spans `H^{2m}` over a field `K`;
  `eq_zero_or_eq_cupPowE` is its `F₂` sharpening.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

/-! ## 1. Lines over `F₂`

The general-coefficient statements are `CoeffLine.exists_smul_of_line` and
`CoeffLine.exists_ne_zero_smul_of_line`.  What survives only at `F₂` is that the
nonzero element is *unique*, which is what makes `lineGen` canonical. -/

/-- A one-dimensional `F₂`-vector space has exactly two elements, so any nonzero
element is a basis in the crudest possible sense.  **Special to `F₂`**; over a
field the statement is `CoeffLine.exists_smul_of_line`. -/
theorem eq_zero_or_eq_of_line {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] ZMod 2) {x : M} (hx : x ≠ 0) (a : M) : a = 0 ∨ a = x := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · exact Or.inr (eq_of_line_of_ne_zero_zmod2 e hx ha)

/-- **Any two constructions of the generator of a line over `F₂` agree**, because
the nonzero element is unique.  This is the `F₂` sharpening of
`CoeffLine.exists_ne_zero_smul_lineGen`. -/
theorem eq_lineGen_of_ne_zero {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] ZMod 2) {x : M} (hx : x ≠ 0) : x = lineGen e :=
  (eq_zero_or_eq_of_line e (lineGen_ne_zero e) x).resolve_left hx

/-- Two presentations of the same line have the same generator. -/
theorem lineGen_eq {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (e e' : M ≃ₗ[ZMod 2] ZMod 2) : lineGen e = lineGen e' :=
  eq_lineGen_of_ne_zero e' (lineGen_ne_zero e)

/-! ## 2. Cup powers of a degree-two class -/

section CupPow

variable {K : Type} [CommRing K] {X Y : TopCat.{0}}

/-- The `m`-th cup power of a degree-2 class.  No degree transport appears:
`Nat.mul` recurses on its second argument, so `2 * (m + 1)` reduces to `2 * m + 2`,
and `2 * 0` reduces to `0`. -/
def cupPowE (e : Hmod K X 2) : (m : ℕ) → Hmod K X (2 * m)
  | 0 => one X
  | (m + 1) => cup (cupPowE e m) e

@[simp] theorem cupPowE_zero (e : Hmod K X 2) : cupPowE e 0 = one X := rfl

@[simp] theorem cupPowE_succ (e : Hmod K X 2) (m : ℕ) :
    cupPowE e (m + 1) = cup (cupPowE e m) e := rfl

/-- Cupping on the right with a fixed degree-2 class, as an additive map
`H^n(X) → H^{n+2}(X)`. -/
def cupRightE (e : Hmod K X 2) (n : ℕ) : Hmod K X n →+ Hmod K X (n + 2) where
  toFun y := cup y e
  map_zero' := zero_cup e
  map_add' a b := cup_add_left a b e

@[simp] theorem cupRightE_apply (e : Hmod K X 2) (n : ℕ) (y : Hmod K X n) :
    cupRightE e n y = cup y e := rfl

theorem cupRightE_cupPowE (e : Hmod K X 2) (m : ℕ) :
    cupRightE e (2 * m) (cupPowE e m) = cupPowE e (m + 1) := rfl

/-- **Cup powers commute with pullback.** -/
theorem pull_cupPowE (f : X ⟶ Y) (e : Hmod K Y 2) (m : ℕ) :
    pull f (2 * m) (cupPowE e m) = cupPowE (pull f 2 e) m := by
  induction m with
  | zero => exact pull_one f
  | succ m ih =>
    show pull f (2 * m + 2) (cup (cupPowE e m) e) = cup (cupPowE (pull f 2 e) m) (pull f 2 e)
    rw [pull_cup, ih]

end CupPow

/-! ## 3. The Gysin sequence -/

/-- **The Gysin sequence of a circle bundle `S → X` with Euler class `e`,** in
element form.  `π` is the pullback to the total space and `δ` the connecting map;
the three `exact_*` fields are exactness at `H^*(X)` (kernel of `π` is the image
of `⌣ e`), at `H^*(S)`, and at `H^*(X)` again (kernel of `⌣ e` is the image of
`δ`).  The coefficient is implicit: `e` determines it. -/
structure GysinSequence {K : Type} [CommRing K] (X S : TopCat.{0}) (e : Hmod K X 2) where
  /-- Pullback to the total space of the circle bundle. -/
  π : (n : ℕ) → Hmod K X n →+ Hmod K S n
  /-- The connecting map, dropping the degree by one. -/
  δ : (n : ℕ) → Hmod K S (n + 1) →+ Hmod K X n
  /-- Exactness at `H^{n+2}(X)`. -/
  exact_X : ∀ (n : ℕ) (x : Hmod K X (n + 2)),
      π (n + 2) x = 0 ↔ ∃ y : Hmod K X n, cupRightE e n y = x
  /-- Exactness at `H^{n+1}(S)`. -/
  exact_S : ∀ (n : ℕ) (s : Hmod K S (n + 1)),
      δ n s = 0 ↔ ∃ x : Hmod K X (n + 1), π (n + 1) x = s
  /-- Exactness at `H^n(X)`. -/
  exact_ker : ∀ (n : ℕ) (y : Hmod K X n),
      cupRightE e n y = 0 ↔ ∃ s : Hmod K S (n + 1), δ n s = y

namespace GysinSequence

variable {K : Type} [CommRing K] {X S : TopCat.{0}} {e : Hmod K X 2}

/-- **Where the sphere bundle is acyclic, cupping with the Euler class is an
isomorphism** `H^n(X) ≅ H^{n+2}(X)`. -/
theorem bijective_cupRight (g : GysinSequence X S e) (n : ℕ)
    (hS1 : ∀ s : Hmod K S (n + 1), s = 0)
    (hS2 : ∀ s : Hmod K S (n + 2), s = 0) :
    Function.Bijective (cupRightE e n) := by
  have hzero : ∀ y : Hmod K X n, cupRightE e n y = 0 → y = 0 := by
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

section Ring

variable {K : Type} [CommRing K] {X S : TopCat.{0}}

/-- **The generator has the expected order.**  If `X` has the cohomology of
`ℂP^N`, and carries a Gysin sequence whose total space has the cohomology of
`S^{2N+1}`, then `h^m ≠ 0` for every `m ≤ N`.

The induction is one application of `bijective_cupRight` per step: the two
vanishing hypotheses hold because `2m+1` and `2m+2` are neither `0` nor `2N+1`
once `m < N`. -/
theorem cupPowE_ne_zero {e : Hmod K X 2} (g : GysinSequence X S e)
    (N : ℕ) (hS : HasSphereCohomologyOf K S (2 * N + 1))
    (hone : (one X : Hmod K X 0) ≠ 0) {m : ℕ} (hm : m ≤ N) : cupPowE e m ≠ 0 := by
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
theorem cupPowE_eq_zero_of_gt (e : Hmod K X 2) (N : ℕ)
    (hX : HasCPCohomologyOf K X N) {m : ℕ} (hm : N < m) : cupPowE e m = 0 :=
  hX.2 (2 * m) (fun n hn => by omega) _

end Ring

section RingField

variable {K : Type} [Field K] {X S : TopCat.{0}}

/-- **The generator spans every even group it survives in.**  Combined with
`cupPowE_ne_zero` this is the statement `H^*(ℂP^N; K) = K[h]/(h^{N+1})`: each
`H^{2m}` with `m ≤ N` is `K · h^m`, and `h^{N+1} = 0`.

Over `F₂` the scalar is forced to `1` and this sharpens to
`eq_zero_or_eq_cupPowE`; over a general field a scalar is all one can ask, and it
is all the tree ever uses, because every consumer is proving something nonzero. -/
theorem exists_smul_cupPowE {e : Hmod K X 2} (g : GysinSequence X S e)
    (N : ℕ) (hX : HasCPCohomologyOf K X N) (hS : HasSphereCohomologyOf K S (2 * N + 1))
    (hone : (one X : Hmod K X 0) ≠ 0) {m : ℕ} (hm : m ≤ N) (a : Hmod K X (2 * m)) :
    ∃ c : K, a = c • cupPowE e m :=
  exists_smul_of_line (hX.1 m hm).some (cupPowE_ne_zero g N hS hone hm) a

/-- And the scalar is nonzero exactly when the class is. -/
theorem exists_ne_zero_smul_cupPowE {e : Hmod K X 2} (g : GysinSequence X S e)
    (N : ℕ) (hX : HasCPCohomologyOf K X N) (hS : HasSphereCohomologyOf K S (2 * N + 1))
    (hone : (one X : Hmod K X 0) ≠ 0) {m : ℕ} (hm : m ≤ N) {a : Hmod K X (2 * m)}
    (ha : a ≠ 0) : ∃ c : K, c ≠ 0 ∧ a = c • cupPowE e m :=
  exists_ne_zero_smul_of_line (hX.1 m hm).some (cupPowE_ne_zero g N hS hone hm) ha

end RingField

/-- **The `F₂` sharpening**: each `H^{2m}` with `m ≤ N` is `{0, h^m}`. -/
theorem eq_zero_or_eq_cupPowE {X S : TopCat.{0}} {e : Hmod2 X 2} (g : GysinSequence X S e)
    (N : ℕ) (hX : HasCPCohomology X N) (hS : HasSphereCohomology S (2 * N + 1))
    (hone : (one X : Hmod2 X 0) ≠ 0) {m : ℕ} (hm : m ≤ N) (a : Hmod2 X (2 * m)) :
    a = 0 ∨ a = cupPowE e m :=
  eq_zero_or_eq_of_line (hX.1 m hm).some (cupPowE_ne_zero g N hS hone hm) a

end

end CharClass
end GroupApproximation
