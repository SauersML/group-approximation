import GroupApproximation.CharClass.ThomFreeModule

/-!
# The Thom class in Leray–Hirsch coordinates, degreewise

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypotheses 6 and 7).

`CharClass/ThomFreeModule.lean` computes the Thom class from a `Module.Basis`,
which is the **ring** view of Leray–Hirsch: `H^*(P)` free over the total
cohomology ring of the base on `1, ξ, …, ξ^{r}`.  `cc-projective`'s
`LerayHirschGraded` is instead **degreewise**: at each `n`, the map

```text
(aᵢ)_{i<r}  ↦  ∑ᵢ π^*(aᵢ) ⌣ ξ^i,        aᵢ ∈ H^{n-2i}(X)
```

is a bijection onto `H^n(P)`.  At `n = 2r` every summand survives, so the two
projectivisations are presented as *products of different groups*

```text
H^{2r}(P(E⊕1)) ≅ ∏_{i ≤ r} H^{2r-2i}(X),      H^{2r}(P(E)) ≅ ∏_{i < r} H^{2r-2i}(X),
```

and there is no single coefficient ring in sight.  This file redoes the Thom-class
linear algebra in that setting.

## What the restriction looks like in coordinates

`ξ₁` restricts to `ξ₂`, so the first `r` coordinates are carried across
unchanged, while the Chern relation rewrites the last one:

```text
ρ (a₀, …, a_r) = (a₀ + g₀ a_r, …, a_{r-1} + g_{r-1} a_r),      gᵢ = (γ_{r-i} ⌣ ·).
```

The `gᵢ` are *linear maps between different groups*, not scalars — that is the
one structural difference from the ring view, and the reason `Module.Basis` does
not apply.  Everything else goes through: the kernel is free of rank one on the
Thom generator, parametrised by the last coordinate, so the relative group of the
pair is `H^0(X)`.

Nothing here is topology.  The topological inputs — the two Leray–Hirsch
bijections, `ξ₁ ↦ ξ₂`, and the Chern relation — are what produce `g`; they are
`cc-projective`'s, and `ThomChernBasis.genPow_dim_eq_neg_basisSum` is the
relation in the form they need.

## Main declarations

* `ThomDeg.restrictMap` — the restriction in coordinates.
* `ThomDeg.thomLift` — the Thom generator, parametrised by the last coordinate.
* `ThomDeg.ker_restrictMap` — **the kernel is exactly the Thom line**.
* `ThomDeg.thomEquiv` — the relative group of the pair is `H^0(X)`: §1.4 item 5.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

namespace ThomDeg

variable {R : Type} [CommRing R] {r : ℕ} {M : Fin (r + 1) → Type}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-! ## 1. The restriction in coordinates -/

variable (g : ∀ i : Fin r, M (Fin.last r) →ₗ[R] M i.castSucc)

/-- **The restriction of a Leray–Hirsch presentation, in coordinates.**  The first
`r` coefficients survive, and the last is folded into them by the Chern relation. -/
def restrictMap : (∀ i, M i) →ₗ[R] (∀ i : Fin r, M i.castSucc) where
  toFun a := fun i => a i.castSucc + g i (a (Fin.last r))
  map_add' a b := by
    funext i
    show (a i.castSucc + b i.castSucc) + g i (a (Fin.last r) + b (Fin.last r))
      = (a i.castSucc + g i (a (Fin.last r))) + (b i.castSucc + g i (b (Fin.last r)))
    rw [map_add]
    exact add_add_add_comm _ _ _ _
  map_smul' c a := by
    funext i
    show c • a i.castSucc + g i (c • a (Fin.last r))
      = c • (a i.castSucc + g i (a (Fin.last r)))
    rw [map_smul, smul_add]

@[simp] theorem restrictMap_apply (a : ∀ i, M i) (i : Fin r) :
    restrictMap g a i = a i.castSucc + g i (a (Fin.last r)) := rfl

/-! ## 2. The Thom generator -/

/-- **The Thom generator**, as a function of its last coordinate: the unique
element of the kernel whose top coefficient is the given one. -/
def thomLift : M (Fin.last r) →ₗ[R] (∀ i, M i) where
  toFun x := Fin.snoc (fun i : Fin r => -g i x) x
  map_add' x y := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · show Fin.snoc _ (x + y) (Fin.last r) = _
      rw [Fin.snoc_last]
      show x + y = Fin.snoc _ x (Fin.last r) + Fin.snoc _ y (Fin.last r)
      rw [Fin.snoc_last, Fin.snoc_last]
    · intro j
      show Fin.snoc _ (x + y) j.castSucc = _
      rw [Fin.snoc_castSucc]
      show -g j (x + y) = Fin.snoc _ x j.castSucc + Fin.snoc _ y j.castSucc
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc, map_add, neg_add]
  map_smul' c x := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · show Fin.snoc _ (c • x) (Fin.last r) = _
      rw [Fin.snoc_last]
      show c • x = c • Fin.snoc _ x (Fin.last r)
      rw [Fin.snoc_last]
    · intro j
      show Fin.snoc _ (c • x) j.castSucc = _
      rw [Fin.snoc_castSucc]
      show -g j (c • x) = c • Fin.snoc _ x j.castSucc
      rw [Fin.snoc_castSucc, map_smul, smul_neg]

@[simp] theorem thomLift_last (x : M (Fin.last r)) :
    thomLift g x (Fin.last r) = x := by
  show Fin.snoc (fun i : Fin r => -g i x) x (Fin.last r) = x
  exact Fin.snoc_last _ _

@[simp] theorem thomLift_castSucc (x : M (Fin.last r)) (i : Fin r) :
    thomLift g x i.castSucc = -g i x := by
  show Fin.snoc (fun j : Fin r => -g j x) x i.castSucc = -g i x
  exact Fin.snoc_castSucc _ _ _

/-! ## 3. The kernel is exactly the Thom line -/

/-- The Thom generator restricts to zero. -/
theorem restrict_thomLift (x : M (Fin.last r)) : restrictMap g (thomLift g x) = 0 := by
  funext i
  rw [restrictMap_apply, thomLift_castSucc, thomLift_last]
  exact neg_add_cancel _

/-- Distinct top coefficients give distinct Thom generators. -/
theorem thomLift_injective : Function.Injective (thomLift g) := by
  intro x y h
  have := congrFun h (Fin.last r)
  rwa [thomLift_last, thomLift_last] at this

/-- **The kernel of the restriction is exactly the Thom line.**  This is the
degreewise form of `ker_eq_span_thomGenerator`: it says the relative group of the
pair is free of rank one on the Thom class, with the top Leray–Hirsch coefficient
as the parameter. -/
theorem ker_restrictMap :
    LinearMap.ker (restrictMap g) = LinearMap.range (thomLift g) := by
  apply le_antisymm
  · intro a ha
    refine ⟨a (Fin.last r), ?_⟩
    funext i
    refine Fin.lastCases ?_ ?_ i
    · rw [thomLift_last]
    · intro j
      rw [thomLift_castSucc]
      have hj := congrFun ha j
      rw [restrictMap_apply] at hj
      have hj0 : a j.castSucc + g j (a (Fin.last r)) = 0 := hj
      rw [← neg_eq_of_add_eq_zero_left hj0]
  · rintro a ⟨x, rfl⟩
    exact restrict_thomLift g x

/-- The kernel, as a copy of the top coefficient group. -/
noncomputable def kerEquiv :
    M (Fin.last r) ≃ₗ[R] LinearMap.ker (restrictMap g) :=
  (LinearEquiv.ofInjective (thomLift g) (thomLift_injective g)).trans
    (LinearEquiv.ofEq _ _ (ker_restrictMap g).symm)

/-! ## 4. The relative group of the pair -/

/-- **`H^{2r}(P(E⊕1), P(E⊕1) ∖ Z) ≅ H^0(X)`**, degreewise.  `jm` is the map from
the relative group with `hinj` its injectivity and `hrange` exactness at the
absolute group, both `cc-relative`'s; the conclusion is §1.4 item 5 at `k = 0`. -/
noncomputable def thomEquiv {P : Type} [AddCommGroup P] [Module R P]
    (jm : P →ₗ[R] (∀ i, M i)) (hinj : Function.Injective jm)
    (hrange : LinearMap.range jm = LinearMap.ker (restrictMap g)) :
    P ≃ₗ[R] M (Fin.last r) :=
  ((LinearEquiv.ofInjective jm hinj).trans
      (LinearEquiv.ofEq _ _ hrange)).trans (kerEquiv g).symm

/-- Every class of the pair has a unique top Leray–Hirsch coefficient. -/
theorem existsUnique_thomLift {P : Type} [AddCommGroup P] [Module R P]
    (jm : P →ₗ[R] (∀ i, M i))
    (hrange : LinearMap.range jm = LinearMap.ker (restrictMap g)) (z : P) :
    ∃! x : M (Fin.last r), jm z = thomLift g x := by
  have hmem : jm z ∈ LinearMap.ker (restrictMap g) := by
    rw [← hrange]
    exact ⟨z, rfl⟩
  rw [ker_restrictMap] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, hx.symm, fun y hy => ?_⟩
  exact thomLift_injective g (by rw [← hy, hx])

end ThomDeg

end GroupApproximation.CharClass
