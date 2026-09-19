import GroupApproximation.CharClass.CohomologyBasic

/-!
# Associativity and left unitality of the mod-2 cup product

The Alexander–Whitney cup product of `CupProduct.lean` is **strictly**
associative and **strictly** unital at the cochain level; the only friction is
that `p + q + r` and `p + (q + r)` are merely propositionally equal natural
numbers, so the identity has to be transported along a degree cast.  This file
does the transport once, in `cochainCup_assoc`, and descends it to cohomology in
`cup_assoc`.

The mechanism is a relabelling morphism `degHom h : ⦋m⦌ ⟶ ⦋m'⦌` attached to an
equality of degrees `h : m = m'`, its action `simplexRelabel` on singular
simplices, and the evaluation rule `cochainCast_eval` saying that evaluating a
degree-cast cochain is evaluating the original cochain on the relabelled simplex.
Everything then reduces to three identities between morphisms of
`SimplexCategory`, each proved by comparing vertex values.

## Main declarations

* `degHom`, `simplexRelabel`, `cochainCast_eval`.
* `frontFace_comp_frontFace`, `backFace_comp_frontFace`, `backFace_comp_backFace` —
  the three vertex computations.
* `cochainCup_assoc` — strict associativity of `cochainCup`, up to the cast.
* `cup_assoc'`, `one_cup'` — the cohomology statements with the cast on the right.
* `cup_assoc`, `one_cup` — the same with the cast on the left, the form the even
  total ring of `cc-projective` consumes.
* `cohCast_symm_cohCast`, `cohCast_cohCast_symm` — the cast cancellation laws.
-/

open CategoryTheory Simplicial
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.CharClass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 1. Degree relabelling of simplices -/

/-- The relabelling morphism `⦋m⦌ ⟶ ⦋m'⦌` of `SimplexCategory` attached to an
equality of degrees. -/
def degHom {m m' : ℕ} (h : m = m') : (⦋m⦌ : SimplexCategory) ⟶ ⦋m'⦌ :=
  eqToHom (by rw [h])

/-- A degree relabelling preserves vertex values. -/
@[simp] theorem degHom_val {m m' : ℕ} (h : m = m') (x : Fin (m + 1)) :
    (((degHom h).toOrderHom x : Fin (m' + 1)) : ℕ) = (x : ℕ) := by
  rw [degHom, SimplexCategory.eqToHom_toOrderHom]
  rfl

/-- Relabel a singular `m'`-simplex as a singular `m`-simplex along `h : m = m'`. -/
def simplexRelabel (X : TopCat.{0}) {m m' : ℕ} (h : m = m')
    (σ : singularSimplices X m') : singularSimplices X m :=
  (TopCat.toSSet.obj X).map (degHom h).op σ

@[simp] theorem simplexRelabel_rfl (X : TopCat.{0}) {m : ℕ} (σ : singularSimplices X m) :
    simplexRelabel X (rfl : m = m) σ = σ := by
  unfold simplexRelabel degHom
  rw [eqToHom_refl, op_id, Functor.map_id_apply]

/-- Restricting a singular simplex along two composable `SimplexCategory`
morphisms is restricting along the composite. -/
theorem sset_map_comp (X : TopCat.{0}) {a b c : ℕ}
    (f : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌) (g : (⦋b⦌ : SimplexCategory) ⟶ ⦋c⦌)
    (σ : singularSimplices X c) :
    (TopCat.toSSet.obj X).map f.op ((TopCat.toSSet.obj X).map g.op σ)
      = (TopCat.toSSet.obj X).map (f ≫ g).op σ := by
  rw [op_comp, Functor.map_comp_apply]

/-! ## 2. The degree cast on cochains, evaluated -/

@[simp] theorem cochainCast_rfl {R : Type} [CommRing R] {X : TopCat.{0}} {m : ℕ}
    (φ : singularCochainGroup R X m) : cochainCast (rfl : m = m) φ = φ := by
  unfold cochainCast
  rw [eqToHom_refl, Category.id_comp]

/-- **Evaluation of a degree-cast cochain.**  `(cast φ)(σ) = φ(relabel σ)`. -/
theorem cochainCast_eval {R : Type} [CommRing R] {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (φ : singularCochainGroup R X m) (σ : singularSimplices X m') :
    cochainEval m' (cochainCast h φ) σ = cochainEval m φ (simplexRelabel X h σ) := by
  subst h
  rw [cochainCast_rfl, simplexRelabel_rfl]

/-- Compatibility of the degree cast on classes with the degree cast on cochains. -/
theorem cohCast_cocycleClass {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (φ : singularCochainGroup (ZMod 2) X m) (hφ : cochainCoboundary (ZMod 2) X m φ = 0)
    (hφ' : cochainCoboundary (ZMod 2) X m' (cochainCast h φ) = 0) :
    cohCast h (cocycleClass X m φ hφ) = cocycleClass X m' (cochainCast h φ) hφ' := by
  subst h
  rw [cohCast_rfl]
  exact cocycleClass_congr X m (cochainCast_rfl φ).symm hφ hφ'

/-! ## 3. The three vertex computations -/

/-- The front `p`-face of the front `(p+q)`-face is the front `p`-face, after
relabelling `p + (q + r)` as `p + q + r`. -/
theorem frontFace_comp_frontFace (p q r : ℕ) :
    frontFace p q ≫ frontFace (p + q) r
      = frontFace p (q + r) ≫ degHom (Nat.add_assoc p q r).symm := by
  ext x : 3
  apply Fin.ext
  have hL : ((frontFace (p + q) r).toOrderHom ((frontFace p q).toOrderHom x) : ℕ)
      = (x : ℕ) := rfl
  have hR1 : ((degHom (Nat.add_assoc p q r).symm).toOrderHom
        ((frontFace p (q + r)).toOrderHom x) : ℕ)
      = (((frontFace p (q + r)).toOrderHom x : Fin (p + (q + r) + 1)) : ℕ) :=
    degHom_val _ _
  have hR2 : (((frontFace p (q + r)).toOrderHom x : Fin (p + (q + r) + 1)) : ℕ)
      = (x : ℕ) := rfl
  show ((frontFace (p + q) r).toOrderHom ((frontFace p q).toOrderHom x) : ℕ)
      = ((degHom (Nat.add_assoc p q r).symm).toOrderHom
          ((frontFace p (q + r)).toOrderHom x) : ℕ)
  omega

/-- The back `q`-face of the front `(p+q)`-face is the front `q`-face of the back
`(q+r)`-face, after the relabelling. -/
theorem backFace_comp_frontFace (p q r : ℕ) :
    backFace p q ≫ frontFace (p + q) r
      = frontFace q r ≫ backFace p (q + r) ≫ degHom (Nat.add_assoc p q r).symm := by
  ext x : 3
  apply Fin.ext
  have hL : ((frontFace (p + q) r).toOrderHom ((backFace p q).toOrderHom x) : ℕ)
      = (x : ℕ) + p := rfl
  have hR1 : ((degHom (Nat.add_assoc p q r).symm).toOrderHom
        ((backFace p (q + r)).toOrderHom ((frontFace q r).toOrderHom x)) : ℕ)
      = (((backFace p (q + r)).toOrderHom ((frontFace q r).toOrderHom x) :
            Fin (p + (q + r) + 1)) : ℕ) :=
    degHom_val _ _
  have hR2 : (((backFace p (q + r)).toOrderHom ((frontFace q r).toOrderHom x) :
        Fin (p + (q + r) + 1)) : ℕ) = (x : ℕ) + p := rfl
  show ((frontFace (p + q) r).toOrderHom ((backFace p q).toOrderHom x) : ℕ)
      = ((degHom (Nat.add_assoc p q r).symm).toOrderHom
          ((backFace p (q + r)).toOrderHom ((frontFace q r).toOrderHom x)) : ℕ)
  omega

/-- The back `r`-face of a `(p+q)+r`-simplex is the back `r`-face of its back
`(q+r)`-face, after the relabelling. -/
theorem backFace_comp_backFace (p q r : ℕ) :
    backFace (p + q) r
      = backFace q r ≫ backFace p (q + r) ≫ degHom (Nat.add_assoc p q r).symm := by
  ext x : 3
  apply Fin.ext
  have hL : ((backFace (p + q) r).toOrderHom x : ℕ) = (x : ℕ) + (p + q) := rfl
  have hR1 : ((degHom (Nat.add_assoc p q r).symm).toOrderHom
        ((backFace p (q + r)).toOrderHom ((backFace q r).toOrderHom x)) : ℕ)
      = (((backFace p (q + r)).toOrderHom ((backFace q r).toOrderHom x) :
            Fin (p + (q + r) + 1)) : ℕ) :=
    degHom_val _ _
  have hR2 : (((backFace p (q + r)).toOrderHom ((backFace q r).toOrderHom x) :
        Fin (p + (q + r) + 1)) : ℕ) = (x : ℕ) + q + p := rfl
  show ((backFace (p + q) r).toOrderHom x : ℕ)
      = ((degHom (Nat.add_assoc p q r).symm).toOrderHom
          ((backFace p (q + r)).toOrderHom ((backFace q r).toOrderHom x)) : ℕ)
  omega

/-- The back `p`-face at front degree `0` is a pure relabelling. -/
theorem backFace_zero_left (p : ℕ) :
    backFace 0 p = degHom (Nat.zero_add p).symm := by
  ext x : 3
  apply Fin.ext
  have hL : ((backFace 0 p).toOrderHom x : ℕ) = (x : ℕ) := rfl
  have hR : ((degHom (Nat.zero_add p).symm).toOrderHom x : ℕ) = (x : ℕ) :=
    degHom_val _ _
  omega

/-! ## 4. Simplex-level associativity -/

theorem frontSimplex_frontSimplex (X : TopCat.{0}) (p q r : ℕ)
    (σ : singularSimplices X (p + q + r)) :
    frontSimplex X p q (frontSimplex X (p + q) r σ)
      = frontSimplex X p (q + r) (simplexRelabel X (Nat.add_assoc p q r).symm σ) := by
  have h1 : frontSimplex X p q (frontSimplex X (p + q) r σ)
      = (TopCat.toSSet.obj X).map (frontFace p q ≫ frontFace (p + q) r).op σ :=
    sset_map_comp X _ _ σ
  have h2 : frontSimplex X p (q + r) (simplexRelabel X (Nat.add_assoc p q r).symm σ)
      = (TopCat.toSSet.obj X).map
          (frontFace p (q + r) ≫ degHom (Nat.add_assoc p q r).symm).op σ :=
    sset_map_comp X _ _ σ
  rw [h1, h2, frontFace_comp_frontFace]

theorem backSimplex_frontSimplex (X : TopCat.{0}) (p q r : ℕ)
    (σ : singularSimplices X (p + q + r)) :
    backSimplex X p q (frontSimplex X (p + q) r σ)
      = frontSimplex X q r
          (backSimplex X p (q + r) (simplexRelabel X (Nat.add_assoc p q r).symm σ)) := by
  have h1 : backSimplex X p q (frontSimplex X (p + q) r σ)
      = (TopCat.toSSet.obj X).map (backFace p q ≫ frontFace (p + q) r).op σ :=
    sset_map_comp X _ _ σ
  have h2 : backSimplex X p (q + r) (simplexRelabel X (Nat.add_assoc p q r).symm σ)
      = (TopCat.toSSet.obj X).map
          (backFace p (q + r) ≫ degHom (Nat.add_assoc p q r).symm).op σ :=
    sset_map_comp X _ _ σ
  have h3 : frontSimplex X q r
        ((TopCat.toSSet.obj X).map
          (backFace p (q + r) ≫ degHom (Nat.add_assoc p q r).symm).op σ)
      = (TopCat.toSSet.obj X).map
          (frontFace q r ≫ backFace p (q + r) ≫ degHom (Nat.add_assoc p q r).symm).op σ :=
    sset_map_comp X _ _ σ
  rw [h1, h2, h3, backFace_comp_frontFace]

theorem backSimplex_backSimplex (X : TopCat.{0}) (p q r : ℕ)
    (σ : singularSimplices X (p + q + r)) :
    backSimplex X (p + q) r σ
      = backSimplex X q r
          (backSimplex X p (q + r) (simplexRelabel X (Nat.add_assoc p q r).symm σ)) := by
  have h2 : backSimplex X p (q + r) (simplexRelabel X (Nat.add_assoc p q r).symm σ)
      = (TopCat.toSSet.obj X).map
          (backFace p (q + r) ≫ degHom (Nat.add_assoc p q r).symm).op σ :=
    sset_map_comp X _ _ σ
  have h3 : backSimplex X q r
        ((TopCat.toSSet.obj X).map
          (backFace p (q + r) ≫ degHom (Nat.add_assoc p q r).symm).op σ)
      = (TopCat.toSSet.obj X).map
          (backFace q r ≫ backFace p (q + r) ≫ degHom (Nat.add_assoc p q r).symm).op σ :=
    sset_map_comp X _ _ σ
  rw [h2, h3, ← backFace_comp_backFace]
  rfl

theorem backSimplex_zero_left (X : TopCat.{0}) (p : ℕ) (σ : singularSimplices X (0 + p)) :
    backSimplex X 0 p σ = simplexRelabel X (Nat.zero_add p).symm σ := by
  show (TopCat.toSSet.obj X).map (backFace 0 p).op σ = _
  rw [backFace_zero_left]
  rfl

/-! ## 5. Associativity and left unitality -/

/-- Casting along `h` and then back along `h.symm` is the identity. -/
@[simp] theorem cohCast_symm_cohCast {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (a : Hmod2 X m) : cohCast h.symm (cohCast h a) = a := by
  subst h; rfl

/-- Casting along `h.symm` and then back along `h` is the identity. -/
@[simp] theorem cohCast_cohCast_symm {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (a : Hmod2 X m') : cohCast h (cohCast h.symm a) = a := by
  subst h; rfl

/-- **Associativity of the cochain cup product**, up to the degree cast
`p + (q + r) = p + q + r`. -/
theorem cochainCup_assoc {R : Type} [CommRing R] {X : TopCat.{0}} (p q r : ℕ)
    (φ : singularCochainGroup R X p) (ψ : singularCochainGroup R X q)
    (χ : singularCochainGroup R X r) :
    cochainCup (p + q) r (cochainCup p q φ ψ) χ
      = cochainCast (Nat.add_assoc p q r).symm
          (cochainCup p (q + r) φ (cochainCup q r ψ χ)) := by
  apply cochain_ext; intro σ
  simp only [cochainCup_eval, cochainCast_eval]
  rw [mul_assoc, frontSimplex_frontSimplex, backSimplex_frontSimplex, backSimplex_backSimplex]

/-- **Left unitality of the cochain cup product**, up to the degree cast
`p = 0 + p`. -/
theorem cochainCup_one_left {R : Type} [CommRing R] {X : TopCat.{0}} (p : ℕ)
    (φ : singularCochainGroup R X p) :
    cochainCup 0 p (cochainOne (R := R) (Z := X)) φ
      = cochainCast (Nat.zero_add p).symm φ := by
  apply cochain_ext; intro σ
  rw [cochainCup_eval, cochainOne_eval, one_mul, cochainCast_eval, backSimplex_zero_left]

/-- **Associativity of the cup product on cohomology**, with the cast on the right. -/
theorem cup_assoc' {X : TopCat.{0}} {p q r : ℕ}
    (a : Hmod2 X p) (b : Hmod2 X q) (c : Hmod2 X r) :
    cup (cup a b) c = cohCast (Nat.add_assoc p q r).symm (cup a (cup b c)) := by
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycle a
  obtain ⟨ψ, hψ, rfl⟩ := exists_cocycle b
  obtain ⟨χ, hχ, rfl⟩ := exists_cocycle c
  have hcc : cochainCoboundary (ZMod 2) X (p + q + r)
      (cochainCast (Nat.add_assoc p q r).symm
        (cochainCup p (q + r) φ (cochainCup q r ψ χ))) = 0 := by
    rw [← cochainCup_assoc]
    exact cochainCupZMod2_respects_cocycles (p + q) r _ χ
      (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) hχ
  rw [cup_mk, cup_mk, cup_mk, cup_mk,
    cohCast_cocycleClass (Nat.add_assoc p q r).symm _ _ hcc]
  exact cocycleClass_congr X (p + q + r) (cochainCup_assoc p q r φ ψ χ) _ _

/-- **Left unitality on cohomology**, with the cast on the right. -/
theorem one_cup' {X : TopCat.{0}} {p : ℕ} (a : Hmod2 X p) :
    cup (one X) a = cohCast (Nat.zero_add p).symm a := by
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycle a
  have hcc : cochainCoboundary (ZMod 2) X (0 + p)
      (cochainCast (Nat.zero_add p).symm φ) = 0 := by
    rw [← cochainCup_one_left]
    exact cochainCupZMod2_respects_cocycles 0 p _ φ (cochainCoboundary_cochainOne X) hφ
  rw [one_eq_cocycleClass, cup_mk, cohCast_cocycleClass (Nat.zero_add p).symm _ _ hcc]
  exact cocycleClass_congr X (0 + p) (cochainCup_one_left p φ) _ _

/-- **Associativity of the cup product**, with the cast on the left: this is the
form the even total ring of `cc-projective` consumes. -/
theorem cup_assoc {X : TopCat.{0}} {p q r : ℕ}
    (a : Hmod2 X p) (b : Hmod2 X q) (c : Hmod2 X r) :
    cohCast (Nat.add_assoc p q r) (cup (cup a b) c) = cup a (cup b c) := by
  rw [cup_assoc', cohCast_cohCast_symm]

/-- **Left unitality**, with the cast on the left. -/
theorem one_cup {X : TopCat.{0}} {p : ℕ} (a : Hmod2 X p) :
    cohCast (Nat.zero_add p) (cup (one X) a) = a := by
  rw [one_cup', cohCast_cohCast_symm]

end

end GroupApproximation.CharClass
