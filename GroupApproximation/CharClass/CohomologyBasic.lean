import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CohomologyCupProduct

/-!
# Element-level mod-2 singular cohomology: the graded module and the cup product

This is the base layer of the `GroupApproximation.CharClass` topology stack.  It
repackages the vendored mod-2 singular cohomology of
`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/`
as an *element-level* graded ring API: cup product, unit, pullback, and the
laws relating them, all phrased about elements `a : Hmod2 X n` rather than about
`ModuleCat` morphisms or cochain complexes.

Every peer lane of the LIX program builds on the names exported here, so they are
deliberately short and deliberately stable.

## Main declarations

* `Hmod2 X n` — `H^n(X; F₂)`, an object of `ModuleCat (ZMod 2)`.
* `cohCast h a` — transport along an equality of degrees `h : m = m'`.
* `cup a b`, notation `a ⌣ b` — the cup product `H^p → H^q → H^{p+q}`.
* `cup_mk` — the cup of the classes of two cocycles is the class of the cochain cup.
* `cup_add_left`, `cup_add_right`, `cup_smul_left`, `cup_smul_right`, `cupBilin` —
  bilinearity.
* `one X` — the unit `1 ∈ H^0(X; F₂)`; `cup_one` is strict right unitality.
* `pull f n` — the pullback `f^* : H^n(Y) → H^n(X)` of `f : X ⟶ Y`, with
  `pull_id`, `pull_comp`, `pull_cup`, `pull_one`, `pull_mk`.

Associativity, left unitality and the degree-cast calculus live in
`CohomologyAssoc.lean`; graded commutativity is **not** provided here (see the
module footer).
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 1. The graded module `H^*(X; F₂)` -/

/-- `H^n(X; F₂)`, the `n`-th mod-2 singular cohomology of the space `X`, as an
object of `ModuleCat (ZMod 2)`.  This is definitionally the `n`-th homology of
the vendored singular `F₂`-cochain complex of `X`. -/
abbrev Hmod2 (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} (ZMod 2) :=
  cohomologyZMod2 X n

/-- Every class is the class of a cocycle. -/
theorem exists_cocycle {X : TopCat.{0}} {n : ℕ} (a : Hmod2 X n) :
    ∃ (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0),
      cocycleClass X n φ hφ = a :=
  cocycleClass_surjective X n a

/-! ## 2. Degree casts

`p + q + r` and `p + (q + r)` are only propositionally equal, so a graded API over
`ℕ`-indexed groups needs a transport.  `cohCast` is that transport; it is a plain
`Eq.rec` in the degree, which makes `subst` the universal proof method for its
laws. -/

/-- Transport a cohomology class along an equality of degrees. -/
def cohCast {X : TopCat.{0}} {m m' : ℕ} (h : m = m') (a : Hmod2 X m) : Hmod2 X m' :=
  h ▸ a

@[simp] theorem cohCast_rfl {X : TopCat.{0}} {m : ℕ} (a : Hmod2 X m) :
    cohCast (rfl : m = m) a = a := rfl

@[simp] theorem cohCast_cohCast {X : TopCat.{0}} {m₁ m₂ m₃ : ℕ} (h : m₁ = m₂) (h' : m₂ = m₃)
    (a : Hmod2 X m₁) : cohCast h' (cohCast h a) = cohCast (h.trans h') a := by
  subst h; subst h'; rfl

@[simp] theorem cohCast_add {X : TopCat.{0}} {m m' : ℕ} (h : m = m') (a b : Hmod2 X m) :
    cohCast h (a + b) = cohCast h a + cohCast h b := by
  subst h; rfl

@[simp] theorem cohCast_zero {X : TopCat.{0}} {m m' : ℕ} (h : m = m') :
    cohCast h (0 : Hmod2 X m) = 0 := by
  subst h; rfl

@[simp] theorem cohCast_smul {X : TopCat.{0}} {m m' : ℕ} (h : m = m') (s : ZMod 2)
    (a : Hmod2 X m) : cohCast h (s • a) = s • cohCast h a := by
  subst h; rfl

theorem cohCast_injective {X : TopCat.{0}} {m m' : ℕ} (h : m = m') :
    Function.Injective (cohCast (X := X) h) := by
  subst h; exact fun _ _ hab => hab

@[simp] theorem cohCast_eq_zero_iff {X : TopCat.{0}} {m m' : ℕ} (h : m = m') (a : Hmod2 X m) :
    cohCast h a = 0 ↔ a = 0 := by
  subst h; exact Iff.rfl

theorem cohCast_eq_iff {X : TopCat.{0}} {m m' : ℕ} (h : m = m') (a : Hmod2 X m)
    (b : Hmod2 X m') : cohCast h a = b ↔ a = cohCast h.symm b := by
  subst h; exact Iff.rfl

/-! ## 3. The cup product -/

/-- The mod-2 cup product `H^p(X; F₂) → H^q(X; F₂) → H^{p+q}(X; F₂)`. -/
def cup {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) : Hmod2 X (p + q) :=
  cupZMod2 a b

@[inherit_doc cup] scoped infixl:70 " ⌣ " => cup

/-- **Computation rule.**  The cup product of the classes of two cocycles is the
class of their Alexander–Whitney cochain cup. -/
theorem cup_mk {X : TopCat.{0}} {p q : ℕ}
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cup (cocycleClass X p φ hφ) (cocycleClass X q ψ hψ)
      = cocycleClass X (p + q) (cochainCup p q φ ψ)
          (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) :=
  cupZMod2_mk φ hφ ψ hψ

/-- Cupping on the right with a fixed class is the descended cochain map
`cupHomologyLeft`; this is the definition, recorded for `map_add`/`map_smul`. -/
theorem cup_eq_cupHomologyLeft {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) :
    cup a b = (cupHomologyLeft X p q (classRepr X q b) (classRepr_isCocycle X q b)).hom a :=
  rfl

/-- Cupping on the left with a fixed class is the descended cochain map
`cupHomologyRight`. -/
theorem cup_eq_cupHomologyRight {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) :
    cup a b = (cupHomologyRight X p q (classRepr X p a) (classRepr_isCocycle X p a)).hom b := by
  obtain ⟨ψ, hψ, rfl⟩ := exists_cocycle b
  rw [cupHomologyRight_apply]
  conv_lhs => rw [← cocycleClass_classRepr X p a]
  rw [cup_mk]

theorem cup_add_left {X : TopCat.{0}} {p q : ℕ} (a a' : Hmod2 X p) (b : Hmod2 X q) :
    cup (a + a') b = cup a b + cup a' b := by
  rw [cup_eq_cupHomologyLeft, cup_eq_cupHomologyLeft a b, cup_eq_cupHomologyLeft a' b, map_add]

theorem cup_add_right {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b b' : Hmod2 X q) :
    cup a (b + b') = cup a b + cup a b' := by
  rw [cup_eq_cupHomologyRight, cup_eq_cupHomologyRight a b, cup_eq_cupHomologyRight a b', map_add]

theorem cup_smul_left {X : TopCat.{0}} {p q : ℕ} (s : ZMod 2) (a : Hmod2 X p) (b : Hmod2 X q) :
    cup (s • a) b = s • cup a b := by
  rw [cup_eq_cupHomologyLeft, cup_eq_cupHomologyLeft a b, map_smul]

theorem cup_smul_right {X : TopCat.{0}} {p q : ℕ} (s : ZMod 2) (a : Hmod2 X p) (b : Hmod2 X q) :
    cup a (s • b) = s • cup a b := by
  rw [cup_eq_cupHomologyRight, cup_eq_cupHomologyRight a b, map_smul]

@[simp] theorem zero_cup {X : TopCat.{0}} {p q : ℕ} (b : Hmod2 X q) :
    cup (0 : Hmod2 X p) b = 0 := by
  rw [cup_eq_cupHomologyLeft, map_zero]

@[simp] theorem cup_zero {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) :
    cup a (0 : Hmod2 X q) = 0 := by
  rw [cup_eq_cupHomologyRight, map_zero]

/-- The cup product as an `F₂`-bilinear map. -/
def cupBilin (X : TopCat.{0}) (p q : ℕ) :
    Hmod2 X p →ₗ[ZMod 2] Hmod2 X q →ₗ[ZMod 2] Hmod2 X (p + q) where
  toFun a :=
    { toFun := fun b => cup a b
      map_add' := cup_add_right a
      map_smul' := fun s b => cup_smul_right s a b }
  map_add' a a' := by
    ext b
    exact cup_add_left a a' b
  map_smul' s a := by
    ext b
    exact cup_smul_left s a b

@[simp] theorem cupBilin_apply {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) :
    cupBilin X p q a b = cup a b := rfl

/-! ## 4. The unit -/

/-- The unit class `1 ∈ H^0(X; F₂)`. -/
def one (X : TopCat.{0}) : Hmod2 X 0 := oneZMod2 X

theorem one_eq_cocycleClass (X : TopCat.{0}) :
    one X = cocycleClass X 0 (cochainOne (R := ZMod 2) (Z := X))
      (cochainCoboundary_cochainOne X) := rfl

/-- **Strict right unitality.**  `a ⌣ 1 = a`; no degree cast is needed because
`p + 0` reduces to `p`. -/
@[simp] theorem cup_one {X : TopCat.{0}} {p : ℕ} (a : Hmod2 X p) : cup a (one X) = a := by
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycle a
  rw [one_eq_cocycleClass, cup_mk]
  exact cocycleClass_congr X (p + 0) (cochainCup_one p φ) _ _

/-! ## 5. Pullback -/

/-- The pullback `f^* : H^n(Y; F₂) → H^n(X; F₂)` along `f : X ⟶ Y`. -/
def pull {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : Hmod2 Y n) : Hmod2 X n :=
  (cohPullback f n).hom a

theorem pull_eq_cohPullback {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : Hmod2 Y n) :
    pull f n a = (cohPullback f n).hom a := rfl

@[simp] theorem pull_add {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a b : Hmod2 Y n) :
    pull f n (a + b) = pull f n a + pull f n b :=
  map_add _ _ _

@[simp] theorem pull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    pull f n (0 : Hmod2 Y n) = 0 :=
  map_zero _

theorem pull_smul {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (s : ZMod 2) (a : Hmod2 Y n) :
    pull f n (s • a) = s • pull f n a :=
  map_smul _ _ _

/-- The pullback of a class along `f`, as an `F₂`-linear map. -/
def pullLinear {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) : Hmod2 Y n →ₗ[ZMod 2] Hmod2 X n :=
  (cohPullback f n).hom

@[simp] theorem pullLinear_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : Hmod2 Y n) :
    pullLinear f n a = pull f n a := rfl

@[simp] theorem pull_id {X : TopCat.{0}} (n : ℕ) (a : Hmod2 X n) : pull (𝟙 X) n a = a := by
  show ((singularCohomologyZMod2 n).map (𝟙 X).op).hom a = a
  rw [CategoryTheory.op_id, (singularCohomologyZMod2 n).map_id]
  rfl

theorem pull_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (a : Hmod2 Z n) :
    pull (f ≫ g) n a = pull f n (pull g n a) := by
  show ((singularCohomologyZMod2 n).map (f ≫ g).op).hom a = _
  rw [CategoryTheory.op_comp, (singularCohomologyZMod2 n).map_comp]
  rfl

theorem pull_congr {X Y : TopCat.{0}} {f g : X ⟶ Y} (h : f = g) (n : ℕ) (a : Hmod2 Y n) :
    pull f n a = pull g n a := by rw [h]

/-- **Computation rule for the pullback.**  The pullback of the class of a cocycle
is the class of the pullback cochain. -/
theorem pull_mk {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) (hφ : cochainCoboundary (ZMod 2) Y n φ = 0) :
    pull f n (cocycleClass Y n φ hφ)
      = cocycleClass X n (cochainPullback f n φ) (cochainPullback_cocycle f n φ hφ) :=
  cohPullback_cocycleClass f n φ hφ

/-- **Naturality of the cup product.**  `f^*(a ⌣ b) = f^* a ⌣ f^* b`. -/
theorem pull_cup {X Y : TopCat.{0}} (f : X ⟶ Y) {p q : ℕ} (a : Hmod2 Y p) (b : Hmod2 Y q) :
    pull f (p + q) (cup a b) = cup (pull f p a) (pull f q b) :=
  cohPullback_cupZMod2 f p q a b

/-- The pullback preserves the unit. -/
@[simp] theorem pull_one {X Y : TopCat.{0}} (f : X ⟶ Y) : pull f 0 (one Y) = one X := by
  rw [one_eq_cocycleClass, pull_mk]
  refine cocycleClass_congr X 0 ?_ _ _
  apply cochain_ext; intro σ
  rw [cochainPullback_eval, cochainOne_eval, cochainOne_eval]

end

end GroupApproximation.CharClass

/-!
## Not provided here

**Graded commutativity** `a ⌣ b = b ⌣ a` (mod 2).  The Alexander–Whitney cochain
cup product is *not* commutative on the nose, and the vendored tree carries no
chain homotopy between the AW diagonal and its transpose.  The homotopy is the
standard consequence of the (ℤ/2-equivariant) acyclic-models theorem, which is
lane `cc-cartan`'s deliverable; until it lands, downstream lemmas must be stated
for classes pulled back from different factors of a product, where the
commutation is a formal consequence of naturality rather than of a chain
homotopy.
-/
