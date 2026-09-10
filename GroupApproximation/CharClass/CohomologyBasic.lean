import GroupApproximation.CharClass.CoeffCohomology

/-!
# Element-level singular cohomology: the graded module and the cup product

This is the base layer of the `GroupApproximation.CharClass` topology stack.  It
repackages the vendored singular cohomology of
`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/`,
made generic in the coefficient ring by `CharClass/CoeffLeibniz.lean` and
`CharClass/CoeffCohomology.lean`, as an *element-level* graded ring API: cup
product, unit, pullback, and the laws relating them, all phrased about elements
`a : Hmod K X n` rather than about `ModuleCat` morphisms or cochain complexes.

Every peer lane of the LIX program builds on the names exported here, so they are
deliberately short and deliberately stable.

## The coefficient parameter

The graded module is `Hmod K X n = H^n(X; K)` for a commutative ring `K`, and
`Hmod2 X n = Hmod (ZMod 2) X n` is the `F₂` instance — an `abbrev`, hence
reducibly the object the vendored layer calls `cohomologyZMod2 X n`.  In
`cup`, `pull`, `cohCast`, `one`, `cupBilin` and `pullLinear` the coefficient ring
is an **implicit** argument, inferred from the class being operated on, so every
call site that names an `Hmod2`-typed class elaborates unchanged.

The one idiom that needs help is a *partial* application with no class in sight —
`Function.Injective (pull f n)` — where the coefficient ring must be given, as
`pull (K := ZMod 2) f n`.

Nothing in this layer uses `1 = -1`.  Graded commutativity is **not** provided
(see the module footer), so no coefficient ring is privileged here.

## Main declarations

* `Hmod K X n` — `H^n(X; K)`, an object of `ModuleCat K`; `Hmod2 X n` is `K = ZMod 2`.
* `cohCast h a` — transport along an equality of degrees `h : m = m'`.
* `cup a b`, notation `a ⌣ b` — the cup product `H^p → H^q → H^{p+q}`.
* `cup_mk` — the cup of the classes of two cocycles is the class of the cochain cup.
* `cup_add_left`, `cup_add_right`, `cup_smul_left`, `cup_smul_right`, `cupBilin` —
  bilinearity.
* `one X` — the unit `1 ∈ H^0(X; K)`; `cup_one` is strict right unitality.
* `pull f n` — the pullback `f^* : H^n(Y) → H^n(X)` of `f : X ⟶ Y`, with
  `pull_id`, `pull_comp`, `pull_cup`, `pull_one`, `pull_mk`.

The `mk`-flavoured computation rules come in two spellings: the generic
`exists_cocycleOf` / `cup_mkOf` / `pull_mkOf` / `one_eq_cocycleClassOf`, phrased
with `cocycleClassK`, and the `F₂` spellings `exists_cocycle` / `cup_mk` /
`pull_mk` / `one_eq_cocycleClass`, phrased with the vendored `cocycleClass`, which
the `Cartan*` and `Steenrod*` files use.  The two are definitionally the same.

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

/-! ## 1. The graded module `H^*(X; K)` -/

/-- `H^n(X; K)`, the `n`-th singular cohomology of the space `X` with coefficients
in the commutative ring `K`, as an object of `ModuleCat K`.  This is
definitionally the `n`-th homology of the singular `K`-cochain complex of `X`. -/
abbrev Hmod (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} K :=
  cohomologyK K X n

/-- `H^n(X; F₂)`, the mod-2 instance of `Hmod`.  This is reducibly the object the
vendored layer calls `cohomologyZMod2 X n`. -/
abbrev Hmod2 (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} (ZMod 2) := Hmod (ZMod 2) X n

/-- Every class is the class of a cocycle. -/
theorem exists_cocycleOf {K : Type} [CommRing K] {X : TopCat.{0}} {n : ℕ} (a : Hmod K X n) :
    ∃ (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0),
      cocycleClassK K X n φ hφ = a :=
  cocycleClassK_surjective K X n a

/-- Every mod-2 class is the class of a cocycle, in the vendored vocabulary. -/
theorem exists_cocycle {X : TopCat.{0}} {n : ℕ} (a : Hmod2 X n) :
    ∃ (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0),
      cocycleClass X n φ hφ = a :=
  cocycleClassK_surjective (ZMod 2) X n a

/-! ## 2. Degree casts

`p + q + r` and `p + (q + r)` are only propositionally equal, so a graded API over
`ℕ`-indexed groups needs a transport.  `cohCast` is that transport; it is a plain
`Eq.rec` in the degree, which makes `subst` the universal proof method for its
laws. -/

/-- Transport a cohomology class along an equality of degrees. -/
def cohCast {K : Type} [CommRing K] {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (a : Hmod K X m) : Hmod K X m' :=
  h ▸ a

@[simp] theorem cohCast_rfl {K : Type} [CommRing K] {X : TopCat.{0}} {m : ℕ} (a : Hmod K X m) :
    cohCast (rfl : m = m) a = a := rfl

@[simp] theorem cohCast_cohCast {K : Type} [CommRing K] {X : TopCat.{0}} {m₁ m₂ m₃ : ℕ}
    (h : m₁ = m₂) (h' : m₂ = m₃) (a : Hmod K X m₁) :
    cohCast h' (cohCast h a) = cohCast (h.trans h') a := by
  subst h; subst h'; rfl

@[simp] theorem cohCast_add {K : Type} [CommRing K] {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (a b : Hmod K X m) : cohCast h (a + b) = cohCast h a + cohCast h b := by
  subst h; rfl

@[simp] theorem cohCast_zero {K : Type} [CommRing K] {X : TopCat.{0}} {m m' : ℕ} (h : m = m') :
    cohCast h (0 : Hmod K X m) = 0 := by
  subst h; rfl

@[simp] theorem cohCast_smul {K : Type} [CommRing K] {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (s : K) (a : Hmod K X m) : cohCast h (s • a) = s • cohCast h a := by
  subst h; rfl

theorem cohCast_injective {K : Type} [CommRing K] {X : TopCat.{0}} {m m' : ℕ} (h : m = m') :
    Function.Injective (cohCast (K := K) (X := X) h) := by
  subst h; exact fun _ _ hab => hab

@[simp] theorem cohCast_eq_zero_iff {K : Type} [CommRing K] {X : TopCat.{0}} {m m' : ℕ}
    (h : m = m') (a : Hmod K X m) : cohCast h a = 0 ↔ a = 0 := by
  subst h; exact Iff.rfl

theorem cohCast_eq_iff {K : Type} [CommRing K] {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (a : Hmod K X m) (b : Hmod K X m') : cohCast h a = b ↔ a = cohCast h.symm b := by
  subst h; exact Iff.rfl

/-- Two transports along proofs of the same degree identity agree.  This is
definitional proof irrelevance, and it is what lets a chain of casts finish by
`rfl`. -/
theorem cohCast_congr {K : Type} [CommRing K] {X : TopCat.{0}} {m n : ℕ} (h h' : m = n)
    (a : Hmod K X m) : cohCast h a = cohCast h' a := rfl

/-- A transport along any proof of a trivial degree identity is the identity. -/
@[simp] theorem cohCast_self {K : Type} [CommRing K] {X : TopCat.{0}} {m : ℕ} (h : m = m)
    (a : Hmod K X m) : cohCast h a = a := rfl

/-! ## 3. The cup product -/

/-- The cup product `H^p(X; K) → H^q(X; K) → H^{p+q}(X; K)`. -/
def cup {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ} (a : Hmod K X p) (b : Hmod K X q) :
    Hmod K X (p + q) :=
  cupK a b

@[inherit_doc cup] scoped infixl:70 " ⌣ " => cup

/-- **Computation rule.**  The cup product of the classes of two cocycles is the
class of their Alexander–Whitney cochain cup. -/
theorem cup_mkOf {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (φ : singularCochainGroup K X p) (hφ : cochainCoboundary K X p φ = 0)
    (ψ : singularCochainGroup K X q) (hψ : cochainCoboundary K X q ψ = 0) :
    cup (cocycleClassK K X p φ hφ) (cocycleClassK K X q ψ hψ)
      = cocycleClassK K X (p + q) (cochainCup p q φ ψ)
          (cochainCup_respects_cocycles p q φ ψ hφ hψ) :=
  cupK_mk φ hφ ψ hψ

/-- The mod-2 computation rule, in the vendored vocabulary. -/
theorem cup_mk {X : TopCat.{0}} {p q : ℕ}
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cup (cocycleClass X p φ hφ) (cocycleClass X q ψ hψ)
      = cocycleClass X (p + q) (cochainCup p q φ ψ)
          (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) :=
  cupK_mk φ hφ ψ hψ

/-- Cupping on the right with a fixed class is the descended cochain map
`cupHomologyLeftK`; this is the definition, recorded for `map_add`/`map_smul`. -/
theorem cup_eq_cupHomologyLeft {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (a : Hmod K X p) (b : Hmod K X q) :
    cup a b = (cupHomologyLeftK K X p q (classReprK K X q b) (classReprK_isCocycle K X q b)).hom a :=
  rfl

/-- Cupping on the left with a fixed class is the descended cochain map
`cupHomologyRightK`. -/
theorem cup_eq_cupHomologyRight {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (a : Hmod K X p) (b : Hmod K X q) :
    cup a b
      = (cupHomologyRightK K X p q (classReprK K X p a) (classReprK_isCocycle K X p a)).hom b := by
  obtain ⟨ψ, hψ, rfl⟩ := exists_cocycleOf b
  rw [cupHomologyRightK_apply]
  conv_lhs => rw [← cocycleClassK_classReprK K X p a]
  rw [cup_mkOf]

theorem cup_add_left {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (a a' : Hmod K X p) (b : Hmod K X q) : cup (a + a') b = cup a b + cup a' b := by
  rw [cup_eq_cupHomologyLeft, cup_eq_cupHomologyLeft a b, cup_eq_cupHomologyLeft a' b, map_add]

theorem cup_add_right {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (a : Hmod K X p) (b b' : Hmod K X q) : cup a (b + b') = cup a b + cup a b' := by
  rw [cup_eq_cupHomologyRight, cup_eq_cupHomologyRight a b, cup_eq_cupHomologyRight a b', map_add]

theorem cup_smul_left {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ} (s : K)
    (a : Hmod K X p) (b : Hmod K X q) : cup (s • a) b = s • cup a b := by
  rw [cup_eq_cupHomologyLeft, cup_eq_cupHomologyLeft a b, map_smul]

theorem cup_smul_right {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ} (s : K)
    (a : Hmod K X p) (b : Hmod K X q) : cup a (s • b) = s • cup a b := by
  rw [cup_eq_cupHomologyRight, cup_eq_cupHomologyRight a b, map_smul]

@[simp] theorem zero_cup {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ} (b : Hmod K X q) :
    cup (0 : Hmod K X p) b = 0 := by
  rw [cup_eq_cupHomologyLeft, map_zero]

@[simp] theorem cup_zero {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ} (a : Hmod K X p) :
    cup a (0 : Hmod K X q) = 0 := by
  rw [cup_eq_cupHomologyRight, map_zero]

/-- The cup product as a `K`-bilinear map. -/
def cupBilin {K : Type} [CommRing K] (X : TopCat.{0}) (p q : ℕ) :
    Hmod K X p →ₗ[K] Hmod K X q →ₗ[K] Hmod K X (p + q) where
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

@[simp] theorem cupBilin_apply {K : Type} [CommRing K] {X : TopCat.{0}} {p q : ℕ}
    (a : Hmod K X p) (b : Hmod K X q) : cupBilin X p q a b = cup a b := rfl

theorem cup_cohCast_left {K : Type} [CommRing K] {X : TopCat.{0}} {p p' q : ℕ} (h : p = p')
    (a : Hmod K X p) (b : Hmod K X q) :
    cup (cohCast h a) b = cohCast (by omega) (cup a b) := by
  subst h; rfl

theorem cup_cohCast_right {K : Type} [CommRing K] {X : TopCat.{0}} {p q q' : ℕ} (h : q = q')
    (a : Hmod K X p) (b : Hmod K X q) :
    cup a (cohCast h b) = cohCast (by omega) (cup a b) := by
  subst h; rfl

/-! ## 4. The unit -/

/-- The unit class `1 ∈ H^0(X; K)`. -/
def one {K : Type} [CommRing K] (X : TopCat.{0}) : Hmod K X 0 := oneK K X

theorem one_eq_cocycleClassOf (K : Type) [CommRing K] (X : TopCat.{0}) :
    one X = cocycleClassK K X 0 (cochainOne (R := K) (Z := X))
      (cochainCoboundary_cochainOneK K X) := rfl

theorem one_eq_cocycleClass (X : TopCat.{0}) :
    one X = cocycleClass X 0 (cochainOne (R := ZMod 2) (Z := X))
      (cochainCoboundary_cochainOne X) := rfl

/-- **Strict right unitality.**  `a ⌣ 1 = a`; no degree cast is needed because
`p + 0` reduces to `p`. -/
@[simp] theorem cup_one {K : Type} [CommRing K] {X : TopCat.{0}} {p : ℕ} (a : Hmod K X p) :
    cup a (one X) = a := by
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycleOf a
  rw [one_eq_cocycleClassOf K, cup_mkOf]
  exact cocycleClassK_congr K X (p + 0) (cochainCup_one p φ) _ _

/-! ## 5. Pullback -/

/-- The pullback `f^* : H^n(Y; K) → H^n(X; K)` along `f : X ⟶ Y`. -/
def pull {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : Hmod K Y n) :
    Hmod K X n :=
  (cohPullbackK K f n).hom a

theorem pull_eq_cohPullback {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : Hmod K Y n) : pull f n a = (cohPullbackK K f n).hom a := rfl

@[simp] theorem pull_add {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a b : Hmod K Y n) : pull f n (a + b) = pull f n a + pull f n b :=
  map_add _ _ _

@[simp] theorem pull_zero {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    pull f n (0 : Hmod K Y n) = 0 :=
  map_zero _

theorem pull_smul {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (s : K)
    (a : Hmod K Y n) : pull f n (s • a) = s • pull f n a :=
  map_smul _ _ _

/-- The pullback of a class along `f`, as a `K`-linear map. -/
def pullLinear {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    Hmod K Y n →ₗ[K] Hmod K X n :=
  (cohPullbackK K f n).hom

@[simp] theorem pullLinear_apply {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : Hmod K Y n) : pullLinear f n a = pull f n a := rfl

@[simp] theorem pull_id {K : Type} [CommRing K] {X : TopCat.{0}} (n : ℕ) (a : Hmod K X n) :
    pull (𝟙 X) n a = a := by
  show ((singularCohomologyFunctor K (ModuleCat.of K K) n).map (𝟙 X).op).hom a = a
  rw [CategoryTheory.op_id, (singularCohomologyFunctor K (ModuleCat.of K K) n).map_id]
  rfl

theorem pull_comp {K : Type} [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (a : Hmod K Z n) : pull (f ≫ g) n a = pull f n (pull g n a) := by
  show ((singularCohomologyFunctor K (ModuleCat.of K K) n).map (f ≫ g).op).hom a = _
  rw [CategoryTheory.op_comp, (singularCohomologyFunctor K (ModuleCat.of K K) n).map_comp]
  rfl

theorem pull_congr {K : Type} [CommRing K] {X Y : TopCat.{0}} {f g : X ⟶ Y} (h : f = g) (n : ℕ)
    (a : Hmod K Y n) : pull f n a = pull g n a := by rw [h]

/-- **Computation rule for the pullback.**  The pullback of the class of a cocycle
is the class of the pullback cochain. -/
theorem pull_mkOf {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup K Y n) (hφ : cochainCoboundary K Y n φ = 0) :
    pull f n (cocycleClassK K Y n φ hφ)
      = cocycleClassK K X n (cochainPullback f n φ) (cochainPullback_cocycleK K f n φ hφ) :=
  cohPullbackK_cocycleClassK K f n φ hφ

/-- The mod-2 pullback computation rule, in the vendored vocabulary. -/
theorem pull_mk {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) (hφ : cochainCoboundary (ZMod 2) Y n φ = 0) :
    pull f n (cocycleClass Y n φ hφ)
      = cocycleClass X n (cochainPullback f n φ) (cochainPullback_cocycle f n φ hφ) :=
  cohPullbackK_cocycleClassK (ZMod 2) f n φ hφ

/-- **Naturality of the cup product.**  `f^*(a ⌣ b) = f^* a ⌣ f^* b`. -/
theorem pull_cup {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) {p q : ℕ}
    (a : Hmod K Y p) (b : Hmod K Y q) :
    pull f (p + q) (cup a b) = cup (pull f p a) (pull f q b) :=
  cohPullbackK_cupK K f p q a b

/-- The pullback preserves the unit. -/
@[simp] theorem pull_one {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) :
    pull f 0 (one Y) = (one X : Hmod K X 0) := by
  rw [one_eq_cocycleClassOf K, pull_mkOf]
  refine cocycleClassK_congr K X 0 ?_ _ _
  apply cochain_ext; intro σ
  rw [cochainPullback_eval, cochainOne_eval, cochainOne_eval]

end

end GroupApproximation.CharClass

/-!
## Not provided here

**Graded commutativity** `a ⌣ b = ± b ⌣ a`.  The Alexander–Whitney cochain
cup product is *not* commutative on the nose, and the vendored tree carries no
chain homotopy between the AW diagonal and its transpose.  The homotopy is the
standard consequence of the (ℤ/2-equivariant, resp. ℤ/p-equivariant)
acyclic-models theorem, which is lane `cc-cartan`'s deliverable at `F₂`; until it
lands, downstream lemmas must be stated for classes pulled back from different
factors of a product, where the commutation is a formal consequence of naturality
rather than of a chain homotopy.  Chern classes have even degree, so nothing in
the LIX program needs it.
-/
