import GroupApproximation.GGT.HullSCUnionGeometryFourPoint
import GroupApproximation.GGT.HullSCFreeProductFactor
import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.HyperbolicFreeGroupAH
import GroupApproximation.Higman.CoprodTorsion

/-!
# `Γ(E ∗ H, A ⊔ B)` is hyperbolic

`GGT/HullSCUnionGeometryFourPoint.lean` proves the four-point condition for the
union alphabet of Mathlib's *indexed* free product `CoprodI`.  Hull's Corollary
7.4 is stated over the *binary* one, `Monoid.Coprod E H`, and it asks for
`HullGeometry.IsHyperbolicSpace` --- the `ℝ`-valued `min` form on
`gromovProduct` --- rather than the `ℕ`-valued `max` form on `wordDist`.  This
module carries the statement across both gaps and lands it on
`HullSC.unionAlphabet`:

    exists_isHyperbolicSpace_cayley_unionAlphabet :
      ∀ (A : HullGeneratingSet E) (B : HullGeneratingSet H),
        ∃ δ, IsHyperbolicSpace δ (Cayley (unionAlphabet A.alphabet B.alphabet))

with no hypothesis on `E` and `H` beyond having Hull generating sets at all: no
finite presentation, no torsion-freeness, no property `(T)`.  That is the first
of the two clauses of `HullSC.FreeProductUnionGeometryStatement`.

## The three steps

* **binary to indexed.**  `Higman.coprodEquiv` identifies `Monoid.Coprod E H`
  with `CoprodI (Amalgam.fam E H)`, and carries `HullSC.UnionCarrier` onto
  `FreeProductUnionNorm.unionCarrier` of the two-element family of factor
  alphabets.  `HullSC.wordNorm_of_mulEquiv` then makes the two word lengths
  equal, and `isFourPointHyperbolic_of_wordNorm_eq` transports the condition.
* **`ℝ` to `ℕ`.**  `isFourPointHyperbolic_of_isHyperbolicSpace` is the converse
  of `GGT.isHyperbolicSpace_cayley_of_fourPoint`: the `min` form at a real `δ`
  gives the `max` form at `⌈δ⌉₊`, since the two are the same six-distance
  inequality read at a permuted quadruple.  It is what turns the `hyperbolic`
  field of a `HullGeneratingSet` back into a combinatorial input.
* **`ℕ` to `ℝ`.**  `GGT.isHyperbolicSpace_cayley_of_fourPoint`, already in the
  repository, closes the circle.

## What is *not* here

The second clause of `HullSC.FreeProductUnionGeometryStatement` --- that the
translation action of `E ∗ H` on `Γ(E ∗ H, A ⊔ B)` is acylindrical --- is not
proved.  `freeProductUnionGeometryStatement_of` records exactly what is left:
that clause, and the construction of a Hull generating set on an infinite
hyperbolic group with property `(T)`, whose only missing ingredient is
non-elementarity of the translation action (`hullGeneratingSetOfHyperbolic`
supplies the other two fields outright).
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.FreeProductUnionNorm
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## 1.  Transport of the four-point condition along an isomorphism -/

/-- **A length-preserving isomorphism carries the four-point condition back.**
Every distance is a length of a difference, and the isomorphism carries
differences to differences. -/
theorem isFourPointHyperbolic_of_wordNorm_eq {E Gam : Type} [Group E] [Group Gam]
    {A : Set E} {C : Set Gam} (e : E ≃* Gam)
    (hnorm : ∀ w : E, wordNorm C (e w) = wordNorm A w) {δ : ℕ}
    (hC : Hyperbolic.IsFourPointHyperbolic C δ) :
    Hyperbolic.IsFourPointHyperbolic A δ := by
  intro w x y z
  have hd : ∀ a b : E, wordDist A a b = wordDist C (e a) (e b) := by
    intro a b
    have h : (e a)⁻¹ * e b = e (a⁻¹ * b) := by
      rw [map_mul, map_inv]
    show wordNorm A (a⁻¹ * b) = wordNorm C ((e a)⁻¹ * e b)
    rw [h, hnorm]
  rw [hd w x, hd y z, hd w y, hd x z, hd w z, hd x y]
  exact hC (e w) (e x) (e y) (e z)

/-! ## 2.  The two-element family of factor alphabets -/

/-- The two factor alphabets, indexed as `Higman.Amalgam.fam` indexes the two
factors of a binary free product. -/
def famCarrier {E H : Type} [Group E] [Group H] (A : Set E) (B : Set H) :
    ∀ b : Bool, Set (Higman.Amalgam.fam E H b)
  | false => A
  | true => B

theorem isSymmetricGeneratingSet_famCarrier {E H : Type} [Group E] [Group H]
    {A : Set E} {B : Set H} (hA : IsSymmetricGeneratingSet A)
    (hB : IsSymmetricGeneratingSet B) :
    ∀ b : Bool, IsSymmetricGeneratingSet (famCarrier A B b) := by
  intro b
  cases b with
  | false => exact hA
  | true => exact hB

theorem isFourPointHyperbolic_famCarrier {E H : Type} [Group E] [Group H]
    {A : Set E} {B : Set H} {δ : ℕ}
    (hA : Hyperbolic.IsFourPointHyperbolic A δ)
    (hB : Hyperbolic.IsFourPointHyperbolic B δ) :
    ∀ b : Bool, Hyperbolic.IsFourPointHyperbolic (famCarrier A B b) δ := by
  intro b
  cases b with
  | false => exact hA
  | true => exact hB

/-! ## 3.  The isomorphism carries the union alphabet to the union alphabet -/

theorem coprodEquiv_inl {E H : Type} [Group E] [Group H] (a : E) :
    Higman.coprodEquiv (Monoid.Coprod.inl a : Monoid.Coprod E H)
      = (Monoid.CoprodI.of (i := false) a
          : Monoid.CoprodI (Higman.Amalgam.fam E H)) := by
  show Higman.toCoprodI (Monoid.Coprod.inl a) = _
  unfold Higman.toCoprodI
  rw [Monoid.Coprod.lift_apply_inl]; rfl

theorem coprodEquiv_inr {E H : Type} [Group E] [Group H] (b : H) :
    Higman.coprodEquiv (Monoid.Coprod.inr b : Monoid.Coprod E H)
      = (Monoid.CoprodI.of (i := true) b : Monoid.CoprodI (Higman.Amalgam.fam E H)) := by
  show Higman.toCoprodI (Monoid.Coprod.inr b) = _
  unfold Higman.toCoprodI
  rw [Monoid.Coprod.lift_apply_inr]; rfl

theorem coprodEquiv_symm_false {E H : Type} [Group E] [Group H] (a : E) :
    Higman.coprodEquiv.symm
        (Monoid.CoprodI.of (i := false) a : Monoid.CoprodI (Higman.Amalgam.fam E H))
      = (Monoid.Coprod.inl a : Monoid.Coprod E H) := by
  show Higman.fromCoprodI (Monoid.CoprodI.of (i := false) a) = _
  unfold Higman.fromCoprodI
  rw [Monoid.CoprodI.lift_of]; rfl

theorem coprodEquiv_symm_true {E H : Type} [Group E] [Group H] (b : H) :
    Higman.coprodEquiv.symm
        (Monoid.CoprodI.of (i := true) b : Monoid.CoprodI (Higman.Amalgam.fam E H))
      = (Monoid.Coprod.inr b : Monoid.Coprod E H) := by
  show Higman.fromCoprodI (Monoid.CoprodI.of (i := true) b) = _
  unfold Higman.fromCoprodI
  rw [Monoid.CoprodI.lift_of]; rfl

/-- **The union alphabet of the binary free product satisfies the four-point
condition at the constant of the two factors.** -/
theorem isFourPointHyperbolic_unionAlphabet {E H : Type} [Group E] [Group H]
    (A : Alphabet E) (B : Alphabet H) {δ : ℕ}
    (hA : Hyperbolic.IsFourPointHyperbolic A.carrier δ)
    (hB : Hyperbolic.IsFourPointHyperbolic B.carrier δ) :
    Hyperbolic.IsFourPointHyperbolic (HullSC.unionAlphabet A B).carrier δ := by
  letI : ∀ b : Bool, DecidableEq (Higman.Amalgam.fam E H b) :=
    fun b => Classical.decEq (Higman.Amalgam.fam E H b)
  have hfam := isSymmetricGeneratingSet_famCarrier A.symmetricGenerating
    B.symmetricGenerating
  have hC := isFourPointHyperbolic_unionCarrier hfam
    (isFourPointHyperbolic_famCarrier hA hB)
  have hmem : ∀ x ∈ HullSC.UnionCarrier A B,
      Higman.coprodEquiv x ∈ unionCarrier (famCarrier A.carrier B.carrier) := by
    intro x hx
    rcases HullSC.mem_unionCarrier.mp hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ⟨false, a, ha, (coprodEquiv_inl a).symm⟩
    · exact ⟨true, b, hb, (coprodEquiv_inr b).symm⟩
  have hmem' : ∀ x ∈ unionCarrier (famCarrier A.carrier B.carrier),
      Higman.coprodEquiv.symm x ∈ HullSC.UnionCarrier A B := by
    rintro x ⟨i, a, ha, rfl⟩
    cases i with
    | false =>
        exact HullSC.mem_unionCarrier.mpr
          (Or.inl ⟨a, ha, (coprodEquiv_symm_false a).symm⟩)
    | true =>
        exact HullSC.mem_unionCarrier.mpr
          (Or.inr ⟨a, ha, (coprodEquiv_symm_true a).symm⟩)
  have hnorm : ∀ w : Monoid.Coprod E H,
      wordNorm (unionCarrier (famCarrier A.carrier B.carrier))
          (Higman.coprodEquiv w)
        = wordNorm (HullSC.UnionCarrier A B) w :=
    HullSC.wordNorm_of_mulEquiv (HullSC.unionAlphabet A B).symmetricGenerating
      (isSymmetricGeneratingSet_unionCarrier hfam)
      (Higman.coprodEquiv (G := E) (H := H)) hmem hmem'
  exact isFourPointHyperbolic_of_wordNorm_eq
    (Higman.coprodEquiv (G := E) (H := H)) hnorm hC

/-! ## 4.  From the `ℝ`-valued `min` form back to the `ℕ`-valued `max` form -/

/-- **The `min` form implies the `max` form**, at six reals.  The two are the
same inequality read at a permuted quadruple, and each branch of the `min`
discharges one branch of the `max`. -/
theorem fourPoint_of_min_gromov {dwx dwy dwz dyx dyz dxz e : ℝ}
    (h : min ((dwy + dwx - dyx) / 2) ((dwx + dwz - dxz) / 2) - e
      ≤ (dwy + dwz - dyz) / 2) :
    dwx + dyz ≤ max (dwy + dxz) (dwz + dyx) + 2 * e := by
  rcases le_total ((dwy + dwx - dyx) / 2) ((dwx + dwz - dxz) / 2) with hm | hm
  · rw [min_eq_left hm] at h
    have hmax := le_max_right (dwy + dxz) (dwz + dyx)
    linarith
  · rw [min_eq_right hm] at h
    have hmax := le_max_left (dwy + dxz) (dwz + dyx)
    linarith

/-- The Gromov product of two vertices of `Γ(G,A)` based at a third, in word
distances. -/
theorem gromovProduct_cayley_of {G : Type} [Group G] (A : Alphabet G)
    (a b c : G) :
    gromovProduct (Cayley.of A a) (Cayley.of A b) (Cayley.of A c)
      = (((wordDist A.carrier c a : ℕ) : ℝ) + ((wordDist A.carrier c b : ℕ) : ℝ)
          - ((wordDist A.carrier a b : ℕ) : ℝ)) / 2 := by
  have hS := A.symmetricGenerating
  have hd : ∀ p q : G, dist (Cayley.of A p) (Cayley.of A q)
      = ((wordDist A.carrier p q : ℕ) : ℝ) := fun _ _ => rfl
  show (dist (Cayley.of A a) (Cayley.of A c) + dist (Cayley.of A b) (Cayley.of A c)
      - dist (Cayley.of A a) (Cayley.of A b)) / 2 = _
  rw [hd, hd, hd, wordDist_comm hS a c, wordDist_comm hS b c]

/-- **A hyperbolic Cayley graph has a four-point alphabet.**  The converse of
`GGT.isHyperbolicSpace_cayley_of_fourPoint`, at the constant `⌈δ⌉₊`: this is what
turns the `hyperbolic` field of a `HullGeneratingSet` back into the
combinatorial input the union-alphabet theorem consumes. -/
theorem isFourPointHyperbolic_of_isHyperbolicSpace {G : Type} [Group G]
    (A : Alphabet G) {δ : ℝ} (h : IsHyperbolicSpace δ (Cayley A)) :
    Hyperbolic.IsFourPointHyperbolic A.carrier ⌈δ⌉₊ := by
  intro w x y z
  have hS := A.symmetricGenerating
  have hceil : δ ≤ ((⌈δ⌉₊ : ℕ) : ℝ) := Nat.le_ceil δ
  have key := h (Cayley.of A w) (Cayley.of A y) (Cayley.of A x) (Cayley.of A z)
  rw [gromovProduct_cayley_of A y x w, gromovProduct_cayley_of A x z w,
    gromovProduct_cayley_of A y z w] at key
  have hR := fourPoint_of_min_gromov key
  have hR2 := le_trans hR
    (add_le_add le_rfl (by linarith : 2 * δ ≤ 2 * ((⌈δ⌉₊ : ℕ) : ℝ)))
  have hdisj :
      ((wordDist A.carrier w x : ℕ) : ℝ) + ((wordDist A.carrier y z : ℕ) : ℝ)
          ≤ (((wordDist A.carrier w y : ℕ) : ℝ)
              + ((wordDist A.carrier x z : ℕ) : ℝ)) + 2 * ((⌈δ⌉₊ : ℕ) : ℝ)
        ∨ ((wordDist A.carrier w x : ℕ) : ℝ) + ((wordDist A.carrier y z : ℕ) : ℝ)
          ≤ (((wordDist A.carrier w z : ℕ) : ℝ)
              + ((wordDist A.carrier y x : ℕ) : ℝ)) + 2 * ((⌈δ⌉₊ : ℕ) : ℝ) := by
    rcases le_total
        (((wordDist A.carrier w y : ℕ) : ℝ) + ((wordDist A.carrier x z : ℕ) : ℝ))
        (((wordDist A.carrier w z : ℕ) : ℝ)
          + ((wordDist A.carrier y x : ℕ) : ℝ)) with hm | hm
    · rw [max_eq_right hm] at hR2
      exact Or.inr hR2
    · rw [max_eq_left hm] at hR2
      exact Or.inl hR2
  have hcomm : wordDist A.carrier y x = wordDist A.carrier x y :=
    wordDist_comm hS y x
  rcases hdisj with hk | hk
  · refine le_trans ?_ (Nat.add_le_add_right (le_max_left _ _) (2 * ⌈δ⌉₊))
    exact_mod_cast hk
  · rw [hcomm] at hk
    refine le_trans ?_ (Nat.add_le_add_right (le_max_right _ _) (2 * ⌈δ⌉₊))
    exact_mod_cast hk

/-! ## 5.  The hyperbolicity clause of the free product input -/

/-- **`Γ(E ∗ H, A ⊔ B)` is hyperbolic**, for Hull generating sets `A` on `E` and
`B` on `H`.

This is the first of the two clauses of
`HullSC.FreeProductUnionGeometryStatement`, and it holds with no hypothesis on
the two groups beyond having Hull generating sets: the constant is
`max ⌈δ_A⌉₊ ⌈δ_B⌉₊`, and the tree directions of the free product cost nothing. -/
theorem exists_isHyperbolicSpace_cayley_unionAlphabet {E H : Type} [Group E]
    [Group H] (A : HullGeneratingSet E) (B : HullGeneratingSet H) :
    ∃ δ : ℝ, IsHyperbolicSpace δ
      (Cayley (HullSC.unionAlphabet A.alphabet B.alphabet)) := by
  have hA : Hyperbolic.IsFourPointHyperbolic A.alphabet.carrier
      (max ⌈A.delta⌉₊ ⌈B.delta⌉₊) :=
    (isFourPointHyperbolic_of_isHyperbolicSpace A.alphabet A.hyperbolic).mono
      (le_max_left _ _)
  have hB : Hyperbolic.IsFourPointHyperbolic B.alphabet.carrier
      (max ⌈A.delta⌉₊ ⌈B.delta⌉₊) :=
    (isFourPointHyperbolic_of_isHyperbolicSpace B.alphabet B.hyperbolic).mono
      (le_max_right _ _)
  exact ⟨((max ⌈A.delta⌉₊ ⌈B.delta⌉₊ : ℕ) : ℝ),
    GGT.isHyperbolicSpace_cayley_of_fourPoint _
      (isFourPointHyperbolic_unionAlphabet A.alphabet B.alphabet hA hB)⟩

/-! ## 6.  What the free product input still needs -/

/-- **A Hull generating set on a hyperbolic group, from non-elementarity
alone.**

Two of the three fields are theorems: the four-point condition of the finite
alphabet is hyperbolicity of `Γ(H,B)` by
`GGT.isHyperbolicSpace_cayley_of_fourPoint`, and a finite alphabet makes the
translation action proper, hence acylindrical, by
`GGT.isAcylindrical_cayley_of_finite`.  Only the third --- that `H` contains two
independent loxodromic elements --- has to be supplied. -/
noncomputable def hullGeneratingSetOfHyperbolic {H : Type} [Group H] {T : Finset H}
    (hT : IsSymmetricGeneratingSet (T : Set H)) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic (T : Set H) δ)
    (hne : ActsNonElementarily (⊤ : Subgroup H)
      (Cayley.base (⟨(T : Set H), hT⟩ : Alphabet H))) : HullGeneratingSet H where
  alphabet := ⟨(T : Set H), hT⟩
  delta := (δ : ℝ)
  hyperbolic := GGT.isHyperbolicSpace_cayley_of_fourPoint _ hδ
  acylindrical := GGT.isAcylindrical_cayley_of_finite _ T.finite_toSet
  nonElementary := hne

/-- **`HullSC.FreeProductUnionGeometryStatement`, with its hyperbolicity clause
discharged.**

The two hypotheses are exactly what this lane does not prove:

* `hacyl` --- the translation action of `E ∗ H` on `Γ(E ∗ H, A ⊔ B)` is
  acylindrical.  This is the tree-of-spaces crossing estimate, and it is the
  clause the free product input still owes.
* `hHull` --- an infinite hyperbolic group with property `(T)` has a Hull
  generating set.  By `hullGeneratingSetOfHyperbolic` all that this needs is
  that such a group acts non-elementarily on its own Cayley graph, i.e. contains
  two independent loxodromic elements; `GGT.RelHyp.isNonElementaryHyperbolic_of_kazhdan'`
  already gives that it is not virtually cyclic.

Everything else --- the choice of alphabet, hyperbolicity of the union Cayley
graph, and the assembly --- is proved. -/
theorem freeProductUnionGeometryStatement_of
    (hacyl : ∀ (E H : Type) [Group E] [Group H] (A : HullGeneratingSet E)
      (B : HullGeneratingSet H),
        IsAcylindrical (Monoid.Coprod E H)
          (Cayley (HullSC.unionAlphabet A.alphabet B.alphabet)))
    (hHull : ∀ (H : Type) [Group H], Infinite H →
      GroupApproximation.Hyperbolic.IsHyperbolicGroup H →
        HasKazhdanPropertyT.{0, 0} H → Nonempty (HullGeneratingSet H)) :
    HullSC.FreeProductUnionGeometryStatement := by
  intro E H instE instH _hEfp _hHfp _hEtf _hHtf hEah hHinf hHhyp hHT
  letI := instE
  letI := instH
  haveI := hEah
  obtain ⟨A⟩ := exists_hullGeneratingSet E
  obtain ⟨B⟩ := hHull H hHinf hHhyp hHT
  obtain ⟨δ, hδ⟩ := exists_isHyperbolicSpace_cayley_unionAlphabet A B
  exact ⟨A, B, δ, hδ, hacyl E H A B⟩

end HullSCUnionGeometry
end GroupApproximation
