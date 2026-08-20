import GroupApproximation.Sofic.HullSuitableDefectSubgroup
import GroupApproximation.Sofic.ConcreteCompressionSource
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# A suitable subgroup inside a compression defect, with no hypotheses at all

`Sofic.HullSuitableDefectSubgroup` builds the object the Hull routing audit says
is missing --- a two-generated subgroup of a compression defect satisfying every
non-geometric clause of Hull's suitability --- from two inputs: an ambient group
that is torsion-free, and a non-commuting pair inside the defect.  At the
Fournier--Facio datum the pair is a field of the datum, but torsion-freeness of
the ambient is a hypothesis, and it has to be: over an ambient with torsion the
clause is false, so no proof can remove it.

This module removes it the only way it can be removed, by **building an ambient
instead of assuming one**.  Everything below is constructed; the final term

    explicitSuitableDefectSubgroup :
      HullSuitable.SuitableDefectSubgroup explicitDatum.defectNormal

takes no arguments, has no hypotheses, and is not conditional on anything.

## The group

Let `Coeff` be the free group of rank two and let `Lamp = ℤ → Coeff` be the
configurations of a `Coeff`-valued lamp at every integer site.  The integers act
on `Lamp` by translating sites, and

    Skeleton = Lamp ⋊ ℤ

is the resulting semidirect product.  This is the compression pattern of the
manuscript in its barest form:

* `iota` embeds `Lamp` by first erasing the negative sites, so its image is the
  configurations supported on `[0, ∞)`;
* the stable letter `stable` translates by one, which pushes that image strictly
  inside itself --- the compression;
* the root is a single lamp at site `-1`.  The compressed copy cannot see site
  `-1`, so the root centralizes it, which is condition (M2);
* transporting the root by the stable letter moves it to site `0`, which the
  compressed copy *can* see.  So the transported root fails to centralize, and
  the compression defect is nontrivial.

Every one of those is an equation between explicit functions on `ℤ`, proved by
splitting on the site.

## Why the coefficients are free

The defect lands in the lamp factor and is, coordinatewise, the normal closure
of `[x, Coeff]`.  So the defect is non-abelian exactly when that normal closure
is, and it is abelian for every soluble coefficient group --- a lamp group over
`ℤ`, over a Klein-bottle group, over any iterated extension with abelian kernels,
all fail.  A free group of rank two is the cheapest coefficient group that
works, and Mathlib's `IsMulTorsionFree (FreeGroup α)` supplies exactly the other
thing needed: torsion-freeness, which passes to the product `ℤ → Coeff`
pointwise and then to `Skeleton` because a semidirect product of a torsion-free
group by `ℤ` is torsion-free.

The two non-commuting defect elements are the marked commutators `[d, ι p]` for
`p` the lamp `y` at site `0` and the lamp `y²` at site `0`; they reduce to
`[x, y]` and `[x, y²]` in the coefficient group, and those do not commute.  The
free group has decidable equality, so that last fact is `decide` --- a kernel
computation on reduced words, not a citation.

## What this is and is not

It **is** an unconditional inhabitant of the object Hull's theorem takes as its
hypothesis: a subgroup of a genuine compression defect, over a genuine ambient
group, satisfying every clause of suitability that is group theory.

It is **not** a step towards routing the Fournier--Facio group: `Skeleton` has no
Kazhdan source and is not acylindrically hyperbolic, so Hull's theorem does not
apply to it and nothing here claims otherwise.  The geometric clause of
Definition 1.4 is not stated in this library at all, for the reason
`Sofic.HullSuitableDefectSubgroup` gives.  What is settled here is that the
algebraic half of the object needs no hypotheses: it can be exhibited.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u v

/-! ## Generic ingredients -/

namespace ExplicitSuitableDefect

/-- Torsion-freeness is a pointwise property of a product of groups. -/
theorem isPowerTorsionFree_pi {X : Type u} {M : Type v} [Group M]
    (hM : IsPowerTorsionFree M) : IsPowerTorsionFree (X → M) := by
  intro g n hn hpow
  funext x
  exact hM (g x) n hn (congrFun hpow x)

/-- A semidirect product of torsion-free groups is torsion-free: the right
factor kills the `ℤ`-coordinate, and what is left lies in the left factor. -/
theorem isPowerTorsionFree_semidirectProduct {N H : Type u} [Group N] [Group H]
    {φ : H →* MulAut N} (hN : IsPowerTorsionFree N)
    (hH : IsPowerTorsionFree H) :
    IsPowerTorsionFree (SemidirectProduct N H φ) := by
  intro g n hn hpow
  have hright : g.right = 1 := by
    refine hH g.right n hn ?_
    have h0 : SemidirectProduct.rightHom (g ^ n) = 1 := by
      rw [hpow, map_one]
    rw [map_pow] at h0
    simpa using h0
  have hg : g = SemidirectProduct.inl g.left :=
    SemidirectProduct.ext (by simp) (by simp [hright])
  have hleft : g.left = 1 := by
    refine hN g.left n hn ?_
    have h2 : (SemidirectProduct.inl (g.left ^ n) : SemidirectProduct N H φ)
        = SemidirectProduct.inl 1 := by
      rw [map_pow, ← hg, hpow, map_one]
    exact SemidirectProduct.inl_injective h2
  rw [hg, hleft, map_one]

/-- Precomposition by a permutation of the index set is an automorphism of a
product group. -/
def piPermAut {X : Type u} {M : Type v} [Group M] (e : Equiv.Perm X) :
    MulAut (X → M) where
  toFun f := fun x => f (e.symm x)
  invFun f := fun x => f (e x)
  left_inv f := by funext x; simp
  right_inv f := by funext x; simp
  map_mul' _ _ := rfl

@[simp] theorem piPermAut_apply {X : Type u} {M : Type v} [Group M]
    (e : Equiv.Perm X) (f : X → M) (x : X) :
    piPermAut e f x = f (e.symm x) := rfl

/-- A permutation action of a group on the index set acts on the product group
by automorphisms. -/
def piPermAutHom {X : Type u} {M : Type v} {H : Type u} [Group M] [Group H]
    (rho : H →* Equiv.Perm X) : H →* MulAut (X → M) where
  toFun h := piPermAut (rho h)
  map_one' := by
    apply MulEquiv.ext
    intro f
    funext x
    rw [map_one]
    rfl
  map_mul' h h' := by
    apply MulEquiv.ext
    intro f
    funext x
    rw [map_mul]
    rfl

/-! ## The explicit ambient group -/

/-- Translation of the integer sites. -/
def transEquiv (k : ℤ) : Equiv.Perm ℤ where
  toFun x := x + k
  invFun x := x - k
  left_inv x := by show x + k - k = x; omega
  right_inv x := by show x - k + k = x; omega

@[simp] theorem transEquiv_symm_apply (k n : ℤ) :
    (transEquiv k).symm n = n - k := rfl

/-- The integers act on their own sites by translation. -/
def transHom : Multiplicative ℤ →* Equiv.Perm ℤ where
  toFun k := transEquiv (Multiplicative.toAdd k)
  map_one' := by
    apply Equiv.ext
    intro x
    show x + Multiplicative.toAdd (1 : Multiplicative ℤ) = x
    simp
  map_mul' k l := by
    apply Equiv.ext
    intro x
    show x + Multiplicative.toAdd (k * l)
        = x + Multiplicative.toAdd l + Multiplicative.toAdd k
    rw [toAdd_mul]
    ring

/-- The coefficient group of the lamps: free of rank two. -/
abbrev Coeff : Type := FreeGroup (Fin 2)

/-- The first free generator. -/
abbrev cx : Coeff := FreeGroup.of 0

/-- The second free generator. -/
abbrev cy : Coeff := FreeGroup.of 1

/-- Lamp configurations: one coefficient at every integer site. -/
abbrev Lamp : Type := ℤ → Coeff

/-- The shift action of the integers on lamp configurations. -/
def shift : Multiplicative ℤ →* MulAut Lamp := piPermAutHom transHom

@[simp] theorem shift_apply (k : Multiplicative ℤ) (f : Lamp) (n : ℤ) :
    shift k f n = f (n - Multiplicative.toAdd k) := rfl

/-- **The explicit ambient group.**  Lamp configurations extended by the shift.
-/
abbrev Skeleton : Type := SemidirectProduct Lamp (Multiplicative ℤ) shift

/-- Free groups are torsion-free in the ordinary power sense. -/
theorem coeff_isPowerTorsionFree : IsPowerTorsionFree Coeff :=
  IsPowerTorsionFree.of_isMulTorsionFree

/-- A product of free groups is torsion-free. -/
theorem lamp_isPowerTorsionFree : IsPowerTorsionFree Lamp :=
  isPowerTorsionFree_pi coeff_isPowerTorsionFree

/-- **The ambient group is torsion-free.**  This is the hypothesis that
`SuitableDefectSubgroup.ofNoncommutingPair` cannot do without and that no
theorem about a general datum can supply; here it is a theorem, because the
group is built rather than assumed. -/
theorem skeleton_isPowerTorsionFree : IsPowerTorsionFree Skeleton :=
  isPowerTorsionFree_semidirectProduct lamp_isPowerTorsionFree
    ConcreteCompressionSource.isPowerTorsionFree_multiplicative_int

/-! ## Lamps at a single site -/

/-- The configuration carrying `a` at site `i` and nothing anywhere else. -/
def lamp (i : ℤ) (a : Coeff) : Lamp := fun n => if n = i then a else 1

@[simp] theorem lamp_self (i : ℤ) (a : Coeff) : lamp i a i = a := by
  simp [lamp]

theorem lamp_of_ne {i n : ℤ} (h : n ≠ i) (a : Coeff) : lamp i a n = 1 := by
  simp [lamp, h]

theorem lamp_eq_one_iff (i : ℤ) (a : Coeff) : lamp i a = 1 ↔ a = 1 := by
  constructor
  · intro h
    have h1 : lamp i a i = 1 := by simp [h]
    rwa [lamp_self] at h1
  · intro h
    subst h
    funext n
    simp [lamp]

/-- A single lamp commutes with every configuration that is trivial at its
site. -/
theorem commute_lamp {i : ℤ} {a : Coeff} {g : Lamp} (hg : g i = 1) :
    Commute (lamp i a) g := by
  show lamp i a * g = g * lamp i a
  funext n
  by_cases hn : n = i
  · rw [hn]
    show lamp i a i * g i = g i * lamp i a i
    rw [hg, lamp_self, mul_one, one_mul]
  · show lamp i a n * g n = g n * lamp i a n
    rw [lamp_of_ne hn, one_mul, mul_one]

/-- Commutators against a single lamp are computed at that lamp's site. -/
theorem commutator_lamp (i : ℤ) (a : Coeff) (g : Lamp) :
    ⁅lamp i a, g⁆ = lamp i ⁅a, g i⁆ := by
  funext n
  by_cases hn : n = i
  · rw [hn]
    show ⁅lamp i a i, g i⁆ = lamp i ⁅a, g i⁆ i
    rw [lamp_self, lamp_self]
  · show ⁅lamp i a n, g n⁆ = lamp i ⁅a, g i⁆ n
    rw [lamp_of_ne hn, lamp_of_ne hn, commutatorElement_one_left]

/-! ## The compression pattern -/

/-- Erasing the negative sites. -/
def mask : Lamp →* Lamp where
  toFun f := fun n => if 0 ≤ n then f n else 1
  map_one' := by
    funext n
    by_cases h : (0:ℤ) ≤ n <;> simp [h]
  map_mul' f g := by
    funext n
    by_cases h : (0:ℤ) ≤ n <;> simp [h]

@[simp] theorem mask_apply (f : Lamp) (n : ℤ) :
    mask f n = if 0 ≤ n then f n else 1 := rfl

/-- The source map: lamp configurations placed on the nonnegative sites. -/
def iota : Lamp →* Skeleton := SemidirectProduct.inl.comp mask

@[simp] theorem iota_apply (f : Lamp) :
    iota f = SemidirectProduct.inl (mask f) := rfl

/-- The stable letter: translation by one site. -/
def stable : Skeleton := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))

/-- Conjugation by the stable letter is the shift on the lamp factor. -/
theorem stable_conj (m : Lamp) :
    stable * SemidirectProduct.inl m * stable⁻¹
      = SemidirectProduct.inl (shift (Multiplicative.ofAdd (1 : ℤ)) m) := by
  show SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) *
      SemidirectProduct.inl m *
      (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))⁻¹ = _
  rw [SemidirectProduct.inl_aut, map_inv]

/-- The shifted image of a masked configuration is already masked: shifting
right moves the support from `[0,∞)` into `[1,∞)`. -/
theorem mask_shift_mask (f : Lamp) :
    mask (shift (Multiplicative.ofAdd (1 : ℤ)) (mask f))
      = shift (Multiplicative.ofAdd (1 : ℤ)) (mask f) := by
  funext n
  simp only [mask_apply, shift_apply, toAdd_ofAdd]
  by_cases h : (0:ℤ) ≤ n
  · simp [h]
  · have h3 : ¬ ((0:ℤ) ≤ n - 1) := by omega
    simp [h, h3]

/-- **The compression.**  The stable letter carries the image of `iota` into
itself. -/
theorem stable_compresses (f : Lamp) :
    stable * iota f * stable⁻¹
      = iota (shift (Multiplicative.ofAdd (1 : ℤ)) (mask f)) := by
  simp only [iota_apply]
  rw [stable_conj, mask_shift_mask]

/-- The transported root: the root lamp moved from site `-1` to site `0`. -/
def transportedRoot : Skeleton := SemidirectProduct.inl (lamp 0 cx)

/-- The compressed copy is trivial at site `0`, which is where the transported
root lives.  This is condition (M2) of the pattern. -/
theorem shift_mask_zero (f : Lamp) :
    (shift (Multiplicative.ofAdd (1 : ℤ)) (mask f)) 0 = 1 := by
  simp only [shift_apply, mask_apply, toAdd_ofAdd]
  norm_num

/-- **Centralization.**  The transported root commutes with every conjugate of
the compressed copy: the conjugate is trivial at site `0`, which is the only
site the transported root occupies.  This is condition (M2). -/
theorem transportedRoot_commutes (f : Lamp) :
    Commute transportedRoot (stable * iota f * stable⁻¹) := by
  rw [stable_compresses, iota_apply, mask_shift_mask]
  show SemidirectProduct.inl (lamp 0 cx) *
      SemidirectProduct.inl (shift (Multiplicative.ofAdd (1 : ℤ)) (mask f))
      = SemidirectProduct.inl (shift (Multiplicative.ofAdd (1 : ℤ)) (mask f)) *
        SemidirectProduct.inl (lamp 0 cx)
  rw [← map_mul, ← map_mul]
  exact congrArg SemidirectProduct.inl (commute_lamp (shift_mask_zero f)).eq

/-- **The marked commutator, computed.**  Every defect generator is a single
lamp at site `0`, carrying a commutator of the coefficient group. -/
theorem commutator_transportedRoot (f : Lamp) :
    ⁅transportedRoot, iota f⁆
      = SemidirectProduct.inl (lamp 0 ⁅cx, f 0⁆) := by
  have h0 : mask f 0 = f 0 := by simp
  show ⁅SemidirectProduct.inl (lamp 0 cx),
      SemidirectProduct.inl (mask f)⁆ = _
  rw [← map_commutatorElement, commutator_lamp, h0]

/-! ## The certificates -/

/-- The free generators do not commute.  A kernel computation on reduced
words. -/
theorem commutator_cx_cy_ne_one : ⁅cx, cy⁆ ≠ 1 := by decide

/-- **The non-commuting pair, at the level of coefficients.**  `[x,y]` and
`[x,y²]` do not commute in a free group of rank two: they are cyclically
reduced of lengths four and six, so a common root would have length dividing
two, and no such root exists.  Here it is a kernel computation. -/
theorem commutator_pair_ne_one : ⁅⁅cx, cy⁆, ⁅cx, cy * cy⁆⁆ ≠ 1 := by decide

/-! ## The compression datum and its defect -/

open ConcreteCompressionSource

/-- **The explicit compression source datum.**  No property `(T)`, no simple
subgroup, and --- unlike every other datum in this development --- no
hypotheses: every field is a theorem proved above. -/
def explicitDatum : CompressionSourceData Lamp Skeleton where
  iota := iota
  u := stable
  s := transportedRoot
  compresses := fun f =>
    ⟨shift (Multiplicative.ofAdd (1 : ℤ)) (mask f), stable_compresses f⟩
  commutesAfterCompression := transportedRoot_commutes
  witness := lamp 0 cy
  witness_commutator_ne_one := by
    rw [commutator_transportedRoot]
    intro h
    apply commutator_cx_cy_ne_one
    have h1 : lamp 0 ⁅cx, (lamp 0 cy) 0⁆ = 1 :=
      SemidirectProduct.inl_injective (by rw [h, map_one])
    rw [lamp_eq_one_iff, lamp_self] at h1
    exact h1

@[simp] theorem explicitDatum_s : explicitDatum.s = transportedRoot := rfl

@[simp] theorem explicitDatum_iota : explicitDatum.iota = iota := rfl

end ExplicitSuitableDefect

/-! ## The defect of a compression source datum -/

namespace ConcreteCompressionSource
namespace CompressionSourceData

variable {P : Type} {E : Type u} [Group P] [Group E]

/-- The compression defect of a source datum: the normal closure of the marked
commutators.  Property `(T)` of the source is what the analytic theorem
consumes, not what defines the defect, so this is stated for a datum with no
Kazhdan field; `defectNormal_eq_core` records that under `(T)` it is literally
`KazhdanCompressionCore.defectNormal`. -/
def defectNormal (d : CompressionSourceData P E) : Subgroup E :=
  Subgroup.normalClosure (Set.range fun p : P ↦ ⁅d.s, d.iota p⁆)

instance defectNormal_normal (d : CompressionSourceData P E) :
    (d.defectNormal).Normal :=
  Subgroup.normalClosure_normal

/-- Every marked commutator lies in the defect. -/
theorem generator_mem_defectNormal (d : CompressionSourceData P E) (p : P) :
    ⁅d.s, d.iota p⁆ ∈ d.defectNormal :=
  Subgroup.subset_normalClosure ⟨p, rfl⟩

/-- Under property `(T)` of the source this is the marker-free core's defect,
so nothing about the notion has been changed by dropping the Kazhdan field. -/
theorem defectNormal_eq_core (d : CompressionSourceData P E)
    (hT : HasKazhdanPropertyT.{0, 0} P) :
    d.defectNormal = (d.core hT).defectNormal :=
  (d.core_defectNormal_eq hT).symm

end CompressionSourceData
end ConcreteCompressionSource

namespace ExplicitSuitableDefect

open ConcreteCompressionSource
open HullSuitable

/-! ## The object -/

/-- The first of the two chosen defect generators. -/
def defectOne : Skeleton := ⁅explicitDatum.s, explicitDatum.iota (lamp 0 cy)⁆

/-- The second of the two chosen defect generators. -/
def defectTwo : Skeleton :=
  ⁅explicitDatum.s, explicitDatum.iota (lamp 0 (cy * cy))⁆

theorem defectOne_mem : defectOne ∈ explicitDatum.defectNormal :=
  explicitDatum.generator_mem_defectNormal _

theorem defectTwo_mem : defectTwo ∈ explicitDatum.defectNormal :=
  explicitDatum.generator_mem_defectNormal _

theorem defectOne_eq : defectOne = SemidirectProduct.inl (lamp 0 ⁅cx, cy⁆) := by
  show ⁅transportedRoot, iota (lamp 0 cy)⁆ = _
  rw [commutator_transportedRoot, lamp_self]

theorem defectTwo_eq :
    defectTwo = SemidirectProduct.inl (lamp 0 ⁅cx, cy * cy⁆) := by
  show ⁅transportedRoot, iota (lamp 0 (cy * cy))⁆ = _
  rw [commutator_transportedRoot, lamp_self]

/-- **The compression defect is not commutative.**  The two chosen generators
reduce to `[x,y]` and `[x,y²]` at site `0`, and those do not commute. -/
theorem defect_noncommuting : ⁅defectOne, defectTwo⁆ ≠ 1 := by
  rw [defectOne_eq, defectTwo_eq, ← map_commutatorElement, commutator_lamp,
    lamp_self]
  intro h
  apply commutator_pair_ne_one
  have h1 : lamp 0 ⁅⁅cx, cy⁆, ⁅cx, cy * cy⁆⁆ = 1 :=
    SemidirectProduct.inl_injective (by rw [h, map_one])
  rwa [lamp_eq_one_iff] at h1

/-- **The suitable subgroup inside the compression defect, unconditionally.**

This term takes no arguments.  Every clause of Hull's suitability that is group
theory --- Definition 1.4(3), and the non-geometric hypotheses of Lemma 5.8 ---
holds of it, and nothing anywhere in its construction is assumed: the ambient
group is built, its torsion-freeness is proved, the compression datum is built,
and the non-commuting pair inside the defect is exhibited and certified. -/
def explicitSuitableDefectSubgroup :
    SuitableDefectSubgroup explicitDatum.defectNormal :=
  SuitableDefectSubgroup.ofNoncommutingPair explicitDatum.defectNormal
    skeleton_isPowerTorsionFree defectOne_mem defectTwo_mem defect_noncommuting

/-- The object is two-generated by the two marked commutators. -/
@[simp] theorem explicitSuitableDefectSubgroup_carrier :
    explicitSuitableDefectSubgroup.carrier =
      Subgroup.closure ({defectOne, defectTwo} : Set Skeleton) :=
  rfl

/-- **Existence, with no hypotheses.**  There is a compression source datum
whose defect contains an algebraically suitable subgroup.  Stated as a bare
existential so that the absence of hypotheses is visible in the type. -/
theorem exists_isAlgebraicallySuitable_le_defectNormal :
    ∃ S : Subgroup Skeleton,
      S ≤ explicitDatum.defectNormal ∧ IsAlgebraicallySuitable S :=
  ⟨explicitSuitableDefectSubgroup.carrier,
    explicitSuitableDefectSubgroup.le_defect,
    explicitSuitableDefectSubgroup.suitable⟩

/-- **Nothing is left as a hypothesis.**  The two clauses of algebraic
suitability, spelled out at the explicit subgroup, with the ambient group, the
datum, the defect and the subgroup all constructed above. -/
theorem explicit_normalizes_no_nontrivial_finite :
    NormalizesNoNontrivialFinite explicitSuitableDefectSubgroup.carrier :=
  explicitSuitableDefectSubgroup.suitable.normalizes_no_nontrivial_finite

theorem explicit_exists_proper_infiniteOrder :
    ∃ h ∈ explicitSuitableDefectSubgroup.carrier,
      ¬ IsOfFinOrder h ∧
        Subgroup.zpowers h < explicitSuitableDefectSubgroup.carrier :=
  explicitSuitableDefectSubgroup.suitable.exists_proper_infiniteOrder

theorem explicit_infinite : Infinite explicitSuitableDefectSubgroup.carrier :=
  explicitSuitableDefectSubgroup.suitable.infinite

end ExplicitSuitableDefect
end GroupApproximation
