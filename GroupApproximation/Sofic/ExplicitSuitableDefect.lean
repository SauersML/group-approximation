import GroupApproximation.Sofic.HullSuitableDefectSubgroup
import GroupApproximation.Sofic.ConcreteCompressionSource
import GroupApproximation.GroupTheory.HNNBrittonCyclic
import GroupApproximation.Sofic.HullSuitabilityGeometry
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

## The same object in the manuscript's own shape

A semidirect product is the compression pattern in its simplest form, but the
manuscript's skeleton `E'` is an *ascending HNN extension*.  The last section
puts the object there too, inside the defect of `ConcreteCompressionSource`'s
own affine HNN source, and it is still unconditional:
`HNNBritton.isPowerTorsionFree_sourceGroup` proves an HNN extension over a
torsion-free base is torsion-free, outright, from Britton's lemma.

## What a compression datum forces

`CompressionSourceData.not_conjugation_surjective` (the compression is strictly
proper), `CompressionSourceData.infinite_source` (hence the source is infinite,
transported to `FournierFacioDefectData.infinite_source`), and
`CompressionSourceData.not_isSuitable_compressedCopy` (the compressed copy is
never Hull's suitable subgroup, because the transported root centralizes it).

## What this is and is not

It **is** an unconditional inhabitant of the object Hull's theorem takes as its
hypothesis: a subgroup of a genuine compression defect --- in the ascending HNN
shape as well as the semidirect one --- over a genuine ambient group,
satisfying every clause of suitability that is group theory.

It is **not** a step towards routing the Fournier--Facio group.  Neither ambient
has a Kazhdan source, and neither is known to be acylindrically hyperbolic, so
Hull's theorem does not apply to either and nothing here claims otherwise.  The
geometric clause is stated in `Sofic.HullSuitabilityGeometry`, and what is
settled here is that the algebraic half of the object needs no hypotheses: it
can be exhibited, in the manuscript's own skeleton shape.
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
    have h1 : lamp i a i = 1 := by rw [h]; rfl
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
  · have h1 : ¬ ((1:ℤ) ≤ n) := fun hn ↦ h (le_trans zero_le_one hn)
    simp [h, h1]

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

/-- The same computation with no mask in the way: a commutator against the
transported root is a single lamp at site `0`. -/
theorem commutator_transportedRoot_inl (m : Lamp) :
    ⁅transportedRoot, (SemidirectProduct.inl m : Skeleton)⁆
      = SemidirectProduct.inl (lamp 0 ⁅cx, m 0⁆) := by
  show ⁅SemidirectProduct.inl (lamp 0 cx), SemidirectProduct.inl m⁆ = _
  rw [← map_commutatorElement, commutator_lamp]

/-- Shifting the root lamp moves it from site `-1` to site `0`. -/
theorem shift_root :
    shift (Multiplicative.ofAdd (1 : ℤ)) (lamp (-1) cx) = lamp 0 cx := by
  funext n
  simp only [shift_apply, toAdd_ofAdd, lamp]
  by_cases hn : n = 0
  · rw [hn]
    norm_num
  · have h1 : n - 1 ≠ -1 := by omega
    rw [if_neg h1, if_neg hn]

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

/-! ### What a compression datum forces

Four theorems, all unconditional and all about an arbitrary datum over an
arbitrary group.  The first two say the interface is not satisfiable trivially;
the last says which subgroup of the pattern can possibly be Hull's suitable
one. -/

/-- **The compression is strictly proper.**  Conjugation by the stable letter
is not onto the source copy.  If it were, the transported root would centralize
the whole copy --- that is exactly what `commutesAfterCompression` says about
each conjugate --- and the marked commutator would be trivial. -/
theorem not_conjugation_surjective (d : CompressionSourceData P E) :
    ¬ ∀ p : P, ∃ q : P, d.u * d.iota q * d.u⁻¹ = d.iota p := by
  intro hsurj
  apply d.witness_commutator_ne_one
  obtain ⟨q, hq⟩ := hsurj d.witness
  rw [← hq]
  exact commutatorElement_eq_one_iff_commute.mpr (d.commutesAfterCompression q)

/-- **Hence the source is infinite.**  Conjugation by the stable letter maps the
source copy into itself and is injective; on a finite copy an injective self-map
is onto, which the previous theorem forbids.  So no compression datum has a
finite source, and in particular none is built over a finite group. -/
theorem infinite_source (d : CompressionSourceData P E) : Infinite P := by
  refine not_finite_iff_infinite.mp fun hP => ?_
  have hmaps : ∀ x : d.iota.range, d.u * (x : E) * d.u⁻¹ ∈ d.iota.range := by
    rintro ⟨x, p, rfl⟩
    obtain ⟨q, hq⟩ := d.compresses p
    exact ⟨q, hq.symm⟩
  haveI hfin : Finite d.iota.range :=
    Finite.of_surjective (fun p : P => (⟨d.iota p, ⟨p, rfl⟩⟩ : d.iota.range))
      (by rintro ⟨x, p, rfl⟩; exact ⟨p, rfl⟩)
  have hinj : Function.Injective
      (fun x : d.iota.range =>
        (⟨d.u * (x : E) * d.u⁻¹, hmaps x⟩ : d.iota.range)) := by
    intro x y hxy
    have h1 : d.u * (x : E) * d.u⁻¹ = d.u * (y : E) * d.u⁻¹ :=
      congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  refine d.not_conjugation_surjective fun p => ?_
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hinj
    (⟨d.iota p, ⟨p, rfl⟩⟩ : d.iota.range)
  obtain ⟨q, hq⟩ := x.2
  refine ⟨q, ?_⟩
  have h2 : d.u * (x : E) * d.u⁻¹ = d.iota p := congrArg Subtype.val hx
  rw [← hq] at h2
  exact h2

/-- The compressed copy `u ι(Γ) u⁻¹` of the datum. -/
def compressedCopy (d : CompressionSourceData P E) : Subgroup E :=
  Subgroup.map ((MulAut.conj d.u).toMonoidHom) d.iota.range

/-- The transported root centralizes the compressed copy.  This is
`commutesAfterCompression` read as a statement about a subgroup. -/
theorem commute_s_of_mem_compressedCopy (d : CompressionSourceData P E)
    {y : E} (hy : y ∈ d.compressedCopy) : Commute d.s y := by
  obtain ⟨z, ⟨p, rfl⟩, rfl⟩ := hy
  simpa using d.commutesAfterCompression p

/-- **The compressed copy is never Hull's suitable subgroup**, over a
torsion-free ambient and any geometry in which the transported root has a
bounded orbit.  The transported root is a nontrivial element centralizing the
whole copy, and `HullGeometry.not_isSuitable_of_centralizing` forbids that.

So the search for a suitable subgroup inside a compression pattern cannot stop
at the compressed copy: it has to go to the defect, which is where
`Sofic.HullSuitableDefectSubgroup` puts it. -/
theorem not_isSuitable_compressedCopy (d : CompressionSourceData P E)
    (htf : IsPowerTorsionFree E) {Y : Type u} [PseudoMetricSpace Y]
    [MulAction E Y] {delta B : ℝ} {y : Y}
    (hbdd : ∀ j : ℤ, dist y ((d.s ^ j) • y) ≤ B) :
    ¬ HullGeometry.IsSuitable delta d.compressedCopy y :=
  HullGeometry.not_isSuitable_of_centralizing htf d.s_ne_one
    (fun _ hz => d.commute_s_of_mem_compressedCopy hz) hbdd

end CompressionSourceData
end ConcreteCompressionSource

namespace FournierFacioDefectData

variable {P : Type} {E : Type u} [Group P] [Group E]

/-- **The Kazhdan source of a Fournier--Facio datum is infinite.**  So the
datum is never satisfiable over a finite Kazhdan group, and the property-`(T)`
source it asks for is an infinite one. -/
theorem infinite_source (D : FournierFacioDefectData P E) : Infinite P :=
  (ConcreteCompressionSource.ofFournierFacio D).infinite_source

/-- The compression of a Fournier--Facio datum is strictly proper as well. -/
theorem not_conjugation_surjective (D : FournierFacioDefectData P E) :
    ¬ ∀ p : P, ∃ q : P, D.u * D.iota q * D.u⁻¹ = D.iota p :=
  (ConcreteCompressionSource.ofFournierFacio D).not_conjugation_surjective

end FournierFacioDefectData

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


/-! ## The same object inside the genuine ascending HNN skeleton

The lamp group above is a semidirect product, which is the compression pattern
in its simplest form but not the manuscript's shape: the skeleton `E'` there is
an *ascending HNN extension*.  This section puts the object where it belongs,
inside the defect of `ConcreteCompressionSource`'s own affine HNN source, and it
is still unconditional --- `HNNBritton.isPowerTorsionFree_sourceGroup` supplies
torsion-freeness of an HNN extension over a torsion-free base, which that module
proves outright from Britton's lemma with no input.

The one thing the HNN group does not hand over cheaply is the non-commuting
pair: reading it off directly would mean a reduced word of sixteen syllables
with fifteen chain conditions.  It is not needed.  A homomorphism to the lamp
group carries the two marked commutators onto the two lamp commutators already
certified, and a pair whose image does not commute does not commute. -/

/-- Configurations of lamps on the nonnegative sites: the compressed source. -/
abbrev HalfLamp : Type := ℕ → Coeff

/-- Shifting a nonnegative-site configuration away from site `0`. -/
def halfShiftFun (f : HalfLamp) : HalfLamp
  | 0 => 1
  | (k + 1) => f k

/-- The shift, as an endomorphism. -/
def halfShift : HalfLamp →* HalfLamp where
  toFun := halfShiftFun
  map_one' := by funext n; cases n <;> simp [halfShiftFun]
  map_mul' f g := by funext n; cases n <;> simp [halfShiftFun]

@[simp] theorem halfShift_zero (f : HalfLamp) : halfShift f 0 = 1 := rfl

@[simp] theorem halfShift_succ (f : HalfLamp) (k : ℕ) :
    halfShift f (k + 1) = f k := rfl

theorem halfShift_injective : Function.Injective ⇑halfShift := by
  intro f g h
  funext n
  exact congrFun h (n + 1)

/-- A configuration visible at site `0`.  Everything in the shift's range is
trivial there, so this element is outside it --- which is exactly what the
affine HNN source needs to be nondegenerate. -/
def halfSeed : HalfLamp := fun n => if n = 0 then cx else 1

@[simp] theorem halfSeed_zero : halfSeed 0 = cx := rfl

/-- The first free generator is not the identity: a kernel computation. -/
theorem cx_ne_one : cx ≠ 1 := by decide

theorem halfSeed_notMem_range : halfSeed ∉ Set.range ⇑halfShift := by
  rintro ⟨f, hf⟩
  apply cx_ne_one
  have h0 : halfShift f 0 = halfSeed 0 := congrFun hf 0
  rw [halfShift_zero, halfSeed_zero] at h0
  exact h0.symm

/-! ### The HNN skeleton and its torsion-freeness -/

theorem halfLamp_isPowerTorsionFree : IsPowerTorsionFree HalfLamp :=
  isPowerTorsionFree_pi coeff_isPowerTorsionFree

theorem halfBase_isPowerTorsionFree :
    IsPowerTorsionFree (ConcreteCompressionSource.Base HalfLamp) :=
  halfLamp_isPowerTorsionFree.prod
    ConcreteCompressionSource.isPowerTorsionFree_multiplicative_int

/-- **The ascending HNN skeleton.**  The affine HNN extension of
`HalfLamp × ℤ` over the shift: `ConcreteCompressionSource`'s own generic
construction instantiated at a torsion-free source. -/
abbrev HnnSkeleton : Type :=
  ConcreteCompressionSource.SourceGroup halfShift halfShift_injective

/-- **The HNN skeleton is torsion-free**, by the repository's own HNN torsion
theorem.  No hypothesis: `HNNBritton.isPowerTorsionFree_sourceGroup` is
unconditional and the base is torsion-free by the two lemmas above. -/
theorem hnnSkeleton_isPowerTorsionFree : IsPowerTorsionFree HnnSkeleton :=
  HNNBritton.isPowerTorsionFree_sourceGroup halfShift halfShift_injective
    halfBase_isPowerTorsionFree

/-- **The HNN compression datum**, with no hypotheses: the generic affine
source at the shift of `ℕ`-indexed free-group lamps. -/
noncomputable def hnnDatum :
    ConcreteCompressionSource.CompressionSourceData HalfLamp HnnSkeleton :=
  ConcreteCompressionSource.sourceData halfShift halfShift_injective
    halfSeed_notMem_range

/-! ### The comparison homomorphism -/

/-- Place a nonnegative-site configuration into the ambient lamp group. -/
def place : HalfLamp →* Lamp where
  toFun f := fun n => if 0 ≤ n then f n.toNat else 1
  map_one' := by
    funext n
    by_cases h : (0:ℤ) ≤ n <;> simp [h]
  map_mul' f g := by
    funext n
    by_cases h : (0:ℤ) ≤ n <;> simp [h]

@[simp] theorem place_apply (f : HalfLamp) (n : ℤ) :
    place f n = if 0 ≤ n then f n.toNat else 1 := rfl

theorem place_zero (f : HalfLamp) : place f 0 = f 0 := by
  simp

theorem mask_place (f : HalfLamp) : mask (place f) = place f := by
  funext n
  by_cases h : (0:ℤ) ≤ n <;> simp [h]

/-- Placing commutes with the two shifts: this is the compression relation,
transported. -/
theorem shift_place (f : HalfLamp) :
    shift (Multiplicative.ofAdd (1 : ℤ)) (place f) = place (halfShift f) := by
  funext n
  simp only [shift_apply, toAdd_ofAdd, place_apply]
  by_cases h1 : (0:ℤ) ≤ n - 1
  · have h2 : (0:ℤ) ≤ n := by omega
    have h3 : n.toNat = (n - 1).toNat + 1 := by omega
    rw [if_pos h1, if_pos h2, h3, halfShift_succ]
  · by_cases h2 : (0:ℤ) ≤ n
    · have hn : n = 0 := by omega
      subst hn
      simp
    · rw [if_neg h1, if_neg h2]

/-- The base of the HNN skeleton, mapped to the lamp group: the source copy
goes to the nonnegative sites and the central direction to site `-1`. -/
def baseToLamp : ConcreteCompressionSource.Base HalfLamp →* Lamp where
  toFun b := fun n =>
    if 0 ≤ n then b.1 n.toNat
    else if n = -1 then cx ^ (Multiplicative.toAdd b.2) else 1
  map_one' := by
    funext n
    by_cases h : (0:ℤ) ≤ n
    · simp [h]
    · by_cases h2 : n = -1 <;> simp [h, h2]
  map_mul' b b' := by
    funext n
    by_cases h : (0:ℤ) ≤ n
    · simp [h]
    · by_cases h2 : n = -1
      · simp [h2, ← zpow_add]
      · simp [h, h2]

@[simp] theorem baseToLamp_apply (b : ConcreteCompressionSource.Base HalfLamp)
    (n : ℤ) :
    baseToLamp b n =
      if 0 ≤ n then b.1 n.toNat
      else if n = -1 then cx ^ (Multiplicative.toAdd b.2) else 1 := rfl

theorem baseToLamp_baseInl (f : HalfLamp) :
    baseToLamp (ConcreteCompressionSource.baseInl f) = place f := by
  funext n
  by_cases h : (0:ℤ) ≤ n
  · simp [h]
  · by_cases h2 : n = -1 <;> simp [h, h2]

theorem baseToLamp_cZ :
    baseToLamp (ConcreteCompressionSource.cZ (Γ := HalfLamp))
      = lamp (-1) cx := by
  funext n
  by_cases h : (0:ℤ) ≤ n
  · have h2 : n ≠ -1 := by omega
    simp [h, h2, lamp, ConcreteCompressionSource.cZ]
  · by_cases h2 : n = -1 <;>
      simp [h, h2, lamp, ConcreteCompressionSource.cZ]

/-- The base map into the skeleton. -/
def baseToSkeleton : ConcreteCompressionSource.Base HalfLamp →* Skeleton :=
  SemidirectProduct.inl.comp baseToLamp

@[simp] theorem baseToSkeleton_apply
    (b : ConcreteCompressionSource.Base HalfLamp) :
    baseToSkeleton b = SemidirectProduct.inl (baseToLamp b) := rfl

/-- The associated isomorphism of the affine source, on the nose. -/
theorem sourceEquiv_coe (f : HalfLamp) :
    ((ConcreteCompressionSource.sourceEquiv halfShift halfShift_injective
        ((MonoidHom.ofInjective
          (ConcreteCompressionSource.baseInl_injective (Γ := HalfLamp))) f) :
      ConcreteCompressionSource.sourceB halfShift) :
      ConcreteCompressionSource.Base HalfLamp)
      = ConcreteCompressionSource.baseInl (halfShift f) := by
  show ((((MonoidHom.ofInjective
      (ConcreteCompressionSource.baseInl_injective (Γ := HalfLamp))).symm.trans
      (MonoidHom.ofInjective
        (ConcreteCompressionSource.baseInlComp_injective halfShift
          halfShift_injective)))
      ((MonoidHom.ofInjective
        (ConcreteCompressionSource.baseInl_injective (Γ := HalfLamp))) f) :
      ConcreteCompressionSource.sourceB halfShift) :
      ConcreteCompressionSource.Base HalfLamp)
      = ConcreteCompressionSource.baseInl (halfShift f)
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MonoidHom.ofInjective_apply]
  rfl

/-- The condition Mathlib's `HNNExtension.lift` asks for. -/
theorem psi_condition (a : ConcreteCompressionSource.sourceA (Γ := HalfLamp)) :
    stable * baseToSkeleton (a : ConcreteCompressionSource.Base HalfLamp)
      = baseToSkeleton
          ((ConcreteCompressionSource.sourceEquiv halfShift
              halfShift_injective a :
              ConcreteCompressionSource.sourceB halfShift) :
            ConcreteCompressionSource.Base HalfLamp) * stable := by
  obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp a.2
  have ha : a = (MonoidHom.ofInjective
      (ConcreteCompressionSource.baseInl_injective (Γ := HalfLamp))) f := by
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply]
    exact hf.symm
  rw [ha, sourceEquiv_coe, MonoidHom.ofInjective_apply, baseToSkeleton_apply,
    baseToSkeleton_apply, baseToLamp_baseInl, baseToLamp_baseInl]
  have h := stable_conj (place f)
  rw [shift_place] at h
  rw [← h]
  group

/-- **The comparison homomorphism.**  It sends the stable letter to the lamp
group's stable letter and the base to the lamp configurations. -/
noncomputable def psi : HnnSkeleton →* Skeleton :=
  HNNExtension.lift baseToSkeleton stable psi_condition

@[simp] theorem psi_t : psi HNNExtension.t = stable :=
  HNNExtension.lift_t _ _ _

@[simp] theorem psi_of (b : ConcreteCompressionSource.Base HalfLamp) :
    psi (HNNExtension.of b) = baseToSkeleton b :=
  HNNExtension.lift_of _ _ _ _

theorem psi_s : psi hnnDatum.s = transportedRoot := by
  show psi (HNNExtension.t * HNNExtension.of ConcreteCompressionSource.cZ *
      HNNExtension.t⁻¹) = SemidirectProduct.inl (lamp 0 cx)
  rw [map_mul, map_mul, map_inv, psi_t, psi_of, baseToSkeleton_apply,
    baseToLamp_cZ, stable_conj, shift_root]

theorem psi_iota (f : HalfLamp) :
    psi (hnnDatum.iota f) = SemidirectProduct.inl (place f) := by
  show psi (HNNExtension.of (ConcreteCompressionSource.baseInl f))
      = SemidirectProduct.inl (place f)
  rw [psi_of, baseToSkeleton_apply, baseToLamp_baseInl]

/-- The image of a marked commutator of the HNN datum is the corresponding
marked commutator of the lamp datum. -/
theorem psi_marked (f : HalfLamp) :
    psi ⁅hnnDatum.s, hnnDatum.iota f⁆
      = SemidirectProduct.inl (lamp 0 ⁅cx, f 0⁆) := by
  rw [map_commutatorElement, psi_s, psi_iota, commutator_transportedRoot_inl,
    place_zero]

/-! ### The object in the HNN defect -/

/-- The first chosen source element: the lamp `y` at site `0`. -/
def hnnGenOne : HalfLamp := fun n => if n = 0 then cy else 1

/-- The second chosen source element: the lamp `y²` at site `0`. -/
def hnnGenTwo : HalfLamp := fun n => if n = 0 then cy * cy else 1

@[simp] theorem hnnGenOne_zero : hnnGenOne 0 = cy := rfl

@[simp] theorem hnnGenTwo_zero : hnnGenTwo 0 = cy * cy := rfl

/-- **The HNN compression defect is not commutative.**  Its two marked
commutators map to the two lamp commutators already certified, so they cannot
commute.  No word combinatorics is needed. -/
theorem hnn_defect_noncommuting :
    ⁅⁅hnnDatum.s, hnnDatum.iota hnnGenOne⁆,
      ⁅hnnDatum.s, hnnDatum.iota hnnGenTwo⁆⁆ ≠ 1 := by
  intro h
  apply defect_noncommuting
  have h2 : psi ⁅⁅hnnDatum.s, hnnDatum.iota hnnGenOne⁆,
      ⁅hnnDatum.s, hnnDatum.iota hnnGenTwo⁆⁆ = 1 := by
    rw [h, map_one]
  rw [map_commutatorElement, psi_marked, psi_marked, hnnGenOne_zero,
    hnnGenTwo_zero, ← defectOne_eq, ← defectTwo_eq] at h2
  exact h2

/-- **The suitable subgroup inside the compression defect of an ascending HNN
skeleton, unconditionally.**

This is the previous object moved to the shape the manuscript's skeleton
actually has.  It still takes no arguments: the skeleton is the repository's own
affine HNN source, its torsion-freeness is the repository's own HNN torsion
theorem, the datum is the repository's own `sourceData`, and the non-commuting
pair is transported along `psi` from the lamp computation. -/
noncomputable def hnnSuitableDefectSubgroup :
    SuitableDefectSubgroup hnnDatum.defectNormal :=
  SuitableDefectSubgroup.ofNoncommutingPair hnnDatum.defectNormal
    hnnSkeleton_isPowerTorsionFree
    (hnnDatum.generator_mem_defectNormal hnnGenOne)
    (hnnDatum.generator_mem_defectNormal hnnGenTwo)
    hnn_defect_noncommuting

/-- Existence in the HNN skeleton, with no hypotheses. -/
theorem exists_isAlgebraicallySuitable_le_hnnDefectNormal :
    ∃ S : Subgroup HnnSkeleton,
      S ≤ hnnDatum.defectNormal ∧ IsAlgebraicallySuitable S :=
  ⟨hnnSuitableDefectSubgroup.carrier, hnnSuitableDefectSubgroup.le_defect,
    hnnSuitableDefectSubgroup.suitable⟩


/-! ## The defect is finitely supported, and always centralized

`Sofic.HullSuitabilityGeometry` proves that a subgroup with a nontrivial
centralizing element of *bounded orbit* is never suitable.  To point that at the
compression defect one needs a nontrivial element commuting with any two given
defect elements, and that is what this section supplies: every element of the
defect is a lamp configuration with finite support, so some site is free, and the
lamp at a free site commutes with both.

The conclusion, `unbounded_of_isSuitable`, is the exact remaining gap made
concrete: if the explicit defect were suitable, the commuting lamp it always
carries would have to have an unbounded orbit. -/

/-- The set of sites where a configuration is nontrivial. -/
def support (f : Lamp) : Set ℤ := {n : ℤ | f n ≠ 1}

theorem mem_support_iff {f : Lamp} {n : ℤ} : n ∈ support f ↔ f n ≠ 1 := Iff.rfl

theorem support_one : support (1 : Lamp) = ∅ := by
  ext n
  simp [support]

theorem support_mul (f g : Lamp) : support (f * g) ⊆ support f ∪ support g := by
  intro n hn
  by_contra hcon
  simp only [Set.mem_union, mem_support_iff, not_or, not_not] at hcon
  exact hn (show f n * g n = 1 by rw [hcon.1, hcon.2, one_mul])

theorem support_inv (f : Lamp) : support f⁻¹ = support f := by
  ext n
  constructor
  · intro hn hcon
    exact hn (show (f n)⁻¹ = 1 by rw [show f n = 1 from hcon]; simp)
  · intro hn hcon
    exact hn (by simpa using congrArg (fun z : Coeff => z⁻¹) hcon)

theorem support_conj (a f : Lamp) : support (a * f * a⁻¹) = support f := by
  ext n
  constructor
  · intro hn hcon
    exact hn (show a n * f n * (a n)⁻¹ = 1 by
      rw [show f n = 1 from hcon, mul_one, mul_inv_cancel])
  · intro hn hcon
    refine hn ?_
    have h : a n * f n * (a n)⁻¹ = 1 := hcon
    have h2 : f n = (a n)⁻¹ * (a n * f n * (a n)⁻¹) * (a n) := by group
    rw [h] at h2
    simpa using h2

theorem support_shift (k : Multiplicative ℤ) (f : Lamp) :
    support (shift k f)
      = (fun n : ℤ => n + Multiplicative.toAdd k) '' support f := by
  ext n
  constructor
  · intro hn
    refine ⟨n - Multiplicative.toAdd k, ?_, by ring⟩
    exact hn
  · rintro ⟨m, hm, rfl⟩
    show f (m + Multiplicative.toAdd k - Multiplicative.toAdd k) ≠ 1
    simpa [support] using hm

theorem finite_support_shift {k : Multiplicative ℤ} {f : Lamp}
    (hf : (support f).Finite) : (support (shift k f)).Finite := by
  rw [support_shift]
  exact hf.image _

/-! ### The subgroup of finitely supported lamps -/

/-- The elements of the skeleton that are lamp configurations of finite
support.  It is normal: conjugating translates and relabels supports. -/
def finSupp : Subgroup Skeleton where
  carrier := {g : Skeleton | g.right = 1 ∧ (support g.left).Finite}
  one_mem' := by
    refine ⟨rfl, ?_⟩
    show (support (1 : Lamp)).Finite
    rw [support_one]
    exact Set.finite_empty
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    have hleft : (a * b).left = a.left * b.left := by
      simp [SemidirectProduct.mul_left, ha1]
    refine ⟨by simp [SemidirectProduct.mul_right, ha1, hb1], ?_⟩
    rw [hleft]
    exact Set.Finite.subset (ha2.union hb2) (support_mul _ _)
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have hleft : a⁻¹.left = a.left⁻¹ := by
      simp [SemidirectProduct.inv_left, ha1]
    refine ⟨by simp [SemidirectProduct.inv_right, ha1], ?_⟩
    rw [hleft, support_inv]
    exact ha2

theorem mem_finSupp_iff (g : Skeleton) :
    g ∈ finSupp ↔ g.right = 1 ∧ (support g.left).Finite := Iff.rfl

instance finSupp_normal : finSupp.Normal := by
  constructor
  rintro n ⟨hn1, hn2⟩ g
  have hright : (g * n * g⁻¹).right = 1 := by
    simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hn1]
  have hcancel : ∀ m : Lamp, (shift g.right) ((shift g.right⁻¹) m) = m := by
    intro m
    rw [map_inv]
    exact MulEquiv.apply_symm_apply (shift g.right) m
  have hleft : (g * n * g⁻¹).left
      = g.left * (shift g.right n.left) * g.left⁻¹ := by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
      SemidirectProduct.mul_right, hn1, mul_one]
    rw [hcancel]
  refine ⟨hright, ?_⟩
  rw [hleft, support_conj]
  exact finite_support_shift hn2

/-- Every marked commutator is a single lamp, hence finitely supported. -/
theorem generator_mem_finSupp (f : Lamp) :
    ⁅transportedRoot, iota f⁆ ∈ finSupp := by
  rw [commutator_transportedRoot]
  refine ⟨rfl, ?_⟩
  show (support (lamp 0 ⁅cx, f 0⁆)).Finite
  refine Set.Finite.subset (Set.finite_singleton (0:ℤ)) ?_
  intro n hn
  by_contra hcon
  exact hn (lamp_of_ne hcon _)

/-- **The compression defect consists of finitely supported configurations.** -/
theorem defectNormal_le_finSupp : explicitDatum.defectNormal ≤ finSupp := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro y ⟨f, rfl⟩
  exact generator_mem_finSupp f

/-! ### A nontrivial commuting lamp always exists -/

/-- A lamp at a site outside the support of a finitely supported element
commutes with it. -/
theorem commute_lamp_of_notMem_support {m : ℤ} {a : Coeff} {g : Skeleton}
    (hg : g ∈ finSupp) (hm : m ∉ support g.left) :
    Commute (SemidirectProduct.inl (lamp m a)) g := by
  obtain ⟨hg1, -⟩ := hg
  have hgeq : g = SemidirectProduct.inl g.left :=
    SemidirectProduct.ext (by simp) (by simp [hg1])
  have hzero : g.left m = 1 := by
    by_contra hcon
    exact hm hcon
  have hcomm := (commute_lamp (i := m) (a := a) hzero).eq
  rw [hgeq]
  show SemidirectProduct.inl (lamp m a) * SemidirectProduct.inl g.left
      = SemidirectProduct.inl g.left * SemidirectProduct.inl (lamp m a)
  rw [← map_mul, ← map_mul, hcomm]

/-- **Any two elements of the compression defect are centralized by a
nontrivial lamp.**  Their supports are finite, so some site is free of both, and
the lamp there commutes with each. -/
theorem exists_commuting_ne_one {g h : Skeleton}
    (hg : g ∈ explicitDatum.defectNormal)
    (hh : h ∈ explicitDatum.defectNormal) :
    ∃ c : Skeleton, c ≠ 1 ∧ Commute c g ∧ Commute c h := by
  have hgf := defectNormal_le_finSupp hg
  have hhf := defectNormal_le_finSupp hh
  have hgs : (support g.left).Finite := hgf.2
  have hhs : (support h.left).Finite := hhf.2
  obtain ⟨m, hm⟩ := (hgs.union hhs).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hm
  refine ⟨SemidirectProduct.inl (lamp m cx), ?_,
    commute_lamp_of_notMem_support hgf hm.1,
    commute_lamp_of_notMem_support hhf hm.2⟩
  intro hcon
  refine cx_ne_one ?_
  have h1 : lamp m cx = 1 := SemidirectProduct.inl_injective (by
    rw [hcon, map_one])
  rwa [lamp_eq_one_iff] at h1

/-- **The remaining gap, made concrete.**  If the explicit compression defect
were suitable for some action, the nontrivial lamp that always commutes with the
two witnessing loxodromics would have to have an unbounded orbit.

`HullGeometry.eq_one_of_commutes_of_bounded` forbids a bounded one, and
`exists_commuting_ne_one` says such a lamp always exists.  So a suitable
geometry for this defect is not merely unproved: it must place every free-site
lamp at unbounded distance from the basepoint, which is exactly what Osin's
elementary-closure theorem is expected to forbid. -/
theorem unbounded_of_isSuitable {Y : Type u} [PseudoMetricSpace Y]
    [MulAction Skeleton Y] {delta : ℝ} {y : Y}
    (hs : HullGeometry.IsSuitable delta explicitDatum.defectNormal y) :
    ∃ c : Skeleton, c ≠ 1 ∧
      ∀ B : ℝ, ¬ ∀ j : ℤ, dist y ((c ^ j) • y) ≤ B := by
  obtain ⟨g, hgS, h, hhS, hg, hh, hind⟩ := hs.nonElementary
  obtain ⟨c, hc, hcg, hch⟩ := exists_commuting_ne_one hgS hhS
  refine ⟨c, hc, fun B hbdd => hc ?_⟩
  exact HullGeometry.eq_one_of_commutes_of_bounded hs.isometric hs.acylindrical
    skeleton_isPowerTorsionFree hg hh hind hcg hch hbdd

end ExplicitSuitableDefect
end GroupApproximation
