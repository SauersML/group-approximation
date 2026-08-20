import GroupApproximation.Algebra.FreeProductCyclicWord

/-!
# Killing normal subgroups of the factors of a free product

A free product modulo relators taken *inside the factors* is the free product
of the quotient factors:

```text
    (∗ᵢ Gᵢ) / ⟪⋃ᵢ Nᵢ⟫  ≃*  ∗ᵢ (Gᵢ / Nᵢ).
```

Both sides classify the same homomorphisms — a map out of either is a family
of maps `Gᵢ → P` killing `Nᵢ` — so the isomorphism is two applications of
`Monoid.CoprodI.lift` and `QuotientGroup.lift` and two round trips.

## What it is for

It is the nondegenerate instance of Osin's conclusion pair.  The quotient of
`U * H` by a family of relators drawn from the factors keeps `U` embedded
whenever the peripheral component `N_U` is trivial (`peripheral_injective`),
and it stays torsion-free whenever the quotient factors are
(`isPowerTorsionFree_quotient`, through `FreeProductCyclic`).  Neither clause
is assumed: both are proved, for every such relator family.

That this is *not* a small-cancellation family is the point.  A relator of
syllable length one violates every metric condition, so the family sits at the
opposite end of the range from the `C'(1/6)` families Osin's theorem is stated
for, and the two conclusions hold there anyway and for a different reason.
What it buys is that the conclusion list of
`Sofic.OsinRelativeSmallCancellation` is inhabited by something other than the
empty relator family, so no statement downstream of it is vacuous.
-/

namespace GroupApproximation
namespace FreeProductFactorQuotient

open Monoid Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
  (N : ∀ i, Subgroup (G i)) [∀ i, (N i).Normal]

/-- The relators: every element of every `N i`, read inside the free
product. -/
def factorRelators : Set (CoprodI G) :=
  ⋃ i, (CoprodI.of : G i →* CoprodI G) '' (N i : Set (G i))

/-- The normal subgroup they generate. -/
def factorNormal : Subgroup (CoprodI G) :=
  Subgroup.normalClosure (factorRelators N)

/-- Normality has to be *registered*: instance search does not unfold a plain
`def` to find `Subgroup.normalClosure_normal` behind it, and every quotient
below needs it to have a group structure at all. -/
instance factorNormal_normal : (factorNormal N).Normal :=
  Subgroup.normalClosure_normal

omit [∀ i, (N i).Normal] in
theorem of_mem_factorRelators {i : ι} {x : G i} (hx : x ∈ N i) :
    CoprodI.of x ∈ factorRelators N :=
  Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ hx⟩

omit [∀ i, (N i).Normal] in
theorem of_mem_factorNormal {i : ι} {x : G i} (hx : x ∈ N i) :
    CoprodI.of x ∈ factorNormal N :=
  Subgroup.subset_normalClosure (of_mem_factorRelators N hx)

/-! ## The two directions -/

/-- Free product of the quotient maps. -/
def toQuotients : CoprodI G →* CoprodI (fun i => G i ⧸ N i) :=
  CoprodI.lift fun i =>
    (CoprodI.of (M := fun j => G j ⧸ N j) (i := i)).comp
      (QuotientGroup.mk' (N i))

@[simp] theorem toQuotients_of {i : ι} (x : G i) :
    toQuotients N (CoprodI.of x)
      = CoprodI.of (M := fun j => G j ⧸ N j) (i := i)
          (QuotientGroup.mk x : G i ⧸ N i) := by
  simp [toQuotients]

theorem factorNormal_le_ker : factorNormal N ≤ (toQuotients N).ker := by
  apply Subgroup.normalClosure_le_normal
  intro y hy
  simp only [factorRelators, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe] at hy
  obtain ⟨i, x, hx, rfl⟩ := hy
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, toQuotients_of]
  rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]

/-- The induced map on the quotient. -/
def liftToQuotients :
    (CoprodI G ⧸ factorNormal N) →* CoprodI (fun i => G i ⧸ N i) :=
  QuotientGroup.lift _ (toQuotients N) (factorNormal_le_ker N)

@[simp] theorem liftToQuotients_mk (g : CoprodI G) :
    liftToQuotients N (QuotientGroup.mk g) = toQuotients N g :=
  QuotientGroup.lift_mk' _ _ g

/-- The map back: a factor of the quotient free product goes to the class of
that factor. -/
def ofQuotients :
    CoprodI (fun i => G i ⧸ N i) →* (CoprodI G ⧸ factorNormal N) :=
  CoprodI.lift fun i =>
    QuotientGroup.lift (N i)
      ((QuotientGroup.mk' (factorNormal N)).comp CoprodI.of)
      (by
        intro x hx
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply,
          QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr (of_mem_factorNormal N hx))

@[simp] theorem ofQuotients_of {i : ι} (x : G i) :
    ofQuotients N (CoprodI.of (QuotientGroup.mk x : G i ⧸ N i))
      = QuotientGroup.mk (CoprodI.of x) := by
  simp [ofQuotients]

/-- **A free product modulo relators inside its factors is the free product of
the quotient factors.** -/
def equivQuotients :
    (CoprodI G ⧸ factorNormal N) ≃* CoprodI (fun i => G i ⧸ N i) where
  toFun := liftToQuotients N
  invFun := ofQuotients N
  left_inv := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [liftToQuotients_mk]
    induction g using CoprodI.induction_on with
    | one => simp
    | of i m => simp
    | mul a b ha hb => simp [ha, hb]
  right_inv := by
    intro y
    induction y using CoprodI.induction_on with
    | one => simp
    | of i m =>
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective m
        simp
    | mul a b ha hb => simp [ha, hb]
  map_mul' := map_mul _

@[simp] theorem equivQuotients_mk (g : CoprodI G) :
    equivQuotients N (QuotientGroup.mk g) = toQuotients N g :=
  liftToQuotients_mk N g

@[simp] theorem equivQuotients_symm_apply
    (y : CoprodI (fun i => G i ⧸ N i)) :
    (equivQuotients N).symm y = ofQuotients N y := rfl

/-! ## The two clauses -/

/-- **The quotient stays torsion-free**, when the quotient factors are.  This
is `FreeProductCyclic.isPowerTorsionFree_coprodI` transported along the
isomorphism. -/
theorem isPowerTorsionFree_quotient
    (h : ∀ i, IsPowerTorsionFree (G i ⧸ N i)) :
    IsPowerTorsionFree (CoprodI G ⧸ factorNormal N) :=
  IsPowerTorsionFree.comap (FreeProductCyclic.isPowerTorsionFree_coprodI h)
    (equivQuotients N).toMonoidHom (equivQuotients N).injective

/-- **The peripheral factor stays embedded**, when nothing was killed inside
it. -/
theorem peripheral_injective (i₀ : ι) (h0 : N i₀ = ⊥) :
    Function.Injective
      (((QuotientGroup.mk' (factorNormal N)).comp CoprodI.of : G i₀ →* _)) := by
  have hmk : Function.Injective (QuotientGroup.mk' (N i₀)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', h0]
  intro x y hxy
  have h1 : toQuotients N (CoprodI.of x) = toQuotients N (CoprodI.of y) := by
    have h2 := congrArg (liftToQuotients N) hxy
    simpa using h2
  rw [toQuotients_of, toQuotients_of] at h1
  exact hmk (CoprodI.of_injective i₀ h1)

end FreeProductFactorQuotient
end GroupApproximation
