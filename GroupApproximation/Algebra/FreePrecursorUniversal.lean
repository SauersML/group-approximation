import GroupApproximation.Algebra.FreePermutationalPrecursor
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The universal property of the free permutational precursor

Equation (54.17) presents the free precursor
`E = (∗_{x ∈ G/Γ} K_x) ⋊ G` on the generators of `G` together with the
generators of a *single* lamp, subject to the relations of `G`, the relations of
`K`, and one commutation relation per generator of the stabiliser `Γ`:

  `E ≅ ⟨S, A | R_G, R_K, [u, a] = 1  (u ∈ U, a ∈ A)⟩`.

A presentation on finitely many generators is available at all -- despite the
lamp subgroup being an infinite free product -- because `G` acts transitively on
the sites.  Every lamp is a `G`-conjugate of the one at the base site, and the
only relations needed to make those conjugates well defined say that the
stabiliser of the base site commutes with the base lamp.

This file proves the statement carrying all of that: the universal property.

## The statement

To give a homomorphism `E → H` is to give `φ : G →* H` and `ψ : K →* H` whose
image is centralised by `φ(Γ)`.  Nothing else is required, and the resulting map
is determined by its values on `G` and on the base lamp.

The construction is forced.  A lamp at the coset `gΓ` must go to
`φ(g) ψ(k) φ(g)⁻¹`.  That is well defined exactly when changing the
representative by an element of `Γ` leaves the answer alone, which is the
centralising hypothesis and nothing more (`siteHomAux_congr`).  The free product
assembles the per-site maps with no further condition, because a free product
imposes none; the semidirect product needs only that the assembled map
intertwines the site permutation with conjugation, which holds because the
per-site maps are themselves conjugation-equivariant (`siteHom_smul`).

## What this gives, and what it does not

`precursorLift` is existence and `precursorLift_unique` is uniqueness.  Together
they identify `E` with the group presented by (54.17): a presented group has the
same universal property by construction, so the two receive the same maps into
every group and are therefore isomorphic.  Assembling that comparison against
Mathlib's `PresentedGroup` is the remaining step for Lemma 54.3, and it is
bookkeeping about one specific relator set rather than further theory.

Neither `K` nor `G` need be finitely generated here; those hypotheses enter only
when counting the generators of the presentation.
-/

namespace GroupApproximation

namespace FreePrecursor

universe u v w

open Monoid.CoprodI

variable {K : Type u} [Group K] {G : Type w} [Group G] {H : Type v} [Group H]

/-! ## The lamp map attached to a site -/

section SiteHom

variable (Γ : Subgroup G) (φ : G →* H) (ψ : K →* H)

/-- The lamp map attached to a coset representative: the base lamp conjugated
by the image of that representative. -/
def siteHomAux (g : G) : K →* H :=
  ((MulAut.conj (φ g)).toMonoidHom).comp ψ

@[simp] theorem siteHomAux_apply (g : G) (k : K) :
    siteHomAux φ ψ g k = φ g * ψ k * (φ g)⁻¹ := rfl

/-- **Well-definedness.**  Changing the coset representative by an element of the
stabiliser leaves the lamp map alone, provided `φ(Γ)` centralises `ψ(K)`.  That
single hypothesis is the whole content of the commutation relations of
(54.17). -/
theorem siteHomAux_congr
    (hcomm : ∀ u ∈ Γ, ∀ k : K, φ u * ψ k = ψ k * φ u)
    {a b : G} (hab : a⁻¹ * b ∈ Γ) :
    siteHomAux φ ψ a = siteHomAux φ ψ b := by
  refine MonoidHom.ext fun k => ?_
  have hcomm' : φ (a⁻¹ * b) * ψ k = ψ k * φ (a⁻¹ * b) := hcomm _ hab k
  rw [map_mul, map_inv] at hcomm'
  show φ a * ψ k * (φ a)⁻¹ = φ b * ψ k * (φ b)⁻¹
  have hb : φ b = φ a * ((φ a)⁻¹ * φ b) := by group
  rw [hb]
  calc φ a * ψ k * (φ a)⁻¹
      = φ a * (ψ k * ((φ a)⁻¹ * φ b)) * ((φ a)⁻¹ * φ b)⁻¹ * (φ a)⁻¹ := by group
    _ = φ a * (((φ a)⁻¹ * φ b) * ψ k) * ((φ a)⁻¹ * φ b)⁻¹ * (φ a)⁻¹ := by
        rw [hcomm']
    _ = φ a * ((φ a)⁻¹ * φ b) * ψ k * (φ a * ((φ a)⁻¹ * φ b))⁻¹ := by group

variable (hcomm : ∀ u ∈ Γ, ∀ k : K, φ u * ψ k = ψ k * φ u)

include hcomm

/-- The lamp map attached to a site of `G ⧸ Γ`. -/
def siteHom : G ⧸ Γ → (K →* H) := fun x =>
  Quotient.liftOn' x (siteHomAux φ ψ) fun _ _ hab =>
    siteHomAux_congr Γ φ ψ hcomm (QuotientGroup.leftRel_apply.mp hab)

@[simp] theorem siteHom_mk (g : G) :
    siteHom Γ φ ψ hcomm (QuotientGroup.mk g) = siteHomAux φ ψ g := rfl

/-- **Conjugation-equivariance.**  Translating a site by `g` conjugates its lamp
map by `φ g`.  This is what lets the assembled map extend across the semidirect
product. -/
theorem siteHom_smul (g : G) (x : G ⧸ Γ) :
    siteHom Γ φ ψ hcomm (g • x)
      = ((MulAut.conj (φ g)).toMonoidHom).comp (siteHom Γ φ ψ hcomm x) := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    refine MonoidHom.ext fun k => ?_
    show siteHomAux φ ψ (g * a) k = φ g * (siteHomAux φ ψ a k) * (φ g)⁻¹
    rw [siteHomAux_apply, siteHomAux_apply, map_mul]
    group

end SiteHom


/-! ## The lift -/

section Lift

variable (Γ : Subgroup G) (φ : G →* H) (ψ : K →* H)
variable (hcomm : ∀ u ∈ Γ, ∀ k : K, φ u * ψ k = ψ k * φ u)

include hcomm

/-- The assembled map on the free lamp group: a free product imposes no
relations, so the per-site maps glue with nothing to check. -/
def lampLift : FreeLamp K (G ⧸ Γ) →* H :=
  Monoid.CoprodI.lift (siteHom Γ φ ψ hcomm)

@[simp] theorem lampLift_of (x : G ⧸ Γ) (k : K) :
    lampLift Γ φ ψ hcomm (Monoid.CoprodI.of (M := fun _ : G ⧸ Γ => K) (i := x) k)
      = siteHom Γ φ ψ hcomm x k := by
  simp [lampLift]

/-- The assembled map intertwines the site permutation with conjugation, which
is exactly the hypothesis the semidirect product needs. -/
theorem lampLift_equivariant (g : G) :
    (lampLift Γ φ ψ hcomm).comp
        (freeLampActionHom K (G ⧸ Γ) g).toMonoidHom
      = ((MulAut.conj (φ g)).toMonoidHom).comp (lampLift Γ φ ψ hcomm) := by
  refine Monoid.CoprodI.ext_hom _ _ fun x => ?_
  refine MonoidHom.ext fun k => ?_
  show lampLift Γ φ ψ hcomm
      (freeLampMap K (G ⧸ Γ) g (Monoid.CoprodI.of (i := x) k))
    = φ g * lampLift Γ φ ψ hcomm (Monoid.CoprodI.of (i := x) k) * (φ g)⁻¹
  rw [freeLampMap, Monoid.CoprodI.lift_of, lampLift_of, lampLift_of,
    siteHom_smul Γ φ ψ hcomm g x]
  rfl

/-- **The universal property of the free precursor (54.17), existence half.**
A homomorphism out of `G`, and one out of `K` whose image is centralised by the
stabiliser, assemble into a homomorphism out of `E`.  No other condition
appears, which is why the presentation needs only the relations of `G`, those of
`K`, and one commutator per generator of `Γ`. -/
def precursorLift : FreeWreath K G (G ⧸ Γ) →* H :=
  SemidirectProduct.lift (lampLift Γ φ ψ hcomm) φ (lampLift_equivariant Γ φ ψ hcomm)

@[simp] theorem precursorLift_inr (g : G) :
    precursorLift Γ φ ψ hcomm (SemidirectProduct.inr g) = φ g := by
  simp [precursorLift, SemidirectProduct.lift]

@[simp] theorem precursorLift_inl_of (x : G ⧸ Γ) (k : K) :
    precursorLift Γ φ ψ hcomm
        (SemidirectProduct.inl
          (Monoid.CoprodI.of (M := fun _ : G ⧸ Γ => K) (i := x) k))
      = siteHom Γ φ ψ hcomm x k := by
  simp [precursorLift, SemidirectProduct.lift]

/-- On the base lamp the lift is just `ψ`: the base site is the coset of `1`. -/
@[simp] theorem precursorLift_base (k : K) :
    precursorLift Γ φ ψ hcomm
        (SemidirectProduct.inl
          (Monoid.CoprodI.of (M := fun _ : G ⧸ Γ => K)
            (i := (QuotientGroup.mk 1 : G ⧸ Γ)) k))
      = ψ k := by
  rw [precursorLift_inl_of, siteHom_mk]
  show φ 1 * ψ k * (φ 1)⁻¹ = ψ k
  simp

end Lift


/-! ## Uniqueness -/

section Unique

variable {Γ : Subgroup G}

/-- **The universal property of the free precursor (54.17), uniqueness half.**
Two homomorphisms out of `E` that agree on `G` and on the *base* lamp agree
everywhere.

Transitivity is what makes one lamp enough: the lamp at `gΓ` is the
`inr g`-conjugate of the lamp at the base site, so agreement there propagates to
every site, and the two factors of the semidirect product then exhaust the
group. -/
theorem precursorLift_unique
    (Φ₁ Φ₂ : FreeWreath K G (G ⧸ Γ) →* H)
    (hg : ∀ g : G, Φ₁ (SemidirectProduct.inr g) = Φ₂ (SemidirectProduct.inr g))
    (hk : ∀ k : K, Φ₁ (SemidirectProduct.inl
        (Monoid.CoprodI.of (M := fun _ : G ⧸ Γ => K)
          (i := (QuotientGroup.mk 1 : G ⧸ Γ)) k))
      = Φ₂ (SemidirectProduct.inl
        (Monoid.CoprodI.of (M := fun _ : G ⧸ Γ => K)
          (i := (QuotientGroup.mk 1 : G ⧸ Γ)) k))) :
    Φ₁ = Φ₂ := by
  -- first: the two agree on every single-site lamp
  have hsite : ∀ (x : G ⧸ Γ) (k : K),
      Φ₁ (SemidirectProduct.inl (Monoid.CoprodI.of
          (M := fun _ : G ⧸ Γ => K) (i := x) k))
        = Φ₂ (SemidirectProduct.inl (Monoid.CoprodI.of
          (M := fun _ : G ⧸ Γ => K) (i := x) k)) := by
    intro x k
    induction x using QuotientGroup.induction_on with
    | H g =>
      have hmove : (Monoid.CoprodI.of (M := fun _ : G ⧸ Γ => K)
            (i := (QuotientGroup.mk g : G ⧸ Γ)) k)
          = freeLampActionHom K (G ⧸ Γ) g
              (Monoid.CoprodI.of (M := fun _ : G ⧸ Γ => K)
                (i := (QuotientGroup.mk 1 : G ⧸ Γ)) k) := by
        have hidx : (g • (QuotientGroup.mk 1 : G ⧸ Γ))
            = (QuotientGroup.mk g : G ⧸ Γ) := by simp
        rw [freeLampActionHom_apply, freeLampMap, Monoid.CoprodI.lift_of, hidx]
      rw [hmove, SemidirectProduct.inl_aut, map_mul, map_mul, map_mul, map_mul,
        hg, hg, hk]
  -- second: they agree on the whole lamp factor
  have hlamp : Φ₁.comp SemidirectProduct.inl = Φ₂.comp SemidirectProduct.inl := by
    refine Monoid.CoprodI.ext_hom _ _ fun x => ?_
    exact MonoidHom.ext fun k => hsite x k
  refine MonoidHom.ext fun a => ?_
  rw [← SemidirectProduct.inl_left_mul_inr_right a, map_mul, map_mul, hg]
  exact congrArg (fun z => z * Φ₂ (SemidirectProduct.inr a.right))
    (congrArg (fun f : FreeLamp K (G ⧸ Γ) →* H => f a.left) hlamp)

end Unique

end FreePrecursor

end GroupApproximation
