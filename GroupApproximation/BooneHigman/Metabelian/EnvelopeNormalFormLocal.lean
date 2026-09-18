import GroupApproximation.BooneHigman.Metabelian.EnvelopeNormalFormCantor
import GroupApproximation.BooneHigman.Metabelian.EnvelopeFPFree
import GroupApproximation.Meta.AxiomGuard

/-!
# Local relators of the normal form: commutation and disjoint cones

In `RNFree X H = V_X ∗ (H ∗ H)` write `nfV v`, `nfH h`, `nfL h` for the three factor images.
Under `rnFreeToPerm H x₀` they go to `v`, `h` and `localize [x₀] h`.  This module names two
families of relators and proves that they lie in the kernel of `rnFreeHom H x₀`.
* `nfCommRelators`: `[nfL h, nfV f]` for `f ∈ V_X` fixing the cone `[x₀]` pointwise.  Such an `f`
  is supported in the complement of `cone [x₀]`, which is disjoint from the support of
  `localize [x₀] h` (`HydeLodha.commute_of_supportedIn`).
* `nfDisjRelators`: `[nfL h, nfV e * nfL k * (nfV e)⁻¹]` for `e ∈ V_X` carrying `cone [x₀]`
  onto the cone of a word `w` incomparable with `[x₀]`.  By `MapsCone.conj_localize` the second
  entry maps to `localize w k`, which commutes with `localize [x₀] h` (`commute_localize`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} [Finite X]

/-- The `V_X` factor of `RNFree X H`. -/
def nfV (H : Subgroup (TreeAut X)) (v : ↥(higmanThompsonV X)) : RNFree X H :=
  Monoid.Coprod.inl v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfV

/-- The first copy of `H` in `RNFree X H`, acting on the whole Cantor set. -/
def nfH (H : Subgroup (TreeAut X)) (h : ↥H) : RNFree X H :=
  Monoid.Coprod.inr (Monoid.Coprod.inl h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfH

/-- The second copy of `H` in `RNFree X H`, acting in the cone `[x₀]`. -/
def nfL (H : Subgroup (TreeAut X)) (h : ↥H) : RNFree X H :=
  Monoid.Coprod.inr (Monoid.Coprod.inr h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfL

theorem nf_toPerm_V (H : Subgroup (TreeAut X)) (x₀ : X) (v : ↥(higmanThompsonV X)) :
    rnFreeToPerm H x₀ (nfV H v) = (v : Equiv.Perm (Cantor X)) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nf_toPerm_V

theorem nf_toPerm_H (H : Subgroup (TreeAut X)) (x₀ : X) (h : ↥H) :
    rnFreeToPerm H x₀ (nfH H h) = cantorHom (h : TreeAut X) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nf_toPerm_H

theorem nf_toPerm_L (H : Subgroup (TreeAut X)) (x₀ : X) (h : ↥H) :
    rnFreeToPerm H x₀ (nfL H h) = localize [x₀] (cantorHom (h : TreeAut X)) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nf_toPerm_L

theorem nf_mem_ker_iff (H : Subgroup (TreeAut X)) (x₀ : X) (r : RNFree X H) :
    r ∈ (rnFreeHom H x₀).ker ↔ rnFreeToPerm H x₀ r = 1 := by
  rw [MonoidHom.mem_ker]
  exact Subtype.ext_iff

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nf_mem_ker_iff

/-- **Commutation relators.**  `nfL h` commutes with every `f ∈ V_X` fixing `cone [x₀]`. -/
def nfCommRelators (H : Subgroup (TreeAut X)) (x₀ : X) : Set (RNFree X H) :=
  {r | ∃ (h : ↥H) (f : ↥(higmanThompsonV X)),
    (∀ y : Cantor X, (f : Equiv.Perm (Cantor X)) (prepend [x₀] y) = prepend [x₀] y) ∧
      r = nfL H h * nfV H f * (nfL H h)⁻¹ * (nfV H f)⁻¹}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfCommRelators

theorem nfCommRelators_subset_ker (H : Subgroup (TreeAut X)) (x₀ : X) :
    nfCommRelators H x₀ ⊆ (rnFreeHom H x₀).ker := by
  rintro r ⟨h, f, hf, rfl⟩
  have hsupp : HydeLodha.SupportedIn (f : Equiv.Perm (Cantor X)) (cone [x₀])ᶜ := by
    intro z hz
    obtain ⟨y, rfl⟩ := mem_cone_iff.mp (not_not.mp hz)
    exact hf y
  have hc : Commute (localize [x₀] (cantorHom (h : TreeAut X))) (f : Equiv.Perm (Cantor X)) :=
    HydeLodha.commute_of_supportedIn (localize_supportedIn [x₀] _) hsupp disjoint_compl_right
  rw [nf_mem_ker_iff, map_mul, map_mul, map_mul, map_inv, map_inv, nf_toPerm_V, nf_toPerm_L,
    hc.eq, mul_inv_cancel_right, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfCommRelators_subset_ker

/-- **Disjoint-cone relators.**  `nfL h` commutes with the copy of `nfL k` conjugated by
`e ∈ V_X` onto the cone of a word `w` incomparable with `[x₀]`. -/
def nfDisjRelators (H : Subgroup (TreeAut X)) (x₀ : X) : Set (RNFree X H) :=
  {r | ∃ (h k : ↥H) (e : ↥(higmanThompsonV X)) (w : List X),
    MapsCone (e : Equiv.Perm (Cantor X)) [x₀] w ∧ ¬ [x₀] <+: w ∧ ¬ w <+: [x₀] ∧
      r = nfL H h * (nfV H e * nfL H k * (nfV H e)⁻¹) * (nfL H h)⁻¹ *
        (nfV H e * nfL H k * (nfV H e)⁻¹)⁻¹}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfDisjRelators

theorem nfDisjRelators_subset_ker (H : Subgroup (TreeAut X)) (x₀ : X) :
    nfDisjRelators H x₀ ⊆ (rnFreeHom H x₀).ker := by
  rintro r ⟨h, k, e, w, he, hxw, hwx, rfl⟩
  rw [nf_mem_ker_iff]
  simp only [map_mul, map_inv, nf_toPerm_V, nf_toPerm_L]
  rw [he.conj_localize, (commute_localize hxw hwx _ _).eq, mul_inv_cancel_right,
    mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfDisjRelators_subset_ker

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
