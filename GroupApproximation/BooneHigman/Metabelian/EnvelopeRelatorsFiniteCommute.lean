import GroupApproximation.BooneHigman.Metabelian.EnvelopeNormalFormSection
import Mathlib.GroupTheory.Finiteness
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite relator families: commutation bookkeeping

Tools for cutting the commutation relator families `nfCommRelators` and `nfDisjRelators` of
`RNFree X H` down to finite subfamilies.
* `rf_commute_closure`: if two homomorphisms into a group commute on generating sets, they
  commute on the generated subgroups.
* `rf_mem_of_commute`, `rf_commute_of_mem`: a commutator lies in a normal subgroup `N` exactly
  when the images commute in `G ⧸ N`.
* `rfL`, `rfV`, `rfConjL`: the factor maps of `RNFree X H` composed with a quotient map, as
  monoid homomorphisms.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

/-- Two homomorphisms that commute on generating sets commute on the generated subgroups. -/
theorem rf_commute_closure {A B Q : Type*} [Group A] [Group B] [Group Q] (φ : A →* Q)
    (ψ : B →* Q) {S : Set A} {T : Set B} (hST : ∀ s ∈ S, ∀ t ∈ T, Commute (φ s) (ψ t))
    {a : A} (ha : a ∈ Subgroup.closure S) {b : B} (hb : b ∈ Subgroup.closure T) :
    Commute (φ a) (ψ b) := by
  have key : ∀ t ∈ T, Commute (φ a) (ψ t) := by
    intro t ht
    induction ha using Subgroup.closure_induction with
    | mem x hx => exact hST x hx t ht
    | one => rw [map_one]; exact Commute.one_left _
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_left hy
    | inv x _ hx => rw [map_inv]; exact hx.inv_left
  induction hb using Subgroup.closure_induction with
  | mem t ht => exact key t ht
  | one => rw [map_one]; exact Commute.one_right _
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
  | inv x _ hx => rw [map_inv]; exact hx.inv_right

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rf_commute_closure

/-- A commutator lies in `N` when the images commute in the quotient. -/
theorem rf_mem_of_commute {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {a b : G}
    (h : Commute (a : G ⧸ N) (b : G ⧸ N)) : a * b * a⁻¹ * b⁻¹ ∈ N := by
  refine (QuotientGroup.eq_one_iff (N := N) _).mp ?_
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv, h.eq, mul_inv_cancel_right, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rf_mem_of_commute

/-- The images of `a` and `b` commute in `G ⧸ N` when their commutator lies in `N`. -/
theorem rf_commute_of_mem {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {a b : G}
    (h : a * b * a⁻¹ * b⁻¹ ∈ N) : Commute (a : G ⧸ N) (b : G ⧸ N) := by
  have h1 := (QuotientGroup.eq_one_iff (N := N) _).mpr h
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv] at h1
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rf_commute_of_mem

/-- A finitely presented group is finitely generated (reproved here to keep imports light). -/
theorem rf_fg_of_isFinitelyPresented {G : Type*} [Group G] (h : Group.IsFinitelyPresented G) :
    Group.FG G := by
  obtain ⟨_, φ, hφ, -⟩ := h.out
  exact Group.fg_of_surjective hφ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rf_fg_of_isFinitelyPresented

variable {X : Type*} [Finite X]

/-- The localized copy of `H`, followed by the quotient map to `RNFree X H ⧸ N`. -/
def rfL (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal] :
    ↥H →* RNFree X H ⧸ N :=
  MonoidHom.comp (QuotientGroup.mk' N)
    (MonoidHom.comp (Monoid.Coprod.inr : Monoid.Coprod ↥H ↥H →* RNFree X H)
      (Monoid.Coprod.inr : ↥H →* Monoid.Coprod ↥H ↥H))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rfL

theorem rfL_apply (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal] (h : ↥H) :
    rfL H N h = ((nfL H h : RNFree X H) : RNFree X H ⧸ N) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rfL_apply

/-- The `V_X` factor, followed by the quotient map to `RNFree X H ⧸ N`. -/
def rfV (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal] :
    ↥(higmanThompsonV X) →* RNFree X H ⧸ N :=
  MonoidHom.comp (QuotientGroup.mk' N)
    (Monoid.Coprod.inl : ↥(higmanThompsonV X) →* RNFree X H)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rfV

theorem rfV_apply (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (v : ↥(higmanThompsonV X)) : rfV H N v = ((nfV H v : RNFree X H) : RNFree X H ⧸ N) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rfV_apply

/-- The localized copy of `H` conjugated by `nfV e`, in the quotient `RNFree X H ⧸ N`. -/
def rfConjL (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (e : ↥(higmanThompsonV X)) : ↥H →* RNFree X H ⧸ N :=
  MonoidHom.comp (MulAut.conj (rfV H N e)).toMonoidHom (rfL H N)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rfConjL

theorem rfConjL_apply (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (e : ↥(higmanThompsonV X)) (k : ↥H) :
    rfConjL H N e k =
      ((nfV H e * nfL H k * (nfV H e)⁻¹ : RNFree X H) : RNFree X H ⧸ N) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rfConjL_apply

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
