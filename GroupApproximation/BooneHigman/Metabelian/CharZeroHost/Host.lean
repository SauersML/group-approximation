import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Faithful
import GroupApproximation.BooneHigman.Metabelian.ChainHost
import GroupApproximation.Meta.AxiomGuard

/-!
# The char-zero host on the affine elementary group (lane bh-met-09)

Research claim: the affine elementary group `R^n ⋊ E_n(R)`, `R = A[t_1, …, t_k]`, of the chain
skeleton (`Chain.AffineElementaryGroup`) acts faithfully and self-similarly on the tree over
`F_p^n × F_p^k`.

**Route.**
* `isSelfSimilarRep_comp`: restricting `rho` along an injective hom `f : Γ →* Aff n R` whose image
  is closed under states gives a faithful self-similar representation of `Γ`;
* `affHom : R^n ⋊ E_n(R) →* R^n ⋊ GL_n(R)` is injective (`affHom_injective`), and the state
  `(stateVec, σ_a g)` of an elementary element is again elementary, since `σ_a` maps `E_n` into
  `E_n` (`elementaryGroupMap`, `affHom_state`);
* `nontrivial_letter`: the alphabet has at least two letters when `1 < p` and `0 < n`.
Endpoint: `isSelfSimilarRep_affineElementary`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharZeroHost

open MvPolynomial
open scoped Matrix

/-- **Plug**: restricting the tree representation along an injective hom whose image is closed
under states. -/
theorem isSelfSimilarRep_comp {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
    [IsNoetherianRing A] {p n k : ℕ} [NeZero p] [Fact (1 < p)] (D : DigitData A p)
    {Γ : Type*} [Group Γ] (f : Γ →* Aff n (MvPolynomial (Fin k) A)) (hf : Function.Injective f)
    (hs : ∀ (γ : Γ) (ℓ : Letter p n k), ∃ δ : Γ, f δ = stateG D (f γ) ℓ) :
    Trees.IsSelfSimilarRep ((rho (n := n) (k := k) D).comp f) :=
  ⟨(rho_injective D).comp hf, (Trees.isSelfSimilar_range_iff _).2 fun γ ℓ => by
    obtain ⟨δ, hδ⟩ := hs γ ℓ
    refine ⟨δ, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hδ]
    exact state_rho D (f γ) ℓ⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.isSelfSimilarRep_comp

/-- The inclusion `R^n ⋊ E_n(R) →* R^n ⋊ GL_n(R)`. -/
def affHom (n : ℕ) (R : Type) [CommRing R] : Chain.AffineElementaryGroup n R →* Aff n R :=
  SemidirectProduct.map (MonoidHom.id _) (elementaryGroup (Fin n) R).subtype
    fun _ => MonoidHom.ext fun _ => rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.affHom

theorem affHom_injective (n : ℕ) (R : Type) [CommRing R] : Function.Injective (affHom n R) :=
  fun x y h => by
    have h1 : x.left = y.left := congrArg SemidirectProduct.left h
    have h2 : (x.right : GL (Fin n) R) = y.right := congrArg SemidirectProduct.right h
    exact SemidirectProduct.ext h1 (Subtype.ext h2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.affHom_injective

/-- The state of an elementary element is elementary. -/
theorem affHom_state {A : Type} [CommRing A] {p n k : ℕ} (D : DigitData A p)
    (x : Chain.AffineElementaryGroup n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) :
    affHom n (MvPolynomial (Fin k) A)
        ⟨Multiplicative.ofAdd (stateVec D (affHom n (MvPolynomial (Fin k) A) x) ℓ),
          elementaryGroupMap (sigmaZ p ℓ.2) x.right⟩ =
      stateG D (affHom n (MvPolynomial (Fin k) A) x) ℓ :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.affHom_state

/-- The alphabet `F_p^n × F_p^k` has two distinct letters when `1 < p` and `0 < n`. -/
theorem nontrivial_letter {p n k : ℕ} [Fact (1 < p)] (hn : 0 < n) :
    Nontrivial (Letter p n k) :=
  ⟨⟨(fun _ => (0 : ZMod p), fun _ => (0 : ZMod p)),
    (fun _ => (1 : ZMod p), fun _ => (0 : ZMod p)), fun h =>
      zero_ne_one (congrFun (congrArg Prod.fst h) ⟨0, hn⟩ : (0 : ZMod p) = 1)⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.nontrivial_letter

/-- **Endpoint**: the affine elementary group over `A[t_1, …, t_k]` acts faithfully and
self-similarly on the tree over `F_p^n × F_p^k`. -/
theorem isSelfSimilarRep_affineElementary {A : Type} [CommRing A] [IsDomain A] [CharZero A]
    [IsNoetherianRing A] {p n k : ℕ} [NeZero p] [Fact (1 < p)] (D : DigitData A p) :
    Trees.IsSelfSimilarRep
      ((rho (n := n) (k := k) D).comp (affHom n (MvPolynomial (Fin k) A))) :=
  isSelfSimilarRep_comp D _ (affHom_injective n _) fun x ℓ =>
    ⟨⟨Multiplicative.ofAdd (stateVec D (affHom n (MvPolynomial (Fin k) A) x) ℓ),
      elementaryGroupMap (sigmaZ p ℓ.2) x.right⟩, affHom_state D x ℓ⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharZeroHost.isSelfSimilarRep_affineElementary

/-- The tree host packaged as in `Chain.CharZeroAffineSelfSimilarStatement`. -/
theorem exists_rep_affineElementary {A : Type} [CommRing A] [IsDomain A] [CharZero A]
    [IsNoetherianRing A] {p n k : ℕ} [NeZero p] [Fact (1 < p)] (D : DigitData A p)
    (hn : 0 < n) :
    ∃ (X : Type) (_ : Finite X) (_ : Nontrivial X)
      (ρ : Chain.AffineElementaryGroup n (MvPolynomial (Fin k) A) →* Trees.TreeAut X),
        Trees.IsSelfSimilarRep ρ :=
  ⟨Letter p n k, inferInstance, nontrivial_letter hn, _, isSelfSimilarRep_affineElementary D⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.exists_rep_affineElementary

end CharZeroHost
end Metabelian
end BooneHigman
end GroupApproximation
