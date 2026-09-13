import GroupApproximation.Kazhdan.HaagerupAffineSums
import GroupApproximation.Kazhdan.GHWTheoremFourClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# Groups embedded in finite products of Haagerup groups

`non_mf_groups_exist.tex`, `sec:chain-core`, the remark after `cor:dynamic-rank-budget`
(tex 1796–1798):

> Its finitely generated restriction image lies in a finite product of groups
> $\GL_2(k[z,z^{-1}])$, hence in a Haagerup group by~\cite[Theorem~4]{GHW}, and is finite.

* `ProperAffineAction.comapHomAffine`: a proper affine action pulled back along a homomorphism, as a
  (not necessarily proper) affine action;
* `hasHaagerupProperty_of_injective_pi`: if finitely many homomorphisms `f i : Γ → H i` separate
  the points of `Γ` and every image `f i (Γ)` has the Haagerup property, then `Γ` has it;
* `hasHaagerupProperty_of_injective_pi_glTwo`: the GHW consumption.  A countable group with finitely
  many point-separating homomorphisms into groups `GL_2` over fields has the Haagerup property, by the
  closed `GHW.printedGHWTheoremFour`.
-/

namespace GroupApproximation
namespace Haagerup

universe u v

/-- A proper affine action pulled back along a homomorphism, forgetting properness. -/
def ProperAffineAction.comapHomAffine {G Γ : Type u} [Group G] [Group Γ]
    (A : ProperAffineAction.{u, v} G) (ρ : Γ →* G) : AffineAction.{u, v} Γ where
  E := A.E
  π := A.π.comp ρ
  b γ := A.b (ρ γ)
  isCocycle γ δ := by
    show A.b (ρ (γ * δ)) = A.b (ρ γ) + A.π (ρ γ) (A.b (ρ δ))
    rw [map_mul]
    exact A.isCocycle (ρ γ) (ρ δ)

/-- **Finite products.**  If finitely many homomorphisms separate the points of `Γ` and each image
has the Haagerup property, the `ℓ²`-sum of the pulled-back proper actions is proper. -/
theorem hasHaagerupProperty_of_injective_pi {Γ : Type u} [Group Γ] {ι : Type} [Finite ι]
    {H : ι → Type u} [∀ i, Group (H i)] (f : ∀ i, Γ →* H i)
    (hf : ∀ γ δ : Γ, (∀ i, f i γ = f i δ) → γ = δ)
    (hH : ∀ i, HasHaagerupProperty.{u, v} (f i).range) :
    HasHaagerupProperty.{u, v} Γ := by
  classical
  have A : ∀ i, ProperAffineAction.{u, v} (f i).range := fun i ↦ Classical.choice (hH i)
  refine hasHaagerupProperty_of_finite_sum
    (fun i ↦ (A i).comapHomAffine (f i).rangeRestrict) fun R ↦ ?_
  let φ : Γ → ∀ i, (f i).range := fun γ i ↦ (f i).rangeRestrict γ
  have hφ : Function.Injective φ := fun γ δ h ↦
    hf γ δ fun i ↦ congrArg Subtype.val (congrFun h i)
  refine ((Set.Finite.pi fun i ↦ (A i).proper R).preimage hφ.injOn).subset ?_
  intro γ hγ i _
  exact hγ i

/-- **GHW consumption at finitely many places.**  A countable group with finitely many
point-separating homomorphisms into groups `GL_2(K i)` over fields has the Haagerup property. -/
theorem hasHaagerupProperty_of_injective_pi_glTwo {Γ : Type} [Group Γ] [Countable Γ] {ι : Type}
    [Finite ι] {K : ι → Type} [∀ i, Field (K i)] (f : ∀ i, Γ →* GL (Fin 2) (K i))
    (hf : ∀ γ δ : Γ, (∀ i, f i γ = f i δ) → γ = δ) : HasHaagerupProperty.{0, 0} Γ :=
  hasHaagerupProperty_of_injective_pi f hf fun i ↦
    GHW.printedGHWTheoremFour (K i) (f i).range
      (Function.Surjective.countable (f i).rangeRestrict_surjective)

end Haagerup
end GroupApproximation

#audit_axioms GroupApproximation.Haagerup.hasHaagerupProperty_of_injective_pi
#audit_axioms GroupApproximation.Haagerup.hasHaagerupProperty_of_injective_pi_glTwo
