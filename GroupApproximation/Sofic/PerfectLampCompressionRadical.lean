import GroupApproximation.Algebra.PerfectLamp
import GroupApproximation.Sofic.AscendingHNNSplitExtension
import GroupApproximation.Sofic.AscendingHNNWreathWitness
import GroupApproximation.Sofic.TorsionSpectralCollapse
import GroupApproximation.Sofic.UniversalVisibleQuotient

/-!
# Perfect lamps: the exact MF radical of a compression wreath product

An *exact* radical statement `Res_MF(W) = N` has two halves.  For the
ascending-HNN compression wreath product

  `W = K^(V/Γ) ⋊ V`,   `V = Vertical α hα`,  `X = Cosets α hα`,

the **exactness half** `Res_MF(W) ≤ K^(V/Γ)` is free whenever the acting group
is MF: the wreath projection lands in an MF group, so it kills the radical
(`actualCoronaMFResidual_le_ker_of_isCDEOperatorMF`), and its kernel is the lamp
subgroup (`ker_rightHom_eq_lampRange`).

This file closes the other half, `K^(V/Γ) ≤ Res_MF(W)`, for every **perfect
torsion** lamp group — in particular for every nontrivial finite perfect `K`.
The analytic content is entirely borrowed: the only approximation-theoretic
input is `TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness`,
the unconditional finite-order collapse endpoint.  Everything added here is
group theory.

## The argument

Fix the universal MF-visible quotient `q : W → W ⧸ Res_MF(W)`.

1. *Collapse.*  For a lamp value `k` of finite order, the one-site lamp
   `witnessLamp` at the witness site is a torsion compression witness
   (`isTorsionCompressionWitness_witnessLamp`), so every collapse commutator
   `⁅γ, witnessLamp k⁆` with `γ` in the base copy lies in the MF radical.  Read
   in the quotient: `q (γ · k_{x₀} · γ⁻¹) = q (k_{x₀})`.

2. *Abelianization.*  Properness supplies a mover `a₀ ∉ α(Γ)`, which carries the
   witness site to a **different** site.  Lamps at distinct sites commute, so
   `commute_map_of_collapse` turns step 1 into
   `Commute (q k_{x₀}) (q k'_{x₀})` for *all* pairs of finite-order values.
   The image of the coordinate copy `K_{x₀}` is therefore abelian.

3. *Perfectness.*  A perfect group has no nontrivial homomorphism with abelian
   image (`eq_one_of_commuting_image_of_perfect`), so the whole coordinate copy
   dies: `witnessLamp k ∈ Res_MF(W)` for every `k`.

4. *Transitivity.*  `V` acts transitively on `V/Γ` (`exists_smul_tSite`) and the
   radical is normal, so every one-site lamp at every site dies; the one-site
   lamps generate the lamp group (`Lamp.mem_closure_singles`), so the whole lamp
   subgroup lies in the radical.

Steps 2--4 are the reason perfectness is the right hypothesis: for an abelian
lamp group the same collapse leaves exactly the parity-per-height invariants
behind, which is the `K = C₂` picture of `Sofic/AscendingHNNFullTelescopeRadical`.
Nothing here assumes soficity, residual finiteness, or any amalgam theorem.
-/

namespace GroupApproximation
namespace PerfectLampRadical

open SemidirectProduct MarkedCompression TorsionCompressionCollapse
open scoped commutatorElement

/-! ## Perfect groups have no abelian shadow -/

/-- **A perfect group has no homomorphism with commuting image.**  If every pair
of values of `φ` commutes then `φ` kills every commutator, hence all of
`commutator K = ⊤`.  This is the only place perfectness is used. -/
theorem eq_one_of_commuting_image_of_perfect {K : Type*} [Group K] {Q : Type*}
    [Group Q] (hK : commutator K = ⊤) (φ : K →* Q)
    (hcomm : ∀ a b : K, Commute (φ a) (φ b)) (k : K) : φ k = 1 := by
  have hker : commutator K ≤ φ.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr ?_
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (hcomm a b)
  have hmem : k ∈ commutator K := by rw [hK]; exact Subgroup.mem_top k
  exact MonoidHom.mem_ker.mp (hker hmem)

/-- Every element of a finite group has finite order.  This is the form the
collapse endpoint consumes. -/
theorem exists_pow_eq_one_of_finite {K : Type*} [Group K] [Finite K] (k : K) :
    ∃ m : ℕ, 0 < m ∧ k ^ m = 1 :=
  ⟨orderOf k, orderOf_pos k, pow_orderOf_eq_one k⟩

/-! ## The compression wreath product -/

section Wreath

variable {Γ₀ : Type} [Group Γ₀] (β : Γ₀ →* Γ₀) (hβ : Function.Injective β)
variable {K₀ : Type} [Group K₀] [DecidableEq (Cosets β hβ)]
variable [Countable (WreathV (K := K₀) β hβ)]

/-- **Step 1: the collapse, borrowed.**  For a finite-order lamp value the
collapse commutator of the witness lamp with any base element is invisible in
every corona representation.  The only analytic input of the file. -/
theorem commutator_witnessLamp_invisible
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    {k : K₀} {m : ℕ} (hm : 0 < m) (hk : k ^ m = 1) (γ : Γ₀) :
    ActualCoronaMFInvisible
      ⁅(inr (iotaVertical β hβ γ) : WreathV (K := K₀) β hβ),
        witnessLamp β hβ k⁆ :=
  TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness
    (baseSub_hasKazhdanPropertyT β hβ hΓ)
    (fun _ hw => wreathT_compress β hβ hw)
    (isTorsionCompressionWitness_witnessLamp β hβ k m hm hk)
    ((mem_baseSub_iff β hβ).mpr ⟨γ, rfl⟩)

/-- **Step 2: fibre abelianization.**  In the universal MF-visible quotient the
images of two one-site lamps at the witness site commute.  The mover `a₀` sends
the witness site to a different site, where lamps commute for free; the collapse
then identifies the moved lamp with the original one. -/
theorem commute_mk_witnessLamp
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    (htor : ∀ k : K₀, ∃ m : ℕ, 0 < m ∧ k ^ m = 1)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β) (a b : K₀) :
    Commute
      (QuotientGroup.mk'
        (actualCoronaMFResidual (WreathV (K := K₀) β hβ)) (witnessLamp β hβ a))
      (QuotientGroup.mk'
        (actualCoronaMFResidual (WreathV (K := K₀) β hβ)) (witnessLamp β hβ b)) := by
  obtain ⟨m, hm, hma⟩ := htor a
  have hcomm1 :
      (QuotientGroup.mk' (actualCoronaMFResidual (WreathV (K := K₀) β hβ)))
        ⁅(inr (iotaVertical β hβ a₀) : WreathV (K := K₀) β hβ),
          witnessLamp β hβ a⁆ = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact commutator_witnessLamp_invisible β hβ hΓ hm hma a₀
  have hid :
      (QuotientGroup.mk' (actualCoronaMFResidual (WreathV (K := K₀) β hβ)))
          ((inr (iotaVertical β hβ a₀) : WreathV (K := K₀) β hβ) *
            witnessLamp β hβ a * (inr (iotaVertical β hβ a₀))⁻¹)
        = (QuotientGroup.mk'
            (actualCoronaMFResidual (WreathV (K := K₀) β hβ))) (witnessLamp β hβ a) :=
    mem_piConjStabilizer_iff.mp ((map_commutator_eq_one_iff _ _ _).mp hcomm1)
  have hsite : iotaVertical β hβ a₀ • tSite β hβ ≠ tSite β hβ :=
    not_smul_tSite_of_not_mem_range β hβ ha₀
  have hconj : (inr (iotaVertical β hβ a₀) : WreathV (K := K₀) β hβ) *
      witnessLamp β hβ a * (inr (iotaVertical β hβ a₀))⁻¹
      = inl (Lamp.single (iotaVertical β hβ a₀ • tSite β hβ) a) :=
    conj_witnessLamp β hβ a₀ a
  have hcomm2 : Commute ((inr (iotaVertical β hβ a₀) : WreathV (K := K₀) β hβ) *
      witnessLamp β hβ a * (inr (iotaVertical β hβ a₀))⁻¹) (witnessLamp β hβ b) := by
    have hs : Commute (Lamp.single (iotaVertical β hβ a₀ • tSite β hβ) a)
        (Lamp.single (tSite β hβ) b) := Lamp.single_commute hsite a b
    rw [hconj]
    exact hs.map (inl : Lamp K₀ (Cosets β hβ) →* WreathV (K := K₀) β hβ)
  exact commute_map_of_collapse _ hid hcomm2

/-- **Step 3: perfectness kills the coordinate copy.**  The one-site lamp at the
witness site is invisible for *every* value of a perfect torsion lamp group. -/
theorem witnessLamp_invisible
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    (htor : ∀ k : K₀, ∃ m : ℕ, 0 < m ∧ k ^ m = 1)
    (hK : commutator K₀ = ⊤)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β) (k : K₀) :
    ActualCoronaMFInvisible (witnessLamp β hβ k) := by
  have hφ := eq_one_of_commuting_image_of_perfect (K := K₀) hK
    ((QuotientGroup.mk' (actualCoronaMFResidual (WreathV (K := K₀) β hβ))).comp
      ((inl : Lamp K₀ (Cosets β hβ) →* WreathV (K := K₀) β hβ).comp
        (Lamp.singleHom (tSite β hβ))))
    (fun a b => commute_mk_witnessLamp β hβ hΓ htor ha₀ a b) k
  have hmem : witnessLamp β hβ k ∈
      (QuotientGroup.mk'
        (actualCoronaMFResidual (WreathV (K := K₀) β hβ))).ker :=
    MonoidHom.mem_ker.mpr hφ
  rw [QuotientGroup.ker_mk'] at hmem
  exact hmem

/-- **Step 4a: transitivity.**  Every one-site lamp, at every site and with
every value, is invisible: the acting group moves the witness site anywhere and
the radical is normal. -/
theorem single_invisible
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    (htor : ∀ k : K₀, ∃ m : ℕ, 0 < m ∧ k ^ m = 1)
    (hK : commutator K₀ = ⊤)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β) (x : Cosets β hβ) (k : K₀) :
    ActualCoronaMFInvisible
      (inl (Lamp.single x k) : WreathV (K := K₀) β hβ) := by
  obtain ⟨g, hg⟩ := exists_smul_tSite β hβ x
  have hwit : witnessLamp β hβ k ∈
      actualCoronaMFResidual (WreathV (K := K₀) β hβ) :=
    witnessLamp_invisible β hβ hΓ htor hK ha₀ k
  have hN : (actualCoronaMFResidual (WreathV (K := K₀) β hβ)).Normal :=
    inferInstance
  have hconj := hN.conj_mem _ hwit (inr g : WreathV (K := K₀) β hβ)
  have heq : (inr g : WreathV (K := K₀) β hβ) * witnessLamp β hβ k *
      (inr g : WreathV (K := K₀) β hβ)⁻¹ = inl (Lamp.single x k) := by
    rw [show witnessLamp β hβ k
        = (inl (Lamp.single (tSite β hβ) k) : WreathV (K := K₀) β hβ) from rfl,
      conj_inl_single K₀ (Vertical β hβ) (Cosets β hβ) g (tSite β hβ) k, hg]
  rwa [heq] at hconj

/-- **Step 4b: the analytic half, in full.**  The whole lamp subgroup of a
perfect torsion lamp group lies in the MF radical of the compression wreath
product.  The one-site lamps generate. -/
theorem lampRange_le_actualCoronaMFResidual
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    (htor : ∀ k : K₀, ∃ m : ℕ, 0 < m ∧ k ^ m = 1)
    (hK : commutator K₀ = ⊤)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β) :
    (inl : Lamp K₀ (Cosets β hβ) →* WreathV (K := K₀) β hβ).range
      ≤ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  rintro _ ⟨f, rfl⟩
  have hclosure :
      Subgroup.closure {g : Lamp K₀ (Cosets β hβ) |
          ∃ (x : Cosets β hβ) (k : K₀), g = Lamp.single x k}
        ≤ (actualCoronaMFResidual (WreathV (K := K₀) β hβ)).comap
            (inl : Lamp K₀ (Cosets β hβ) →* WreathV (K := K₀) β hβ) := by
    rw [Subgroup.closure_le]
    rintro g ⟨x, k, rfl⟩
    exact single_invisible β hβ hΓ htor hK ha₀ x k
  exact hclosure (Lamp.mem_closure_singles f)

/-! ## The exact radical -/

/-- **The exact MF radical of a perfect-lamp compression wreath product.**
`Res_MF(K^(V/Γ) ⋊ V) = K^(V/Γ)` for every perfect torsion lamp group `K`, as
soon as the acting group is MF.

The two halves are independent: the inclusion `≥` is the collapse-plus-
perfectness argument of this file, and the inclusion `≤` is the MF-ness of the
acting group.  Neither uses an amalgam theorem. -/
theorem actualCoronaMFResidual_eq_lampRange
    [Countable (Vertical β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    (htor : ∀ k : K₀, ∃ m : ℕ, 0 < m ∧ k ^ m = 1)
    (hK : commutator K₀ = ⊤)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β)
    (hV : IsCDEOperatorMF (Vertical β hβ)) :
    actualCoronaMFResidual (WreathV (K := K₀) β hβ)
      = (inl : Lamp K₀ (Cosets β hβ) →* WreathV (K := K₀) β hβ).range := by
  refine le_antisymm ?_
    (lampRange_le_actualCoronaMFResidual β hβ hΓ htor hK ha₀)
  refine le_trans (actualCoronaMFResidual_le_ker_of_isCDEOperatorMF
    (rightHom : WreathV (K := K₀) β hβ →* Vertical β hβ) hV) ?_
  exact le_of_eq ker_rightHom_eq_lampRange

/-- The MF radical is exactly the kernel of the wreath projection. -/
theorem actualCoronaMFResidual_eq_ker_rightHom
    [Countable (Vertical β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    (htor : ∀ k : K₀, ∃ m : ℕ, 0 < m ∧ k ^ m = 1)
    (hK : commutator K₀ = ⊤)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β)
    (hV : IsCDEOperatorMF (Vertical β hβ)) :
    actualCoronaMFResidual (WreathV (K := K₀) β hβ)
      = (rightHom : WreathV (K := K₀) β hβ →* Vertical β hβ).ker := by
  rw [actualCoronaMFResidual_eq_lampRange β hβ hΓ htor hK ha₀ hV,
    ker_rightHom_eq_lampRange]

/-- **The universal MF-visible quotient is the acting group.**  MF approximation
forgets the entire lamp group and remembers exactly the skeleton. -/
noncomputable def universalVisibleQuotientEquiv
    [Countable (Vertical β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    (htor : ∀ k : K₀, ∃ m : ℕ, 0 < m ∧ k ^ m = 1)
    (hK : commutator K₀ = ⊤)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β)
    (hV : IsCDEOperatorMF (Vertical β hβ)) :
    (WreathV (K := K₀) β hβ ⧸
        actualCoronaMFResidual (WreathV (K := K₀) β hβ)) ≃* Vertical β hβ :=
  (QuotientGroup.quotientMulEquivOfEq
      (actualCoronaMFResidual_eq_ker_rightHom β hβ hΓ htor hK ha₀ hV)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (rightHom : WreathV (K := K₀) β hβ →* Vertical β hβ)
      rightHom_surjective)

end Wreath

end PerfectLampRadical
end GroupApproximation
