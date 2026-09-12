import GroupApproximation.Sofic.PushoutEmbedding
import GroupApproximation.Sofic.WeakMFNonsoficDouble
import GroupApproximation.Meta.AxiomGuard

/-!
# When a map of factors embeds an amalgamated double

A faithful homomorphism of vertex groups does not by itself induce a faithful
homomorphism of doubles: the subgroup over which the target is amalgamated may
contain new images of source elements.  This file proves the exact normal-form
criterion.

The general theorem `PushoutBaseChange.map_injective_of_reflects_range` allows
both the vertex groups and the base group to change.  Its specialization
`symmetricDoubleMap_injective_iff_reflects_mem` says that a faithful
`rho : G →* K` induces an embedding

`G *_Γ G → K *_Δ K`

if and only if `rho g ∈ Δ` implies `g ∈ Γ`.  Thus subgroup reflection is
precisely the injectivity step needed when passing from a faithful
representation of a vertex group to a representation of its double.
-/

namespace GroupApproximation

open Monoid

universe uι uH uH' uG uG'

namespace PushoutBaseChange

variable {ι : Type uι} {H : Type uH} {H' : Type uH'}
  {G : ι → Type uG} {G' : ι → Type uG'}
  [Group H] [Group H'] [∀ i, Group (G i)] [∀ i, Group (G' i)]

/-- The map of pushouts induced by maps of the base and every vertex group. -/
def map (φ : ∀ i, H →* G i) (ψ : ∀ i, H' →* G' i)
    (k : H →* H') (f : ∀ i, G i →* G' i)
    (hcomm : ∀ i, (f i).comp (φ i) = (ψ i).comp k) :
    PushoutI φ →* PushoutI ψ :=
  PushoutI.lift
    (fun i ↦ (PushoutI.of (φ := ψ) i).comp (f i))
    ((PushoutI.base ψ).comp k)
    (fun i ↦ by
      rw [MonoidHom.comp_assoc, hcomm i, ← MonoidHom.comp_assoc,
        PushoutI.of_comp_eq_base])

@[simp]
theorem map_of (φ : ∀ i, H →* G i) (ψ : ∀ i, H' →* G' i)
    (k : H →* H') (f : ∀ i, G i →* G' i)
    (hcomm : ∀ i, (f i).comp (φ i) = (ψ i).comp k)
    (i : ι) (g : G i) :
    map φ ψ k f hcomm (PushoutI.of (φ := φ) i g) =
      PushoutI.of (φ := ψ) i (f i g) := by
  simp [map]

@[simp]
theorem map_base (φ : ∀ i, H →* G i) (ψ : ∀ i, H' →* G' i)
    (k : H →* H') (f : ∀ i, G i →* G' i)
    (hcomm : ∀ i, (f i).comp (φ i) = (ψ i).comp k)
    (h : H) :
    map φ ψ k f hcomm (PushoutI.base φ h) =
      PushoutI.base ψ (k h) := by
  simp [map]

theorem map_ofCoprodI_prod
    (φ : ∀ i, H →* G i) (ψ : ∀ i, H' →* G' i)
    (k : H →* H') (f : ∀ i, G i →* G' i)
    (hf : ∀ i, Function.Injective (f i))
    (hcomm : ∀ i, (f i).comp (φ i) = (ψ i).comp k)
    (w : CoprodI.Word G) :
    map φ ψ k f hcomm (PushoutI.ofCoprodI w.prod) =
      PushoutI.ofCoprodI (PushoutEmbedding.wordMap f hf w).prod := by
  rw [PushoutEmbedding.wordMap_prod]
  induction w.prod using CoprodI.induction_on with
  | one => simp
  | of i g => simp [map]
  | mul x y hx hy => simp [hx, hy]

/-- **Base-changing Bass--Serre embedding criterion.**  An injective map on
the base and on every vertex group induces an injective map of pushouts when
each vertex map reflects membership in the target base group. -/
theorem map_injective_of_reflects_range
    (φ : ∀ i, H →* G i) (ψ : ∀ i, H' →* G' i)
    (k : H →* H') (f : ∀ i, G i →* G' i)
    (hφ : ∀ i, Function.Injective (φ i))
    (hψ : ∀ i, Function.Injective (ψ i))
    (hk : Function.Injective k)
    (hf : ∀ i, Function.Injective (f i))
    (hcomm : ∀ i, (f i).comp (φ i) = (ψ i).comp k)
    (hreflect : ∀ i g, f i g ∈ (ψ i).range → g ∈ (φ i).range) :
    Function.Injective (map φ ψ k f hcomm) := by
  classical
  apply (injective_iff_map_eq_one (map φ ψ k f hcomm)).2
  intro x hx
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty φ hφ
  let w : PushoutI.NormalWord d := PushoutI.NormalWord.equiv x
  have hxprod : w.prod = x :=
    (PushoutI.NormalWord.equiv (d := d)).symm_apply_apply x
  have hredSource : PushoutI.Reduced φ w.toWord :=
    PushoutEmbedding.normalWord_reduced φ d w
  have hredTarget :
      PushoutI.Reduced ψ (PushoutEmbedding.wordMap f hf w.toWord) := by
    intro l hl
    obtain ⟨l', hl', heq⟩ := List.mem_map.mp hl
    cases heq
    exact fun hrange ↦ hredSource l' hl' (hreflect l'.1 l'.2 hrange)
  have hwordRange :
      PushoutI.ofCoprodI (PushoutEmbedding.wordMap f hf w.toWord).prod ∈
        (PushoutI.base ψ).range := by
    refine ⟨(k w.head)⁻¹, ?_⟩
    have hprodImage :
        map φ ψ k f hcomm w.prod =
          PushoutI.base ψ (k w.head) *
            PushoutI.ofCoprodI
              (PushoutEmbedding.wordMap f hf w.toWord).prod := by
      rw [PushoutI.NormalWord.prod, map_mul, map_base,
        map_ofCoprodI_prod φ ψ k f hf hcomm]
    rw [hxprod, hx] at hprodImage
    calc
      PushoutI.base ψ (k w.head)⁻¹ =
          (PushoutI.base ψ (k w.head))⁻¹ * 1 := by simp
      _ = (PushoutI.base ψ (k w.head))⁻¹ *
          (PushoutI.base ψ (k w.head) *
            PushoutI.ofCoprodI
              (PushoutEmbedding.wordMap f hf w.toWord).prod) :=
        congrArg
          (fun z ↦ (PushoutI.base ψ (k w.head))⁻¹ * z)
          hprodImage
      _ = PushoutI.ofCoprodI
          (PushoutEmbedding.wordMap f hf w.toWord).prod := by simp
  have hempty := hredTarget.eq_empty_of_mem_range hψ hwordRange
  have hsourceEmpty : w.toWord = .empty := by
    apply CoprodI.Word.ext
    have hlist := congrArg CoprodI.Word.toList hempty
    simpa [PushoutEmbedding.wordMap, CoprodI.Word.empty] using hlist
  have hxbase : x = PushoutI.base φ w.head := by
    rw [← hxprod, PushoutI.NormalWord.prod, hsourceEmpty]
    simp
  have hkhead : k w.head = 1 := by
    apply PushoutI.base_injective hψ
    have : PushoutI.base ψ (k w.head) = 1 := by
      rw [← map_base φ ψ k f hcomm, ← hxbase, hx]
    simpa using this
  have hhead : w.head = 1 := hk (hkhead.trans (map_one k).symm)
  rw [hxbase, hhead, map_one]

end PushoutBaseChange

section SymmetricDouble

variable {G : Type uG} {K : Type uG'} [Group G] [Group K]
  (Γ : Subgroup G) (Δ : Subgroup K) (rho : G →* K)

/-- Restrict a vertex homomorphism to a map between the two amalgamating
subgroups. -/
def subgroupMap (hsub : ∀ g, g ∈ Γ → rho g ∈ Δ) : ↥Γ →* ↥Δ :=
  (rho.comp Γ.subtype).codRestrict Δ fun g ↦ hsub g g.property

theorem subgroupMap_injective (hsub : ∀ g, g ∈ Γ → rho g ∈ Δ)
    (hrho : Function.Injective rho) :
    Function.Injective (subgroupMap Γ Δ rho hsub) := by
  intro g h heq
  apply Subtype.ext
  apply hrho
  exact congrArg Subtype.val heq

theorem subgroupMap_commutes
    (hsub : ∀ g, g ∈ Γ → rho g ∈ Δ) :
    ∀ b, rho.comp (doubleMap G Γ b) =
      (doubleMap K Δ b).comp (subgroupMap Γ Δ rho hsub) := by
  intro b
  ext g
  rfl

/-- The homomorphism of symmetric doubles induced by a vertex homomorphism
which maps the source edge subgroup into the target edge subgroup. -/
def symmetricDoubleMap
    (hsub : ∀ g, g ∈ Γ → rho g ∈ Δ) :
    SymmetricDouble G Γ →* SymmetricDouble K Δ :=
  PushoutBaseChange.map (doubleMap G Γ) (doubleMap K Δ)
    (subgroupMap Γ Δ rho hsub) (fun _ ↦ rho)
    (subgroupMap_commutes Γ Δ rho hsub)

@[simp]
theorem symmetricDoubleMap_inDouble
    (hsub : ∀ g, g ∈ Γ → rho g ∈ Δ)
    (b : Bool) (g : G) :
    symmetricDoubleMap Γ Δ rho hsub (inDouble G Γ b g) =
      inDouble K Δ b (rho g) := by
  simp [symmetricDoubleMap, inDouble]

/-- The two copies of a vertex element in a symmetric double agree exactly
when that element belongs to the amalgamating subgroup. -/
theorem inDouble_false_eq_true_iff (g : G) :
    inDouble G Γ false g = inDouble G Γ true g ↔ g ∈ Γ := by
  constructor
  · intro heq
    have hinter :
        inDouble G Γ false g ∈
          (inDouble G Γ false).range ⊓ (inDouble G Γ true).range :=
      ⟨⟨g, rfl⟩, ⟨g, heq.symm⟩⟩
    have hinterBase :
        inDouble G Γ false g ∈ (PushoutI.base (doubleMap G Γ)).range := by
      rw [← PushoutI.inf_of_range_eq_base_range
        (doubleMap_injective G Γ) Bool.false_ne_true]
      simpa [inDouble] using hinter
    obtain ⟨gamma, hgamma⟩ := hinterBase
    have hvertex :
        inDouble G Γ false g = inDouble G Γ false (gamma : G) := by
      calc
        inDouble G Γ false g = PushoutI.base (doubleMap G Γ) gamma :=
          hgamma.symm
        _ = inDouble G Γ false (gamma : G) :=
          (PushoutI.of_apply_eq_base (doubleMap G Γ) false gamma).symm
    have : g = (gamma : G) := inDouble_injective G Γ false hvertex
    exact this.symm ▸ gamma.property
  · intro hg
    let gamma : ↥Γ := ⟨g, hg⟩
    change PushoutI.of (φ := doubleMap G Γ) false (gamma : G) =
      PushoutI.of (φ := doubleMap G Γ) true (gamma : G)
    exact (PushoutI.of_apply_eq_base (doubleMap G Γ) false gamma).trans
      (PushoutI.of_apply_eq_base (doubleMap G Γ) true gamma).symm

/-- **Exact injectivity criterion for a symmetric double.**  A faithful map
of vertex groups induces a faithful map of doubles precisely when it reflects
membership in the amalgamating subgroup. -/
theorem symmetricDoubleMap_injective_iff_reflects_mem
    (hsub : ∀ g, g ∈ Γ → rho g ∈ Δ)
    (hrho : Function.Injective rho) :
    Function.Injective (symmetricDoubleMap Γ Δ rho hsub) ↔
      ∀ g, rho g ∈ Δ → g ∈ Γ := by
  constructor
  · intro hinj g hg
    apply (inDouble_false_eq_true_iff Γ g).mp
    apply hinj
    rw [symmetricDoubleMap_inDouble, symmetricDoubleMap_inDouble]
    exact (inDouble_false_eq_true_iff Δ (rho g)).mpr hg
  · intro hreflect
    apply PushoutBaseChange.map_injective_of_reflects_range
      (doubleMap G Γ) (doubleMap K Δ)
      (subgroupMap Γ Δ rho hsub) (fun _ ↦ rho)
      (doubleMap_injective G Γ) (doubleMap_injective K Δ)
      (subgroupMap_injective Γ Δ rho hsub hrho) (fun _ ↦ hrho)
      (subgroupMap_commutes Γ Δ rho hsub)
    intro b g hg
    obtain ⟨delta, hdelta⟩ := hg
    have hmem : rho g ∈ Δ := by
      rw [← hdelta]
      exact delta.property
    refine ⟨⟨g, hreflect g hmem⟩, ?_⟩
    rfl

/-- Enlarging the target edge subgroup all the way to the vertex group makes
the induced map noninjective for every nontrivial source group, even when the
vertex homomorphism is the identity.  This is the minimal countermodel to the
invalid inference "faithful on each factor, therefore faithful on the
double". -/
theorem symmetricDoubleMap_bot_top_not_injective
    (G : Type uG) [Group G] [Nontrivial G] :
    ¬ Function.Injective
      (symmetricDoubleMap (⊥ : Subgroup G) (⊤ : Subgroup G)
        (MonoidHom.id G) (fun _ _ ↦ Subgroup.mem_top _)) := by
  intro hinj
  have hreflect :=
    (symmetricDoubleMap_injective_iff_reflects_mem
      (⊥ : Subgroup G) (⊤ : Subgroup G) (MonoidHom.id G)
      (fun _ _ ↦ Subgroup.mem_top _) (fun _ _ h ↦ h)).mp hinj
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hbot : g ∈ (⊥ : Subgroup G) := hreflect g (Subgroup.mem_top _)
  exact hg (by simpa using hbot)

#audit_axioms PushoutBaseChange.map_injective_of_reflects_range
#audit_axioms symmetricDoubleMap_injective_iff_reflects_mem
#audit_axioms symmetricDoubleMap_bot_top_not_injective

end SymmetricDouble

end GroupApproximation
