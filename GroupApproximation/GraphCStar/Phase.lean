import GroupApproximation.GraphCStar.Universal

/-!
# Phase automorphisms of `C*(G)` and the gauge action

For `c : E → 𝕋`, the family `p_v`, `c_e s_e` is again a Cuntz–Krieger family. This file builds the
automorphism of `C*(G)` fixing every `p_v` and sending `s_e` to `c_e s_e`.

The automorphism is not obtained from the universal property of `C*(G)`, which only applies to
targets in the universe of `G`. It acts on the ambient product by reindexing: its coordinate at a
representation `R` is the coordinate at the phased representation `R.phase c`.

* `CKFamily.phase`: the phased family.
* `phaseHom G c`: the endomorphism `p_v ↦ p_v`, `s_e ↦ c_e s_e` of `C*(G)`.
* `phaseHom_comp`, `phaseHom_one`: `c ↦ phaseHom G c` is multiplicative.
* `phaseEquiv G c`: the automorphism.
* `gaugeEquiv G z`: the gauge automorphism `γ_z`, `s_e ↦ z s_e` (Kumjian–Pask–Raeburn 1998, §2).
* `edgePhaseEquiv G e₀ z`: the automorphism multiplying the single edge `e₀` by `z`. For the graph
  `E(u)` and the edge `a_ij^(1)` this is the automorphism `g_{ij,z}` of the STW Problem L artifact
  (`research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md`, §2).

The prose of this module was written by Claude (Anthropic).
-/

open scoped CStarAlgebra ENNReal

noncomputable section

universe u

namespace GroupApproximation
namespace GraphCStar

open Finset

variable {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V]

namespace CKFamily

variable {G : Graph V E} {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- The family `p_v`, `c_e s_e` for scalars `c_e` of modulus one. -/
def phase (F : CKFamily G A) (c : E → unitary ℂ) : CKFamily G A where
  p := F.p
  s e := (c e : ℂ) • F.s e
  star_p := F.star_p
  p_mul_p_self := F.p_mul_p_self
  p_mul_p_of_ne := F.p_mul_p_of_ne
  s_mul_p_rng e := by rw [smul_mul_assoc, F.s_mul_p_rng]
  star_s_mul_s_self e := by
    rw [star_smul, smul_mul_smul_comm, Unitary.star_mul_self_of_mem (c e).2, one_smul,
      F.star_s_mul_s_self]
  star_s_mul_s_of_ne e e' h := by
    rw [star_smul, smul_mul_smul_comm, F.star_s_mul_s_of_ne e e' h, smul_zero]
  sum_s_mul_star_s v hv := by
    rw [← F.sum_s_mul_star_s v hv]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [star_smul, smul_mul_smul_comm, Unitary.mul_star_self_of_mem (c e).2, one_smul]
  sum_p := F.sum_p

@[simp] theorem phase_p (F : CKFamily G A) (c : E → unitary ℂ) (v : V) : (F.phase c).p v = F.p v :=
  rfl

@[simp] theorem phase_s (F : CKFamily G A) (c : E → unitary ℂ) (e : E) :
    (F.phase c).s e = (c e : ℂ) • F.s e := rfl

end CKFamily

/-- The representation with the same carrier and the phased family. -/
def CKRepresentation.phase {G : Graph V E} (R : CKRepresentation G) (c : E → unitary ℂ) :
    CKRepresentation G where
  carrier := R.carrier
  instCStarAlgebra := R.instCStarAlgebra
  instNontrivial := R.instNontrivial
  family := R.family.phase c

variable (G : Graph V E)

/-- Reindexing the ambient product along `R ↦ R.phase c`. -/
def ambientPhase (c : E → unitary ℂ) : CKAmbient G →⋆ₐ[ℂ] CKAmbient G where
  toFun f := ⟨fun R ↦ f (R.phase c), memℓp_infty ⟨‖f‖, by
    rintro _ ⟨R, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (R.phase c)⟩⟩
  map_one' := lp.ext rfl
  map_mul' _ _ := lp.ext rfl
  map_zero' := lp.ext rfl
  map_add' _ _ := lp.ext rfl
  commutes' _ := lp.ext rfl
  map_star' _ := lp.ext rfl

theorem ambientPhase_P (c : E → unitary ℂ) (v : V) : ambientPhase G c (ambientP G v) = ambientP G v :=
  lp.ext rfl

theorem ambientPhase_S (c : E → unitary ℂ) (e : E) :
    ambientPhase G c (ambientS G e) = (c e : ℂ) • ambientS G e :=
  lp.ext rfl

theorem graphCStarSubalgebra_le_comap (c : E → unitary ℂ) :
    graphCStarSubalgebra G ≤ (graphCStarSubalgebra G).comap (ambientPhase G c) := by
  refine StarSubalgebra.topologicalClosure_minimal (s := StarAlgebra.adjoin ℂ (ckGenerators G)) ?_ ?_
  · apply StarAlgebra.adjoin_le
    rintro _ (⟨v, rfl⟩ | ⟨e, rfl⟩)
    · show ambientPhase G c (ambientP G v) ∈ graphCStarSubalgebra G
      rw [ambientPhase_P]
      exact ambientP_mem G v
    · show ambientPhase G c (ambientS G e) ∈ graphCStarSubalgebra G
      rw [ambientPhase_S]
      exact (graphCStarSubalgebra G).smul_mem (ambientS_mem G e) _
  · exact IsClosed.preimage (map_continuous (ambientPhase G c)) (graphCStarSubalgebra_isClosed G)

/-- The endomorphism `p_v ↦ p_v`, `s_e ↦ c_e s_e` of `C*(G)`. -/
def phaseHom (c : E → unitary ℂ) : GraphCStarAlgebra G →⋆ₐ[ℂ] GraphCStarAlgebra G :=
  ((ambientPhase G c).comp (graphCStarSubalgebra G).subtype).codRestrict (graphCStarSubalgebra G)
    fun x ↦ (StarSubalgebra.mem_comap _ _ _).1 (graphCStarSubalgebra_le_comap G c x.2)

theorem phaseHom_p (c : E → unitary ℂ) (v : V) :
    phaseHom G c ((ckFamily G).p v) = (ckFamily G).p v :=
  Subtype.ext (ambientPhase_P G c v)

theorem phaseHom_s (c : E → unitary ℂ) (e : E) :
    phaseHom G c ((ckFamily G).s e) = (c e : ℂ) • (ckFamily G).s e :=
  Subtype.ext (ambientPhase_S G c e)

/-- Two endomorphisms of `C*(G)` agreeing on the generators are equal. This is `hom_ext` with the
instances of `GraphCStarAlgebra G →⋆ₐ[ℂ] GraphCStarAlgebra G` as synthesized for endomorphisms. -/
theorem endo_ext {φ ψ : GraphCStarAlgebra G →⋆ₐ[ℂ] GraphCStarAlgebra G}
    (hp : ∀ v, φ ((ckFamily G).p v) = ψ ((ckFamily G).p v))
    (hs : ∀ e, φ ((ckFamily G).s e) = ψ ((ckFamily G).s e)) : φ = ψ :=
  hom_ext G hp hs

theorem phaseHom_comp (c c' : E → unitary ℂ) :
    (phaseHom G c).comp (phaseHom G c') = phaseHom G (c * c') := by
  apply endo_ext G
  · intro v
    exact (congrArg (phaseHom G c) (phaseHom_p G c' v)).trans
      ((phaseHom_p G c v).trans (phaseHom_p G (c * c') v).symm)
  · intro e
    refine (congrArg (phaseHom G c) (phaseHom_s G c' e)).trans ?_
    rw [map_smul, phaseHom_s, phaseHom_s, smul_smul]
    exact congrArg (fun z : ℂ ↦ z • (ckFamily G).s e) (mul_comm _ _)

theorem phaseHom_one : phaseHom G 1 = StarAlgHom.id ℂ (GraphCStarAlgebra G) := by
  apply hom_ext G
  · intro v
    exact phaseHom_p G 1 v
  · intro e
    exact (phaseHom_s G 1 e).trans (one_smul ℂ _)

/-- The automorphism `p_v ↦ p_v`, `s_e ↦ c_e s_e` of `C*(G)`. -/
def phaseEquiv (c : E → unitary ℂ) : GraphCStarAlgebra G ≃⋆ₐ[ℂ] GraphCStarAlgebra G :=
  StarAlgEquiv.ofStarAlgHom (phaseHom G c) (phaseHom G c⁻¹)
    (by rw [phaseHom_comp, inv_mul_cancel, phaseHom_one])
    (by rw [phaseHom_comp, mul_inv_cancel, phaseHom_one])

theorem phaseEquiv_p (c : E → unitary ℂ) (v : V) :
    phaseEquiv G c ((ckFamily G).p v) = (ckFamily G).p v :=
  phaseHom_p G c v

theorem phaseEquiv_s (c : E → unitary ℂ) (e : E) :
    phaseEquiv G c ((ckFamily G).s e) = (c e : ℂ) • (ckFamily G).s e :=
  phaseHom_s G c e

/-- The gauge automorphism `γ_z`: `p_v ↦ p_v`, `s_e ↦ z s_e`. -/
def gaugeEquiv (z : unitary ℂ) : GraphCStarAlgebra G ≃⋆ₐ[ℂ] GraphCStarAlgebra G :=
  phaseEquiv G fun _ ↦ z

theorem gaugeEquiv_p (z : unitary ℂ) (v : V) :
    gaugeEquiv G z ((ckFamily G).p v) = (ckFamily G).p v :=
  phaseEquiv_p G _ v

theorem gaugeEquiv_s (z : unitary ℂ) (e : E) :
    gaugeEquiv G z ((ckFamily G).s e) = (z : ℂ) • (ckFamily G).s e :=
  phaseEquiv_s G _ e

section EdgePhase

variable [DecidableEq E]

/-- The automorphism multiplying the edge `e₀` by `z` and fixing every other generator. -/
def edgePhaseEquiv (e₀ : E) (z : unitary ℂ) : GraphCStarAlgebra G ≃⋆ₐ[ℂ] GraphCStarAlgebra G :=
  phaseEquiv G (Function.update 1 e₀ z)

theorem edgePhaseEquiv_p (e₀ : E) (z : unitary ℂ) (v : V) :
    edgePhaseEquiv G e₀ z ((ckFamily G).p v) = (ckFamily G).p v :=
  phaseEquiv_p G _ v

theorem edgePhaseEquiv_s_self (e₀ : E) (z : unitary ℂ) :
    edgePhaseEquiv G e₀ z ((ckFamily G).s e₀) = (z : ℂ) • (ckFamily G).s e₀ :=
  (phaseEquiv_s G (Function.update 1 e₀ z) e₀).trans (by rw [Function.update_self])

theorem edgePhaseEquiv_s_of_ne {e₀ e : E} (h : e ≠ e₀) (z : unitary ℂ) :
    edgePhaseEquiv G e₀ z ((ckFamily G).s e) = (ckFamily G).s e :=
  (phaseEquiv_s G (Function.update 1 e₀ z) e).trans (by
    rw [Function.update_of_ne h]
    exact one_smul ℂ _)

end EdgePhase

end GraphCStar
end GroupApproximation
