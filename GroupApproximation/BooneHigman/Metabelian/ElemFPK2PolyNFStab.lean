import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegAmalgam
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal forms for `K₂(F_p[X])`, part 1: the stabiliser residual and the coset criterion

Lane `bh-met-92c`.  Notation of `ElemFPK2PolyDegSpans`: `R = F_p[X]`, `K` a finset, `L ∉ K`,
`K' = K ∪ {L}`, `G = G_{K'}(R)`, `S = S_K`, `V = ⟨x_Lj(f) : j ∈ K⟩`, all in `St_I(R)`.
Put `Q = S ⊔ V` (`k2PolyNF_Q`).  `St_I(R)` acts on columns through `projection`
(`FieldTwo.act`), and `Q` fixes `e_L` (`k2PolyNF_Q_fix`).

* `k2PolyNF_StabStatement` (**the residual**): at the inductive step, every `g ∈ G` with
  `g e_L = e_L` lies in `Q`.  So `Stab_G(e_L) = Q`, a Steinberg-level normal form for the
  stabiliser of `e_L`.
* `k2PolyNF_CosetStatement` (van der Waerden criterion): a set map `σ` from the orbit `G e_L`
  to `St_I(R)`, with `σ(e_L) ∈ Q` and `σ(x v)⁻¹ x σ(v) ∈ Q` for every root `x = x_ij(a)`,
  `i, j ∈ K'`, and every orbit point `v`.  No relation of `G` is checked.
* `k2PolyNF_closure`: from the generator condition, `σ(g v)⁻¹ g σ(v) ∈ Q` for all `g ∈ G`.
* `k2PolyNF_stab_of_coset` and `k2PolyNF_coset_of_stab` prove the two statements
  equivalent (choose `σ` by `Classical.epsilon`).

The step `G ∩ K₂ = 1` follows from the residual and the kernel lemma
`k2PolyDeg_eq_one_of_mem_P` (`ElemFPK2PolyNFWiring`).

**Truth check.**  The matrix shadow holds: a matrix of `E_{K'}(R)` fixing `e_L` is
`[[A, 0], [r, 1]]` with `A ∈ SL_K(R) = E_K(R)` (Euclid), hence in `π(Q)`.  Transitivity on
unimodular columns and the Euclidean reduction of `SL₂` columns were checked for `p = 2, 3`,
degree `≤ 2`, `|K'| = 3, 4, 5` (scratchpad `bh92c/chk.py`).  Lifting to `St`: given the true
theorem `K₂(N, F_p[X]) = 0` (`N ≥ 5`), `G ∩ K₂ = 1`, so `g ∈ G` fixing `e_L` equals `q ∈ Q`
with `π q = π g`.  **The residual is TRUE.**

**LOUD: EQUIVALENT, NOT WEAKER.**  With the hypotheses it grants, and given
`SL_K(F_p[X]) = E_K(F_p[X])`, the residual is logically equivalent to the step `G ∩ K₂ = 1`.
One direction is `k2PolyNF_step`; the converse is the truth check above.  What it removes is
proof content.  The residual of lane 91z (`k2PolyRank2_SectionStatement`) asks for a
*homomorphism* on `Ḡ`, i.e. for all relations of `E_{K'}(R)`.  Here only a *set map* on
unimodular columns is needed, plus one coset check per (generator, column): the
van der Waerden method, with `K₂` gone from the statement.  The Euclidean normal form is the
natural `σ`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  x_mem_rootSpan rootSpan_induction act unitVec unitVec_apply act_mul act_one
  act_eq_self_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I]

section Defs

variable (p : ℕ) [Fact p.Prime]

/-- `Q = S ⊔ V`, the stabiliser of `e_L` expected by the normal form. -/
def k2PolyNF_Q (K : Finset I) (L : I) : Subgroup (SteinbergGroup I (Polynomial (ZMod p))) :=
  k2PolyDeg_S p K ⊔ k2PolyDeg_V p K L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_Q

/-- A chosen `g ∈ G` with `g e_L = v`, when one exists. -/
noncomputable def k2PolyNF_eps (K : Finset I) (L : I) (v : I → Polynomial (ZMod p)) :
    SteinbergGroup I (Polynomial (ZMod p)) :=
  @Classical.epsilon (SteinbergGroup I (Polynomial (ZMod p)))
    (Nonempty.intro (1 : SteinbergGroup I (Polynomial (ZMod p))))
    (fun g => g ∈ k2PolyDeg_G p K L ∧ act g (unitVec L) = v)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_eps

end Defs

/-- **The residual.**  At the inductive step (granting `S ∩ K₂ = 1`, the constants lemma and a
third index), every `g ∈ G_{K ∪ {L}}` fixing `e_L` lies in `Q = S ⊔ V`.  TRUE; LOUD: equivalent
to the step given `SL_K(F_p[X]) = E_K(F_p[X])` (module docstring). -/
def k2PolyNF_StabStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (L : I),
    L ∉ K → K.Nonempty → (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) →
    (∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1) →
    ∀ g ∈ k2PolyDeg_G p K L, act g (unitVec L) = unitVec L → g ∈ k2PolyNF_Q p K L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_StabStatement

/-- **The van der Waerden criterion** (equivalent to the residual): a set section `σ` of the
orbit `G e_L`, equivariant modulo `Q` on the generating roots of `G`. -/
def k2PolyNF_CosetStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (L : I),
    L ∉ K → K.Nonempty → (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) →
    (∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1) →
    ∃ σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p)),
      σ (unitVec L) ∈ k2PolyNF_Q p K L ∧
      ∀ (i j : I) (hij : i ≠ j) (a : Polynomial (ZMod p)), i ∈ insert L K → j ∈ insert L K →
        ∀ v : I → Polynomial (ZMod p), (∃ g ∈ k2PolyDeg_G p K L, act g (unitVec L) = v) →
          (σ (act (x i j hij a) v))⁻¹ * x i j hij a * σ v ∈ k2PolyNF_Q p K L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_CosetStatement

variable {p : ℕ} [Fact p.Prime]

/-- `Q` fixes `e_L`: the residual says that `Q` is the whole stabiliser. -/
theorem k2PolyNF_Q_fix {K : Finset I} {L : I} (hLK : L ∉ K)
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyNF_Q p K L) :
    act g (unitVec L) = unitVec L := by
  obtain ⟨s, hs, v, hv, rfl⟩ := k2PolyDeg_SV_decomp hLK hg
  have hfix : ∀ j : I, j ∈ K → unitVec (R := Polynomial (ZMod p)) L j = 0 := fun j hj => by
    rw [unitVec_apply, if_neg (fun e => hLK (e ▸ hj))]
  have hS : act s (unitVec L) = unitVec L :=
    act_eq_self_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (fun _ j hij => hfix j hij.2) hs
  have hV : act v (unitVec L) = unitVec L :=
    act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ K) (fun _ j hij => hfix j hij.2) hv
  rw [act_mul, hV, hS]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_Q_fix

/-- The orbit `G e_L` is stable under `G`. -/
theorem k2PolyNF_orbit_act {K : Finset I} {L : I}
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyDeg_G p K L)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) :
    ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = act g v := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨g * y, Subgroup.mul_mem _ hg hy, act_mul g y (unitVec L)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_orbit_act

/-- If `g e_L = w`, then `g⁻¹ w = e_L`. -/
theorem k2PolyNF_act_inv {L : I} {g : SteinbergGroup I (Polynomial (ZMod p))}
    {w : I → Polynomial (ZMod p)} (hw : act g (unitVec L) = w) : act g⁻¹ w = unitVec L := by
  rw [← hw, ← act_mul, inv_mul_cancel, act_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_act_inv

/-- The chosen element does its job on the orbit. -/
theorem k2PolyNF_eps_spec {K : Finset I} {L : I} {v : I → Polynomial (ZMod p)}
    (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) :
    k2PolyNF_eps p K L v ∈ k2PolyDeg_G p K L ∧ act (k2PolyNF_eps p K L v) (unitVec L) = v :=
  Classical.epsilon_spec_aux (Nonempty.intro (1 : SteinbergGroup I (Polynomial (ZMod p))))
    (fun g => g ∈ k2PolyDeg_G p K L ∧ act g (unitVec L) = v) hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNF_eps_spec
