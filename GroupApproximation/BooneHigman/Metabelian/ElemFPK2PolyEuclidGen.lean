import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNFWiring
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegWeyl
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal forms for `K₂(F_p[X])`: the van der Waerden check on a small generating set

Lane `bh-met-92h`.  Notation of `ElemFPK2PolyNFStab`: `R = F_p[X]`, `K` a finset, `L ∉ K`,
`K' = K ∪ {L}`, `G = G_{K'}(R)`, `Q = S_K ⊔ V`, and `St_I(R)` acts on columns by `act`.

The target `k2PolyNF_CosetStatement` asks for a set map `σ` on the orbit `G e_L`, with
`σ(e_L) ∈ Q` and `σ(x v)⁻¹ x σ(v) ∈ Q` for **every** root `x = x_ij(a)`, `i, j ∈ K'`,
`a ∈ R`.  Call `g ∈ G` *good* (`k2PolyEuclid_Good`) when `σ(g v)⁻¹ g σ(v) ∈ Q` on the whole
orbit.

* `k2PolyEuclid_good_mul`, `k2PolyEuclid_good_inv`: good elements form a subgroup of `G`.
* **Generation.**  Fix `m ∈ K` and a third index `n ∉ {m, L}`.  Take the generators
  `x_im(1)`, `x_mi(1)` (`i ∈ K \ {m}`), `y = x_mL(1)`, and the one family `x_Lm(f)` (`f ∈ R`).
  They generate all of `G`:
  - `W = x_mL(1) x_Lm(-1) x_mL(1) = w_mL(1)`, and `x_mL(f) = W x_Lm(-f) W⁻¹`;
  - `x_iL(f) = ⁅x_im(1), x_mL(f)⁆` and `x_Lj(f) = ⁅x_Lm(f), x_mj(1)⁆`;
  - `x_ij(f) = ⁅x_iL(f), x_Lj(1)⁆` for `i, j ∈ K`.
  So if these generators are good, every root of `G` is good (`k2PolyEuclid_good_all`).
* `k2PolyEuclid_GenStatement` (**the residual**): a `σ` with `σ(e_L) ∈ Q` whose coset check
  holds for the `2(|K| - 1)` constant roots `x_im(1)`, `x_mi(1)`, for the constant root
  `x_mL(1)`, and for the single family `x_Lm(f)`.
* `k2PolyEuclid_coset_of_gen`: the residual gives `k2PolyNF_CosetStatement`.
  `k2PolyEuclid_gen_of_coset` gives the converse.
* `k2PolyEuclid_K2_eq_bot_of_gen`: the residual gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`.

**LOUD: EQUIVALENT IN LOGICAL STRENGTH, STRICTLY SMALLER IN PROOF CONTENT.**  The residual is a
sub-list of the checks in `k2PolyNF_CosetStatement` (`k2PolyEuclid_gen_of_coset`, trivial),
and implies it (`k2PolyEuclid_coset_of_gen`).  So it is *not* logically weaker.  What it removes
is proof content: `|K'| (|K'| - 1)` root families with arbitrary coefficients become
`2|K| - 1` constant roots plus the one family `x_Lm(f)`.  In the Euclidean normal form, that
family is the only generator that changes the degree of the leading row `L`.

**Truth.**  It is TRUE, because it is equivalent to `k2PolyNF_StabStatement`, which lane 92c
checked (matrix shadow `SL_K(F_p[X]) = E_K(F_p[X])`, plus the true `K₂(N, F_p[X]) = 0`).  The
matrix shadows of the five generation identities (with signs) were checked over `F_2` and
`F_3`, for coefficients of degree `≤ 2` in `3 × 3` and `4 × 4` matrices (scratchpad
`bh92h/chk.py`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (x_mem_rootSpan
  act unitVec act_mul act_one)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w x_congr)

variable {I : Type} [Fintype I] [DecidableEq I]

section Defs

variable (p : ℕ) [Fact p.Prime]

/-- The coset check of `g` against the set map `σ`, on the whole orbit `G e_L`. -/
def k2PolyEuclid_Check (K : Finset I) (L : I)
    (σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p)))
    (g : SteinbergGroup I (Polynomial (ZMod p))) : Prop :=
  ∀ v : I → Polynomial (ZMod p), (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) →
    (σ (act g v))⁻¹ * g * σ v ∈ k2PolyNF_Q p K L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_Check

/-- `g` is *good*: it lies in `G` and passes the coset check. -/
def k2PolyEuclid_Good (K : Finset I) (L : I)
    (σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p)))
    (g : SteinbergGroup I (Polynomial (ZMod p))) : Prop :=
  g ∈ k2PolyDeg_G p K L ∧ k2PolyEuclid_Check p K L σ g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_Good

end Defs

variable {p : ℕ} [Fact p.Prime]

/-- Every root `x_ij(a)` with `i, j ∈ K'` lies in `G`. -/
theorem k2PolyEuclid_x_mem_G {K : Finset I} {L i j : I} (hij : i ≠ j)
    (a : Polynomial (ZMod p)) (hi : i ∈ insert L K) (hj : j ∈ insert L K) :
    x i j hij a ∈ k2PolyDeg_G p K L :=
  x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ insert L K) hij a ⟨hi, hj⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_x_mem_G

/-- Good elements are closed under products. -/
theorem k2PolyEuclid_good_mul {K : Finset I} {L : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))}
    {g k : SteinbergGroup I (Polynomial (ZMod p))} (hg : k2PolyEuclid_Good p K L σ g)
    (hk : k2PolyEuclid_Good p K L σ k) : k2PolyEuclid_Good p K L σ (g * k) := by
  refine ⟨Subgroup.mul_mem _ hg.1 hk.1, fun v hv => ?_⟩
  have e : (σ (act (g * k) v))⁻¹ * (g * k) * σ v =
      ((σ (act g (act k v)))⁻¹ * g * σ (act k v)) * ((σ (act k v))⁻¹ * k * σ v) := by
    rw [act_mul]
    group
  rw [e]
  exact Subgroup.mul_mem _ (hg.2 (act k v) (k2PolyNF_orbit_act hk.1 hv)) (hk.2 v hv)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_good_mul

/-- Good elements are closed under inverses. -/
theorem k2PolyEuclid_good_inv {K : Finset I} {L : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))}
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : k2PolyEuclid_Good p K L σ g) :
    k2PolyEuclid_Good p K L σ g⁻¹ := by
  refine ⟨Subgroup.inv_mem _ hg.1, fun v hv => ?_⟩
  have h := hg.2 (act g⁻¹ v) (k2PolyNF_orbit_act (Subgroup.inv_mem _ hg.1) hv)
  have e1 : act g (act g⁻¹ v) = v := by
    rw [← act_mul, mul_inv_cancel, act_one]
  rw [e1] at h
  have e2 : (σ (act g⁻¹ v))⁻¹ * g⁻¹ * σ v = ((σ v)⁻¹ * g * σ (act g⁻¹ v))⁻¹ := by
    group
  rw [e2]
  exact Subgroup.inv_mem _ h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_good_inv

/-- Good elements are closed under commutators. -/
theorem k2PolyEuclid_good_comm {K : Finset I} {L : I}
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))}
    {g k : SteinbergGroup I (Polynomial (ZMod p))} (hg : k2PolyEuclid_Good p K L σ g)
    (hk : k2PolyEuclid_Good p K L σ k) : k2PolyEuclid_Good p K L σ ⁅g, k⁆ := by
  rw [commutatorElement_def]
  exact k2PolyEuclid_good_mul (k2PolyEuclid_good_mul (k2PolyEuclid_good_mul hg hk)
    (k2PolyEuclid_good_inv hg)) (k2PolyEuclid_good_inv hk)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyEuclid_good_comm
