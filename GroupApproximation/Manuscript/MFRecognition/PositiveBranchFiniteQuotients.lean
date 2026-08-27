import GroupApproximation.GroupTheory.HNNBrittonPinch
import GroupApproximation.Manuscript.MFRecognition.RecognitionInputs
import GroupApproximation.Sofic.FiniteResidualKernel
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SemidirectProduct

/-!
# `lem:positive-branch`: the finite quotients, in full

This module proves, with no open leaves, the group-theoretic half of the
printed proof of `lem:positive-branch` --- the paragraph beginning "The group
`P = F(x_1,y) × F(x_2,t)` is residually finite" and ending with the displayed
kernel inclusion.  Nothing analytic occurs here; the output is exactly the
hypothesis list of `lem:tensor-sync`.

The printed steps, in order:

1. "choose finite-index normal subgroups `P_1 ≥ P_2 ≥ ⋯` of `P` with trivial
   intersection, let `r_n : P → C_n = P/P_n`, and put `β_n = r_n ∘ j`"
   --- `DescendingFiniteIndexChain`, `proj`, `beta`;
2. "Since `j` is injective and the `P_n` decrease to the trivial group, every
   `h ≠ 1` has `β_n(h) ≠ 1` for all large `n`" --- `beta_ne_one_eventually`;
3. "Let `G_n = (C_n × C_n) ⋊ ⟨σ⟩`, where `σ` of order two exchanges the
   coordinates" --- `SwapProduct`, `sigmaElt`;
4. "Define `λ_n` on `K_e = K⁰_e × (F × P)` by killing `K⁰_e` and sending
   `(f,p)` to `(r_n j q_+(f), r_n(p))`, and put `λ_n(v) = σ`.  This respects
   the relations of `eq:central-rope`" --- `baseHom`,
   `baseHom_diagonal_of_mem_ropeEdge`, `ropeLambda`;
5. the two displayed values `λ_n(i(f)) = (r_n j q_+(f), 1)` and
   `λ_n(v i(f) v⁻¹) = (1, r_n j q_+(f))` --- `ropeLambda_ropeGen`,
   `ropeLambda_ropeGenConj`;
6. "`λ_n|_{S_e} = (r_n j π_0, r_n j π_1)`, both sides being homomorphisms that
   agree on generators" --- `ropeLambda_restrict_eq`;
7. "`ker(λ_n|_{S_e}) = ker(r_n j π_0) ∩ ker(r_n j π_1) ≤ ker(β_n ∘ α_e)`"
   --- `ker_ropeLambda_restrict` and `ker_ropeLambda_restrict_le`.

Because `σ` has order two, `λ_n(v)` is the same element whether the printed
stable letter `v` is read as Mathlib's `HNNExtension.t` or as its inverse;
`ropeLambda_stable_inv` records this.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Recognition

/-! ## 1.  The printed chain `P_1 ≥ P_2 ≥ ⋯` and the maps `r_n`, `β_n` -/

/-- **"choose finite-index normal subgroups `P_1 ≥ P_2 ≥ ⋯` of `P` with
trivial intersection".**  Finite index is recorded in the equivalent form
"the quotient is finite". -/
structure DescendingFiniteIndexChain (P : Type) [Group P] where
  /-- The subgroups `P_n`. -/
  sub : ℕ → Subgroup P
  /-- Each `P_n` is normal. -/
  normal : ∀ n, (sub n).Normal
  /-- `P_1 ≥ P_2 ≥ ⋯`. -/
  antitone : ∀ n, sub (n + 1) ≤ sub n
  /-- Each `P_n` has finite index. -/
  finite_quotient : ∀ n, Finite (P ⧸ sub n)
  /-- The intersection is trivial. -/
  iInf_eq_bot : (⨅ n, sub n) = ⊥

namespace DescendingFiniteIndexChain

variable {P : Type} [Group P] (T : DescendingFiniteIndexChain P)

instance instNormalSub (n : ℕ) : (T.sub n).Normal := T.normal n

/-- The printed finite quotient `C_n = P/P_n`. -/
abbrev Quot (n : ℕ) : Type := P ⧸ T.sub n

instance instFiniteQuot (n : ℕ) : Finite (T.Quot n) := T.finite_quotient n

/-- The printed `r_n : P → C_n`. -/
def proj (n : ℕ) : P →* T.Quot n := QuotientGroup.mk' (T.sub n)

theorem sub_antitone : Antitone T.sub := antitone_nat_of_succ_le T.antitone

theorem proj_eq_one_iff (n : ℕ) (p : P) : T.proj n p = 1 ↔ p ∈ T.sub n :=
  QuotientGroup.eq_one_iff p

/-- "the `P_n` decrease to the trivial group": every nonidentity element of
`P` survives in `C_n` for all large `n`. -/
theorem proj_ne_one_eventually {p : P} (hp : p ≠ 1) :
    ∃ N, ∀ n, N ≤ n → T.proj n p ≠ 1 := by
  have hmem : ¬ ∀ n, p ∈ T.sub n := by
    intro hall
    apply hp
    have hbot : p ∈ (⨅ n, T.sub n) := Subgroup.mem_iInf.mpr hall
    rw [T.iInf_eq_bot] at hbot
    exact Subgroup.mem_bot.mp hbot
  push Not at hmem
  obtain ⟨N, hN⟩ := hmem
  refine ⟨N, fun n hn hcon => hN ?_⟩
  exact T.sub_antitone hn ((T.proj_eq_one_iff n p).mp hcon)

/-- The printed `β_n = r_n ∘ j`. -/
def beta {Qp : Type} [Group Qp] (j : Qp →* P) (n : ℕ) : Qp →* T.Quot n :=
  (T.proj n).comp j

@[simp] theorem beta_apply {Qp : Type} [Group Qp] (j : Qp →* P) (n : ℕ)
    (q : Qp) : T.beta j n q = T.proj n (j q) := rfl

/-- **"Since `j` is injective and the `P_n` decrease to the trivial group,
every `h ≠ 1` has `β_n(h) ≠ 1` for all large `n`."** -/
theorem beta_ne_one_eventually {Qp : Type} [Group Qp] (j : Qp →* P)
    (hj : Function.Injective j) {h : Qp} (hh : h ≠ 1) :
    ∃ N, ∀ n, N ≤ n → T.beta j n h ≠ 1 := by
  have hjh : j h ≠ 1 := fun hcon => hh (hj (hcon.trans (map_one j).symm))
  exact T.proj_ne_one_eventually hjh

end DescendingFiniteIndexChain

/-- The chain the printed proof chooses exists for every countable residually
finite group.  The `n`-th subgroup is the kernel of the product of the first
`n` chosen finite quotients, so the chain is decreasing by construction, each
quotient embeds in a finite group, and an element surviving nowhere in the
chain survives in no finite quotient at all. -/
theorem exists_descendingFiniteIndexChain (P : Type) [Group P] [Countable P]
    [Group.ResiduallyFinite P] :
    Nonempty (DescendingFiniteIndexChain P) := by
  classical
  obtain ⟨g, hg⟩ := exists_surjective_nat P
  haveI hfintop : Finite (P ⧸ (⊤ : Subgroup P)) := by
    refine Finite.of_surjective (fun _ : PUnit => (1 : P ⧸ (⊤ : Subgroup P))) ?_
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨PUnit.unit, ((QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_top y)).symm⟩
  have hchoice : ∀ n : ℕ, ∃ N : Subgroup P,
      N.Normal ∧ Finite (P ⧸ N) ∧ (g n ≠ 1 → g n ∉ N) := by
    intro n
    by_cases hn : g n = 1
    · exact ⟨⊤, inferInstance, hfintop, fun hcon => absurd hn hcon⟩
    · obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem (g n) hn
      letI := N.isNormal'
      letI := N.isFiniteIndex'
      haveI : Finite (P ⧸ N.toSubgroup) :=
        Subgroup.finite_quotient_of_finiteIndex
      exact ⟨N.toSubgroup, N.isNormal', inferInstance, fun _ => hN⟩
  choose N hNnormal hNfinite hNsep using hchoice
  letI : ∀ n, (N n).Normal := hNnormal
  letI : ∀ n, Finite (P ⧸ N n) := hNfinite
  let d : ∀ n, P →* (P ⧸ N n) := fun n => QuotientGroup.mk' (N n)
  let block : ∀ n : ℕ, P →* (∀ k : Fin n, P ⧸ N (k : ℕ)) := fun n =>
    { toFun := fun p k => d (k : ℕ) p
      map_one' := by
        funext k
        exact map_one (d (k : ℕ))
      map_mul' := fun a b => by
        funext k
        exact map_mul (d (k : ℕ)) a b }
  refine ⟨{ sub := fun n => (block n).ker
            normal := fun n => inferInstance
            antitone := ?_
            finite_quotient := ?_
            iInf_eq_bot := ?_ }⟩
  · intro n p hp
    rw [MonoidHom.mem_ker] at hp ⊢
    funext k
    exact congrFun hp (⟨(k : ℕ), Nat.lt_succ_of_lt k.isLt⟩ : Fin (n + 1))
  · intro n
    haveI : Finite (∀ k : Fin n, P ⧸ N (k : ℕ)) := inferInstance
    exact Finite.of_equiv _
      (QuotientGroup.quotientKerEquivRange (block n)).symm.toEquiv
  · rw [Subgroup.eq_bot_iff_forall]
    intro p hp
    by_contra hp1
    obtain ⟨n, hn⟩ := hg p
    have hmem : p ∈ (block (n + 1)).ker := (Subgroup.mem_iInf.mp hp) (n + 1)
    rw [MonoidHom.mem_ker] at hmem
    have hd : d n p = 1 :=
      congrFun hmem (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
    have hgn : g n ≠ 1 := by
      rw [hn]
      exact hp1
    refine hNsep n hgn ?_
    rw [hn]
    exact (QuotientGroup.eq_one_iff p).mp hd

/-! ## 2.  The finite group `G_n = (C_n × C_n) ⋊ ⟨σ⟩` -/

/-- The coordinate exchange of `C × C`, an automorphism of order two. -/
def swapAut (C : Type) [Group C] : MulAut (C × C) where
  toFun x := (x.2, x.1)
  invFun x := (x.2, x.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem swapAut_apply (C : Type) [Group C] (x : C × C) :
    swapAut C x = (x.2, x.1) := rfl

theorem swapAut_mul_self (C : Type) [Group C] :
    swapAut C * swapAut C = 1 := by
  apply MulEquiv.ext
  intro x
  rfl

private theorem zmod_two_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

/-- The value of the printed action of `⟨σ⟩` at an element of `ℤ/2`. -/
def swapVal (C : Type) [Group C] (x : ZMod 2) : MulAut (C × C) :=
  if x = 0 then 1 else swapAut C

@[simp] theorem swapVal_zero (C : Type) [Group C] :
    swapVal C 0 = 1 := if_pos rfl

@[simp] theorem swapVal_one (C : Type) [Group C] :
    swapVal C 1 = swapAut C := if_neg (by decide)

theorem swapVal_add (C : Type) [Group C] (x y : ZMod 2) :
    swapVal C (x + y) = swapVal C x * swapVal C y := by
  rcases zmod_two_cases x with rfl | rfl
  · rcases zmod_two_cases y with rfl | rfl
    · rw [show (0 : ZMod 2) + 0 = 0 from by decide, swapVal_zero, one_mul]
    · rw [show (0 : ZMod 2) + 1 = 1 from by decide, swapVal_zero,
        swapVal_one, one_mul]
  · rcases zmod_two_cases y with rfl | rfl
    · rw [show (1 : ZMod 2) + 0 = 1 from by decide, swapVal_zero,
        swapVal_one, mul_one]
    · rw [show (1 : ZMod 2) + 1 = 0 from by decide, swapVal_zero,
        swapVal_one, swapAut_mul_self]

/-- **"`σ` of order two exchanges the coordinates"**, as an action of the
two-element group on `C × C`. -/
def swapAction (C : Type) [Group C] :
    Multiplicative (ZMod 2) →* MulAut (C × C) where
  toFun a := swapVal C (Multiplicative.toAdd a)
  map_one' := swapVal_zero C
  map_mul' a b :=
    swapVal_add C (Multiplicative.toAdd a) (Multiplicative.toAdd b)

/-- **The printed finite group `G_n = (C_n × C_n) ⋊ ⟨σ⟩`.** -/
abbrev SwapProduct (C : Type) [Group C] : Type :=
  (C × C) ⋊[swapAction C] Multiplicative (ZMod 2)

/-- The printed generator `σ` of the complement `⟨σ⟩`. -/
def sigmaElt (C : Type) [Group C] : SwapProduct C :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

/-- `G_n` is finite whenever `C_n` is. -/
theorem finite_swapProduct (C : Type) [Group C] [Finite C] :
    Finite (SwapProduct C) := inferInstance

theorem sigmaElt_mul_self (C : Type) [Group C] :
    sigmaElt C * sigmaElt C = 1 := by
  show SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) *
      SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) = 1
  rw [← map_mul]
  have h : Multiplicative.ofAdd (1 : ZMod 2) *
      Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
    have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    calc Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)
        = Multiplicative.ofAdd ((1 : ZMod 2) + 1) := (ofAdd_add _ _).symm
      _ = Multiplicative.ofAdd (0 : ZMod 2) := by rw [h2]
      _ = 1 := rfl
  rw [h, map_one]

/-- `σ⁻¹ = σ`, so the printed stable letter and its inverse have the same
image in `G_n`. -/
theorem sigmaElt_inv (C : Type) [Group C] : (sigmaElt C)⁻¹ = sigmaElt C :=
  inv_eq_of_mul_eq_one_right (sigmaElt_mul_self C)

/-- Conjugating by `σ` exchanges the two coordinates. -/
theorem sigma_conj_inl (C : Type) [Group C] (x : C × C) :
    sigmaElt C * SemidirectProduct.inl x * (sigmaElt C)⁻¹ =
      SemidirectProduct.inl (x.2, x.1) := by
  have hact : swapAction C (Multiplicative.ofAdd (1 : ZMod 2)) x = (x.2, x.1) := by
    show swapVal C (1 : ZMod 2) x = (x.2, x.1)
    simp only [swapVal_one, swapAut_apply]
  have h := SemidirectProduct.inl_aut (φ := swapAction C)
    (Multiplicative.ofAdd (1 : ZMod 2)) x
  rw [hact] at h
  show SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) *
      SemidirectProduct.inl x *
      (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹ =
    SemidirectProduct.inl (x.2, x.1)
  rw [← map_inv, h]

/-- "an element `(f, jq_+(f))` of `L^{\mathrm g}` is sent to
`(r_n jq_+(f), r_n jq_+(f))`, which lies on the diagonal and commutes with
`σ`." -/
theorem sigma_mul_inl_diagonal (C : Type) [Group C] (c : C) :
    sigmaElt C * SemidirectProduct.inl ((c, c) : C × C) =
      SemidirectProduct.inl ((c, c) : C × C) * sigmaElt C := by
  have h := sigma_conj_inl C ((c, c) : C × C)
  calc sigmaElt C * SemidirectProduct.inl ((c, c) : C × C)
      = sigmaElt C * SemidirectProduct.inl ((c, c) : C × C) * (sigmaElt C)⁻¹ *
          sigmaElt C := by group
    _ = SemidirectProduct.inl ((c, c) : C × C) * sigmaElt C := by rw [h]

/-! ## 3.  `λ_n` on the base, and the relation check -/

section Lambda

variable {K0 F P C : Type} [Group K0] [Group F] [Group P] [Group C]

/-- **"Define `λ_n` on `K_e = K⁰_e × (F × P)` by killing `K⁰_e` and sending
`(f,p)` to `(r_n jq_+(f), r_n(p))`."** -/
def baseHom (psi : F →* P) (r : P →* C) : RopeBase K0 F P →* C × C :=
  ((r.comp psi).comp
      ((MonoidHom.fst F P).comp (MonoidHom.snd K0 (F × P)))).prod
    (r.comp ((MonoidHom.snd F P).comp (MonoidHom.snd K0 (F × P))))

@[simp] theorem baseHom_apply (psi : F →* P) (r : P →* C)
    (x : RopeBase K0 F P) :
    baseHom psi r x = (r (psi x.2.1), r x.2.2) := rfl

/-- **"the factor `L⁰_e` of `L_e` lies in `K⁰_e` and is killed, and an element
`(f, jq_+(f))` of `L^{\mathrm g}` is sent to `(r_n jq_+(f), r_n jq_+(f))`,
which lies on the diagonal"**. -/
theorem baseHom_diagonal_of_mem_ropeEdge (L0 : Subgroup K0) (psi : F →* P)
    (r : P →* C) {x : RopeBase K0 F P} (hx : x ∈ ropeEdge L0 psi) :
    (baseHom psi r x).1 = (baseHom psi r x).2 := by
  obtain ⟨-, hgraph⟩ := Subgroup.mem_prod.mp hx
  obtain ⟨f, hf⟩ := (mem_ropeGraph_iff psi x.2).mp hgraph
  have h1 : x.2.1 = f := (congrArg Prod.fst hf).symm
  have h2 : x.2.2 = psi f := (congrArg Prod.snd hf).symm
  show r (psi x.2.1) = r x.2.2
  rw [h1, h2]

/-- **`λ_n : Γ_e → G_n`.**  "This respects the relations of
`eq:central-rope` ... So `λ_n : Γ_e → G_n` is a homomorphism." -/
def ropeLambda (L0 : Subgroup K0) (psi : F →* P) (r : P →* C) :
    CentralRope L0 psi →* SwapProduct C :=
  HNNExtension.lift
    ((SemidirectProduct.inl : (C × C) →* SwapProduct C).comp (baseHom psi r))
    (sigmaElt C)
    (by
      intro a
      show sigmaElt C *
          SemidirectProduct.inl (baseHom psi r (a : RopeBase K0 F P)) =
        SemidirectProduct.inl (baseHom psi r (a : RopeBase K0 F P)) *
          sigmaElt C
      have hdiag := baseHom_diagonal_of_mem_ropeEdge L0 psi r a.2
      have hpair : baseHom psi r (a : RopeBase K0 F P) =
          ((baseHom psi r (a : RopeBase K0 F P)).1,
            (baseHom psi r (a : RopeBase K0 F P)).1) :=
        Prod.ext rfl hdiag.symm
      calc sigmaElt C *
            SemidirectProduct.inl (baseHom psi r (a : RopeBase K0 F P))
          = sigmaElt C *
              SemidirectProduct.inl
                ((baseHom psi r (a : RopeBase K0 F P)).1,
                  (baseHom psi r (a : RopeBase K0 F P)).1) := by
                rw [← hpair]
        _ = SemidirectProduct.inl
                ((baseHom psi r (a : RopeBase K0 F P)).1,
                  (baseHom psi r (a : RopeBase K0 F P)).1) * sigmaElt C :=
              sigma_mul_inl_diagonal C _
        _ = SemidirectProduct.inl (baseHom psi r (a : RopeBase K0 F P)) *
              sigmaElt C := by rw [← hpair])

theorem ropeLambda_of (L0 : Subgroup K0) (psi : F →* P) (r : P →* C)
    (x : RopeBase K0 F P) :
    ropeLambda L0 psi r (HNNExtension.of x) =
      SemidirectProduct.inl (baseHom psi r x) := by
  have h : ropeLambda L0 psi r (HNNExtension.of x) =
      ((SemidirectProduct.inl : (C × C) →* SwapProduct C).comp
        (baseHom psi r)) x := by
    unfold ropeLambda
    rw [HNNExtension.lift_of]
  exact h

/-- **"put `λ_n(v) = σ`."** -/
theorem ropeLambda_stable (L0 : Subgroup K0) (psi : F →* P) (r : P →* C) :
    ropeLambda L0 psi r (ropeStable L0 psi) = sigmaElt C := by
  unfold ropeLambda ropeStable
  rw [HNNExtension.lift_t]

/-- `σ` has order two, so the printed value `λ_n(v) = σ` is unchanged if the
manuscript's stable letter `v` is realized as the inverse of Mathlib's
`HNNExtension.t`. -/
theorem ropeLambda_stable_inv (L0 : Subgroup K0) (psi : F →* P) (r : P →* C) :
    ropeLambda L0 psi r (ropeStable L0 psi)⁻¹ = sigmaElt C := by
  rw [map_inv, ropeLambda_stable, sigmaElt_inv]

/-- **The first displayed value: `λ_n(i(f)) = (r_n jq_+(f), 1)`.** -/
theorem ropeLambda_ropeGen (L0 : Subgroup K0) (psi : F →* P) (r : P →* C)
    (i0 : F →* K0) (f : F) :
    ropeLambda L0 psi r (ropeGen L0 psi i0 f) =
      SemidirectProduct.inl ((r (psi f), 1) : C × C) := by
  have h : ropeLambda L0 psi r (ropeGen L0 psi i0 f) =
      SemidirectProduct.inl (baseHom psi r (ropeEmbedding i0 f)) :=
    ropeLambda_of L0 psi r _
  have hbase : baseHom psi r (ropeEmbedding i0 f) = ((r (psi f), 1) : C × C) := by
    show ((r (psi f), r 1) : C × C) = (r (psi f), 1)
    rw [map_one]
  rw [h, hbase]

/-- **The second displayed value: `λ_n(v i(f) v⁻¹) = (1, r_n jq_+(f))`.** -/
theorem ropeLambda_ropeGenConj (L0 : Subgroup K0) (psi : F →* P) (r : P →* C)
    (i0 : F →* K0) (f : F) :
    ropeLambda L0 psi r (ropeGenConj L0 psi i0 f) =
      SemidirectProduct.inl ((1, r (psi f)) : C × C) := by
  rw [ropeGenConj_apply, map_mul, map_mul, map_inv, ropeLambda_stable,
    ropeLambda_ropeGen]
  exact sigma_conj_inl C ((r (psi f), 1) : C × C)

end Lambda

/-! ## 4.  The restriction to `S_e` and the kernel inclusion -/

/-- Two homomorphisms out of a group agreeing on a generating set agree. -/
theorem hom_ext_of_closure_eq_top {G A : Type} [Group G] [Group A]
    {gens : Set G} (hgens : Subgroup.closure gens = ⊤) {Phi Psi : G →* A}
    (h : ∀ x ∈ gens, Phi x = Psi x) : Phi = Psi := by
  ext x
  have hx : x ∈ Subgroup.closure gens := by
    rw [hgens]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => rw [map_one, map_one]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]
  | inv y _ hy => rw [map_inv, map_inv, hy]

section Restriction

variable {K0 F P C Qp : Type} [Group K0] [Group F] [Group P] [Group C]
  [Group Qp]

/-- The printed generators of `S_e`, read inside `S_e`, generate it. -/
theorem ropeSubgroup_closure_preimage_eq_top (L0 : Subgroup K0)
    (psi : F →* P) (i0 : F →* K0) :
    Subgroup.closure
        (((↑) : ↥(ropeSubgroup L0 psi i0) → CentralRope L0 psi) ⁻¹'
          (Set.range (ropeGen L0 psi i0) ∪
            Set.range (ropeGenConj L0 psi i0))) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

/-- **"The displayed formulas show that `λ_n|_{S_e} = (r_n j π_0, r_n j π_1)`,
both sides being homomorphisms that agree on generators."**

Here `beta` is the printed `β_n = r_n ∘ j`, `pi0` is `π_0 = α_e` and `pi1` is
`π_1`, both read through the identification `Q_e = Q_+` of the infinite
branch; `psi` is the printed `j q_+`, so that `beta ∘ q_+ = r_n j q_+`. -/
theorem ropeLambda_restrict_eq (L0 : Subgroup K0) (psi : F →* P) (r : P →* C)
    (i0 : F →* K0) (qplus : F →* Qp) (beta : Qp →* C)
    (pi0 pi1 : ↥(ropeSubgroup L0 psi i0) →* Qp)
    (hpsi : ∀ f : F, r (psi f) = beta (qplus f))
    (hpi0gen : ∀ f : F, pi0 (ropeGenS L0 psi i0 f) = qplus f)
    (hpi0conj : ∀ f : F, pi0 (ropeGenConjS L0 psi i0 f) = 1)
    (hpi1gen : ∀ f : F, pi1 (ropeGenS L0 psi i0 f) = 1)
    (hpi1conj : ∀ f : F, pi1 (ropeGenConjS L0 psi i0 f) = qplus f) :
    (ropeLambda L0 psi r).comp (ropeSubgroup L0 psi i0).subtype =
      (SemidirectProduct.inl : (C × C) →* SwapProduct C).comp
        ((beta.comp pi0).prod (beta.comp pi1)) := by
  refine hom_ext_of_closure_eq_top
    (ropeSubgroup_closure_preimage_eq_top L0 psi i0) ?_
  rintro x (⟨f, hf⟩ | ⟨f, hf⟩)
  · have hxe : x = ropeGenS L0 psi i0 f := Subtype.ext hf.symm
    subst hxe
    show ropeLambda L0 psi r (ropeGen L0 psi i0 f) =
      SemidirectProduct.inl
        (beta (pi0 (ropeGenS L0 psi i0 f)), beta (pi1 (ropeGenS L0 psi i0 f)))
    rw [ropeLambda_ropeGen, hpi0gen, hpi1gen, map_one, hpsi]
  · have hxe : x = ropeGenConjS L0 psi i0 f := Subtype.ext hf.symm
    subst hxe
    show ropeLambda L0 psi r (ropeGenConj L0 psi i0 f) =
      SemidirectProduct.inl
        (beta (pi0 (ropeGenConjS L0 psi i0 f)),
          beta (pi1 (ropeGenConjS L0 psi i0 f)))
    rw [ropeLambda_ropeGenConj, hpi0conj, hpi1conj, map_one, hpsi]

/-- **"`ker(λ_n|_{S_e}) = ker(r_n j π_0) ∩ ker(r_n j π_1)`."** -/
theorem ker_ropeLambda_restrict (L0 : Subgroup K0) (psi : F →* P) (r : P →* C)
    (i0 : F →* K0) (qplus : F →* Qp) (beta : Qp →* C)
    (pi0 pi1 : ↥(ropeSubgroup L0 psi i0) →* Qp)
    (hpsi : ∀ f : F, r (psi f) = beta (qplus f))
    (hpi0gen : ∀ f : F, pi0 (ropeGenS L0 psi i0 f) = qplus f)
    (hpi0conj : ∀ f : F, pi0 (ropeGenConjS L0 psi i0 f) = 1)
    (hpi1gen : ∀ f : F, pi1 (ropeGenS L0 psi i0 f) = 1)
    (hpi1conj : ∀ f : F, pi1 (ropeGenConjS L0 psi i0 f) = qplus f) :
    ((ropeLambda L0 psi r).comp (ropeSubgroup L0 psi i0).subtype).ker =
      (beta.comp pi0).ker ⊓ (beta.comp pi1).ker := by
  rw [ropeLambda_restrict_eq L0 psi r i0 qplus beta pi0 pi1 hpsi hpi0gen
    hpi0conj hpi1gen hpi1conj]
  ext s
  constructor
  · intro hs
    have hpair : ((beta.comp pi0).prod (beta.comp pi1)) s = 1 :=
      SemidirectProduct.inl_injective (by
        rw [map_one]
        exact MonoidHom.mem_ker.mp hs)
    exact Subgroup.mem_inf.mpr
      ⟨MonoidHom.mem_ker.mpr (congrArg Prod.fst hpair),
        MonoidHom.mem_ker.mpr (congrArg Prod.snd hpair)⟩
  · intro hmem
    obtain ⟨h0, h1⟩ := Subgroup.mem_inf.mp hmem
    refine MonoidHom.mem_ker.mpr ?_
    have hpair : ((beta.comp pi0).prod (beta.comp pi1)) s = 1 := by
      have e0 : (beta.comp pi0) s = 1 := MonoidHom.mem_ker.mp h0
      have e1 : (beta.comp pi1) s = 1 := MonoidHom.mem_ker.mp h1
      show (((beta.comp pi0) s, (beta.comp pi1) s) : C × C) = 1
      rw [e0, e1]
      rfl
    show SemidirectProduct.inl (((beta.comp pi0).prod (beta.comp pi1)) s) = 1
    rw [hpair, map_one]

/-- **The hypothesis of `lem:tensor-sync`:
`ker(λ_n|_{S_e}) ≤ ker(β_n ∘ α_e)`.**  With `π_0 = α_e` this is the printed
inclusion of an intersection in its first factor. -/
theorem ker_ropeLambda_restrict_le (L0 : Subgroup K0) (psi : F →* P)
    (r : P →* C) (i0 : F →* K0) (qplus : F →* Qp) (beta : Qp →* C)
    (pi0 pi1 : ↥(ropeSubgroup L0 psi i0) →* Qp)
    (hpsi : ∀ f : F, r (psi f) = beta (qplus f))
    (hpi0gen : ∀ f : F, pi0 (ropeGenS L0 psi i0 f) = qplus f)
    (hpi0conj : ∀ f : F, pi0 (ropeGenConjS L0 psi i0 f) = 1)
    (hpi1gen : ∀ f : F, pi1 (ropeGenS L0 psi i0 f) = 1)
    (hpi1conj : ∀ f : F, pi1 (ropeGenConjS L0 psi i0 f) = qplus f) :
    ((ropeLambda L0 psi r).comp (ropeSubgroup L0 psi i0).subtype).ker ≤
      (beta.comp pi0).ker := by
  rw [ker_ropeLambda_restrict L0 psi r i0 qplus beta pi0 pi1 hpsi hpi0gen
    hpi0conj hpi1gen hpi1conj]
  exact inf_le_left

end Restriction

/-! ## 5.  Why `V` does not extend faithfully (key `0377d8ab7ef4`) -/

section Faithfulness

variable {K0 F P C : Type} [Group K0] [Group F] [Group P] [Group C]

/-- **The printed reason: "the finite maps `λ_n` are trivial on the Mihailova
factor".**

`K⁰_e` is the first factor of `K_e = K⁰_e × (F × P)`, and `λ_n` was defined by
killing it, so the composite `K⁰_e → K_e → Γ_e → G_n` is trivial. -/
theorem sentence_0377d8ab7ef4_reason (L0 : Subgroup K0) (psi : F →* P)
    (r : P →* C) (k : K0) :
    ropeLambda L0 psi r
        (HNNExtension.of (MonoidHom.inl K0 (F × P) k)) = 1 := by
  have hbase : baseHom psi r (MonoidHom.inl K0 (F × P) k) = (1 : C × C) := by
    show ((r (psi 1), r 1) : C × C) = 1
    rw [map_one, map_one]
    rfl
  calc ropeLambda L0 psi r (HNNExtension.of (MonoidHom.inl K0 (F × P) k))
      = SemidirectProduct.inl (baseHom psi r (MonoidHom.inl K0 (F × P) k)) :=
        ropeLambda_of L0 psi r _
    _ = SemidirectProduct.inl (1 : C × C) := by rw [hbase]
    _ = 1 := map_one _

/-- **"although `u` does not commute with `(γ,1)` in `R_e`".**

Britton's lemma for `eq:twisted-rope`: the stable letter conjugates the base
copy back into itself only on the edge subgroup `{(s,1) : s ∈ S_e}`, so a `γ`
outside `S_e` is moved. -/
theorem stable_not_commute_of_notMem {Gamma Q : Type} [Group Gamma] [Group Q]
    (S : Subgroup Gamma) (tau : ↥S →* Q) {gamma : Gamma} (hgamma : gamma ∉ S) :
    (HNNExtension.t : TwistedHNN S tau) *
          HNNExtension.of ((gamma, 1) : Gamma × Q) *
        (HNNExtension.t : TwistedHNN S tau)⁻¹ ≠
      HNNExtension.of ((gamma, 1) : Gamma × Q) := by
  intro hcon
  have hnot : ((gamma, 1) : Gamma × Q) ∉ edgeSubgroupSource S Q := by
    intro hmem
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hmem
    have hfst : (s : Gamma) = gamma := congrArg Prod.fst hs
    refine hgamma ?_
    rw [← hfst]
    exact s.2
  refine HNNBritton.t_conj_notMem_range (edgeMulEquiv S tau) hnot ?_
  rw [hcon]
  exact MonoidHom.mem_range.mpr ⟨(gamma, 1), rfl⟩

/-- **Sentence `0377d8ab7ef4`.**

"The homomorphism `V` of `lem:tensor-sync` does not extend faithfully to `R_e`
in the corona: the finite maps `λ_n` are trivial on the Mihailova factor, so
`W` commutes with `V(γ,1)` for every `γ ∈ K⁰_e`, although `u` does not commute
with `(γ,1)` in `R_e`.  Injectivity is obtained in `thm:hnn-permanence` from
the universal algebra."

The assertable content is stated here as printed: *any* homomorphism out of
`R_e` whose value at `u` commutes with its value at `(γ,1)` fails to be
injective, as soon as `γ ∉ S_e`.  The hypothesis `hcomm` is the printed middle
clause: for `γ` in the Mihailova factor, `λ_n(γ) = 1`
(`sentence_0377d8ab7ef4_reason`), so the coordinate conjugators `W_n` of
`lem:tensor-sync` — which act only through `λ_n` and `β_n` — commute with
`V(γ,1)`.  The last printed sentence is a pointer, not an assertion:
injectivity of the realization of `R_e` comes from the universal C-star HNN
algebra in `thm:hnn-permanence`, not from the covariant pair `(ιρ, W)`. -/
theorem sentence_0377d8ab7ef4 {Gamma Q M : Type} [Group Gamma] [Group Q]
    [Group M] (S : Subgroup Gamma) (tau : ↥S →* Q)
    (Phi : TwistedHNN S tau →* M) {gamma : Gamma} (hgamma : gamma ∉ S)
    (hcomm : Commute (Phi HNNExtension.t)
      (Phi (HNNExtension.of ((gamma, 1) : Gamma × Q)))) :
    ¬ Function.Injective Phi := by
  intro hinj
  have hcomm' : Phi HNNExtension.t *
        Phi (HNNExtension.of ((gamma, 1) : Gamma × Q)) =
      Phi (HNNExtension.of ((gamma, 1) : Gamma × Q)) * Phi HNNExtension.t :=
    hcomm
  refine stable_not_commute_of_notMem S tau hgamma (hinj ?_)
  rw [map_mul, map_mul, map_inv, hcomm', mul_assoc, mul_inv_cancel, mul_one]

end Faithfulness

end Recognition
end MFRecognition
end Manuscript
end GroupApproximation
