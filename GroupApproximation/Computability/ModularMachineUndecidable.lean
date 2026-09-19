import GroupApproximation.Computability.QuadMachineTM0
import GroupApproximation.Computability.UniversalMachineUndecidable
import GroupApproximation.Computability.MarkovPost

/-!
# S9: a modular machine whose halting set is not computable

This is Simpson's Theorem 4, the one input his write-up leaves to the reader.
Everything it needs is now in place:

* `Computability.QuadMachine` reads a modular machine as a machine on two stacks
  of digits and shows that such a machine's halting --- *reaching* `(0,0)`,
  after the erasure --- is the two-stack machine's running out of instructions.
* `Computability.QuadMachineTM0` puts a Post--Turing machine on those stacks.
* `Computability.UniversalMachineUndecidable` supplies a `TM0` machine whose
  halting on an encoded input is not decidable in that input.

Chaining the three gives a single modular machine and a map `ℕ → ℕ²` along
which halting is undecidable.  There is no hypothesis and no literature input:
the undecidable source is Mathlib's `ComputablePred.halting_problem`, reached
through Mathlib's own `PartrecToTM2` compiler.
-/

namespace GroupApproximation
namespace Computability

open Turing Turing.PartrecToTM2

namespace TMData

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

/-- Naming the alphabet and the states by numbers, given that both are
finite. -/
noncomputable def ofFintype (Γ Λ : Type) [Inhabited Γ] [Fintype Γ] [Inhabited Λ]
    [Fintype Λ] : TMData Γ Λ where
  nsym := Fintype.card Γ
  nstΛ := Fintype.card Λ + 1
  encodeSym γ := (Fintype.equivFin Γ γ : ℕ) + 1
  decode d := if h : 0 < d ∧ d - 1 < Fintype.card Γ then
      (Fintype.equivFin Γ).symm ⟨d - 1, h.2⟩ else default
  encodeSt q := (Fintype.equivFin Λ q : ℕ)
  decodeSt d := if h : d < Fintype.card Λ then
      (Fintype.equivFin Λ).symm ⟨d, h⟩ else default
  decode_encodeSym γ := by
    have h : 0 < (Fintype.equivFin Γ γ : ℕ) + 1 ∧
        ((Fintype.equivFin Γ γ : ℕ) + 1) - 1 < Fintype.card Γ := by
      refine ⟨Nat.succ_pos _, ?_⟩
      simp
    rw [dif_pos h]
    simp
  encodeSym_pos γ := Nat.succ_le_succ (Nat.zero_le _)
  encodeSym_le γ := (Fintype.equivFin Γ γ).isLt
  decode_zero := by
    rw [dif_neg]
    rintro ⟨h, -⟩
    exact absurd h (lt_irrefl 0)
  decodeSt_encodeSt q := by
    rw [dif_pos (Fintype.equivFin Λ q).isLt]
    simp
  encodeSt_lt q := lt_trans (Fintype.equivFin Λ q).isLt (Nat.lt_succ_self _)

variable (D : TMData Γ Λ)

omit [Inhabited Λ] in
theorem map_decode_encodeSym : ∀ l : List Γ, (l.map D.encodeSym).map D.decode = l
  | [] => rfl
  | a :: l => by
      rw [List.map_cons, List.map_cons, D.decode_encodeSym, map_decode_encodeSym l]

omit [Inhabited Λ] in
theorem decode_headI_map (l : List Γ) :
    D.decode ((l.map D.encodeSym).headI) = l.headI := by
  cases l with
  | nil => simpa using D.decode_zero
  | cons a l => simpa using D.decode_encodeSym a

/-- The two-stack configuration a `TM0` input starts from: the whole input on
the scanned stack, nothing behind, the initial state facing right. -/
def initQCfg (l : List Γ) : QCfg :=
  ⟨[], l.map D.encodeSym, D.stIdx default false true, true⟩

theorem rep_initQCfg (M : TM0.Machine Γ Λ) (l : List Γ) :
    D.Rep M (D.initQCfg l) (TM0.init l) := by
  refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · rintro d ⟨⟩
  · intro d hd
    obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hd
    exact ⟨D.encodeSym_pos γ, D.encodeSym_le γ⟩
  · exact D.stIdx_lt _ _ _
  · show D.decode ((l.map D.encodeSym).headI) = (TM0.init l).Tape.head
    rw [D.decode_headI_map]
    simp [TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk']
  · show ListBlank.mk (((l.map D.encodeSym).tail).map D.decode) = (TM0.init l).Tape.right
    have h1 : (l.map D.encodeSym).tail = l.tail.map D.encodeSym := by cases l <;> simp
    rw [h1, D.map_decode_encodeSym]
    simp [TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk']
  · show ListBlank.mk ((([] : List ℕ)).map D.decode) = (TM0.init l).Tape.left
    simp [TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk']

theorem tmHalts_iff_eval_dom (M : TM0.Machine Γ Λ) (l : List Γ) :
    TMHalts M (TM0.init l) ↔ (TM0.eval M l).Dom := by
  constructor
  · rintro ⟨X, hreach, hnone⟩
    have hX : X ∈ StateTransition.eval (TM0.step M) (TM0.init l) := by
      rw [StateTransition.mem_eval]
      exact ⟨hreach, hnone⟩
    rw [TM0.eval]
    exact Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ hX⟩
  · intro h
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
    rw [TM0.eval, Part.mem_map_iff] at hb
    obtain ⟨X, hX, -⟩ := hb
    rw [StateTransition.mem_eval] at hX
    exact ⟨X, hX.1, hX.2⟩

/-- **The whole simulation, in one statement.**  The modular machine of a
Post--Turing machine reaches `(0,0)` from the encoded input exactly when the
Post--Turing machine halts on it. -/
theorem modular_halts_iff_eval_dom (M : TM0.Machine Γ Λ) (l : List Γ) :
    (D.toQuad M).toModular.Halts ((D.toQuad M).encCfg (D.initQCfg l))
      ↔ (TM0.eval M l).Dom := by
  have hrep := D.rep_initQCfg M l
  rw [QuadMachine.halts_encCfg_iff _ hrep.wf, D.QHalts_iff_TMHalts hrep,
    tmHalts_iff_eval_dom]

end TMData

/-! ## Restricting to a supported set of states

The `TM0` machine that Mathlib's compiler produces has state type
`Option (TM1.Stmt Γ Λ σ) × σ`, which contains function types and carries no
`Fintype` instance --- and a two-stack machine needs to number its states.  What
`TM0.Supports` gives is a *finite* set of states the machine cannot leave, so
the machine is replaced by its restriction to that set.

The restriction is defined without any dependency on the closure: out-of-range
states are clamped to the default.  Closure is used only in the proofs, where it
says the clamp never fires. -/

namespace TM0Restrict

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {S : Finset Λ}
  [Inhabited {q // q ∈ S}]

/-- A state of `S`, or the default one. -/
noncomputable def clamp (q : Λ) : {q // q ∈ S} :=
  letI := Classical.dec (q ∈ S)
  if h : q ∈ S then ⟨q, h⟩ else default

omit [Inhabited Λ] in
theorem clamp_val {q : Λ} (h : q ∈ S) : (clamp (S := S) q).1 = q := by
  simp only [clamp]
  rw [dif_pos h]

/-- The machine, restricted to a finite set of states. -/
noncomputable def restrict (M : TM0.Machine Γ Λ) (S : Finset Λ)
    [Inhabited {q // q ∈ S}] : TM0.Machine Γ {q // q ∈ S} :=
  fun q a => (M q.1 a).map fun p => (clamp p.1, p.2)

/-- Forgetting the restriction. -/
def unrestrict (X : TM0.Cfg Γ {q // q ∈ S}) : TM0.Cfg Γ Λ := ⟨X.q.1, X.Tape⟩

theorem step_unrestrict (M : TM0.Machine Γ Λ)
    (hsup : TM0.Supports M (S : Set Λ)) (X : TM0.Cfg Γ {q // q ∈ S}) :
    (TM0.step (restrict M S) X).map unrestrict = TM0.step M (unrestrict X) := by
  obtain ⟨q, T⟩ := X
  show ((restrict M S q T.head).map _).map unrestrict = (M q.1 T.head).map _
  cases h : M q.1 T.head with
  | none => simp [restrict, h]
  | some p =>
      obtain ⟨q', st⟩ := p
      have hq' : q' ∈ S := hsup.2 (Option.mem_def.mpr h) (Finset.mem_coe.mpr q.2)
      show ((((M q.1 T.head).map _).map _).map unrestrict) = _
      rw [h]
      simp only [Option.map_some]
      show (some (⟨(clamp (S := S) q').1, _⟩ : TM0.Cfg Γ Λ)) = _
      rw [clamp_val hq']

theorem step_eq_none_iff (M : TM0.Machine Γ Λ)
    (hsup : TM0.Supports M (S : Set Λ)) (X : TM0.Cfg Γ {q // q ∈ S}) :
    TM0.step (restrict M S) X = none ↔ TM0.step M (unrestrict X) = none := by
  rw [← step_unrestrict M hsup X]
  cases TM0.step (restrict M S) X <;> simp

theorem reaches_unrestrict (M : TM0.Machine Γ Λ)
    (hsup : TM0.Supports M (S : Set Λ)) {X Y : TM0.Cfg Γ {q // q ∈ S}}
    (h : TM0.Reaches (restrict M S) X Y) :
    TM0.Reaches M (unrestrict X) (unrestrict Y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      rename_i B C _
      refine Relation.ReflTransGen.tail ih ?_
      have hB : TM0.step (restrict M S) B = some C := hstep
      have hmap := step_unrestrict M hsup B
      rw [hB] at hmap
      exact hmap.symm

theorem exists_reaches_restrict (M : TM0.Machine Γ Λ)
    (hsup : TM0.Supports M (S : Set Λ)) {X : TM0.Cfg Γ {q // q ∈ S}}
    {Y : TM0.Cfg Γ Λ} (h : TM0.Reaches M (unrestrict X) Y) :
    ∃ Y', TM0.Reaches (restrict M S) X Y' ∧ unrestrict Y' = Y := by
  induction h with
  | refl => exact ⟨X, Relation.ReflTransGen.refl, rfl⟩
  | tail _ hstep ih =>
      rename_i B C _
      obtain ⟨Y', hY', hYB⟩ := ih
      have hBC : TM0.step M B = some C := hstep
      have hmap := step_unrestrict M hsup Y'
      rw [hYB, hBC] at hmap
      rcases hY'' : TM0.step (restrict M S) Y' with _ | Y''
      · rw [hY''] at hmap; exact absurd hmap (by simp)
      · rw [hY''] at hmap
        exact ⟨Y'', Relation.ReflTransGen.tail hY' hY'', Option.some.inj hmap⟩

theorem tmHalts_iff (M : TM0.Machine Γ Λ)
    (hsup : TM0.Supports M (S : Set Λ)) (X : TM0.Cfg Γ {q // q ∈ S}) :
    TMData.TMHalts (restrict M S) X ↔ TMData.TMHalts M (unrestrict X) := by
  constructor
  · rintro ⟨Y, hreach, hnone⟩
    exact ⟨unrestrict Y, reaches_unrestrict M hsup hreach,
      (step_eq_none_iff M hsup Y).1 hnone⟩
  · rintro ⟨Y, hreach, hnone⟩
    obtain ⟨Y', hY', rfl⟩ := exists_reaches_restrict M hsup hreach
    exact ⟨Y', hY', (step_eq_none_iff M hsup Y').2 hnone⟩

end TM0Restrict

/-- **S9, Simpson's Theorem 4.**  There is a modular machine and a map from `ℕ`
to configurations along which halting is not decidable.

Unconditional: no hypothesis, and no literature input. -/
theorem exists_modularMachine_halting_not_computablePred (n : ℕ) :
    ∃ (mm : BooneGroup.ModularMachine) (f : ℕ → ℕ × ℕ),
      ¬ ComputablePred fun m : ℕ => mm.Halts (f m) := by
  classical
  obtain ⟨c, hc⟩ := tm0_halting_not_computablePred n
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  letI : Fintype (TM2to1.Γ' K' (fun _ : K' => Γ')) := TM2to1.Γ'.fintype
  -- Mathlib's support chain: TM2, then TM1, then TM0
  have hs2 : TM2.Supports tr (codeSupp c Cont'.halt) := tr_supports c Cont'.halt
  have hs1 := TM2to1.tr_supports tr hs2
  have hs0 := TM1to0.tr_supports (TM2to1.tr tr) hs1
  set M₀ := TM1to0.tr (TM2to1.tr tr) with hM₀
  set S₀ := TM1to0.trStmts (TM2to1.tr tr) (TM2to1.trSupp tr (codeSupp c Cont'.halt))
    with hS₀
  have hdef : (default : TM1to0.Λ' (TM2to1.tr tr)) ∈ S₀ := hs0.1
  letI : Inhabited {q // q ∈ S₀} := ⟨⟨default, hdef⟩⟩
  set M₁ := TM0Restrict.restrict M₀ S₀ with hM₁
  set D := TMData.ofFintype (TM2to1.Γ' K' (fun _ : K' => Γ')) {q // q ∈ S₀} with hD
  have hinit : ∀ l : List (TM2to1.Γ' K' (fun _ : K' => Γ')),
      TM0Restrict.unrestrict (TM0.init l : TM0.Cfg _ {q // q ∈ S₀}) = TM0.init l :=
    fun _ => rfl
  refine ⟨(D.toQuad M₁).toModular,
    fun m => (D.toQuad M₁).encCfg (D.initQCfg (TM2to1.trInit K'.main (trList [m]))), ?_⟩
  intro hcomp
  refine hc ?_
  have hkey : ∀ m : ℕ, ((D.toQuad M₁).toModular.Halts
      ((D.toQuad M₁).encCfg (D.initQCfg (TM2to1.trInit K'.main (trList [m]))))
      ↔ (TM0.eval M₀ (TM2to1.trInit K'.main (trList [m]))).Dom) := by
    intro m
    rw [QuadMachine.halts_encCfg_iff _ (D.rep_initQCfg M₁ _).wf,
      D.QHalts_iff_TMHalts (D.rep_initQCfg M₁ _),
      TM0Restrict.tmHalts_iff M₀ hs0, hinit,
      TMData.tmHalts_iff_eval_dom]
  have hEq : (fun m : ℕ => (D.toQuad M₁).toModular.Halts
        ((D.toQuad M₁).encCfg (D.initQCfg (TM2to1.trInit K'.main (trList [m])))))
      = fun m : ℕ => (TM0.eval M₀ (TM2to1.trInit K'.main (trList [m]))).Dom :=
    funext fun m => propext (hkey m)
  exact hEq ▸ hcomp

end Computability
end GroupApproximation
