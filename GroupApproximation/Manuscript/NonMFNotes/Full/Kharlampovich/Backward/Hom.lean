import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Backward.Carrier
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Backward.Letters

/-!
# The KMS model group on generators

Input for the "if" direction of KMS Theorem `tmm`(b) (`l654`, `l789` of
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4.1), used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`.

The model group acts on `Fn K (Cls M) × 𝔽_2`.  The letter `x_{q_j ∏_{i ∈ S} A_i}`
acts by the translation by the evaluation at `(v0, [q_j ∏_{i ∈ S} A_i])`, where
`v0` is the constant vector `z1`.  A letter of `L_1 ∪ L_2` acts by `liftP` of its
permutation `genH`.  This file defines the resulting homomorphism `mF` on the free
group, the homomorphism `mH` of `genH`, and the subgroup `E` where `mF = liftP ∘ mH`.
All letters of `L_1 ∪ L_2` lie in `E`.  It also records the values of the letter
permutations at active classes.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Backward

variable {K N : ℕ}

/-- The base vector `v0 = (z1, …, z1)` (KMS `l789`). -/
def v0 : Fin K → Tri := fun _ ↦ .z1

theorem v0_apply (n : Fin K) : v0 n = .z1 := rfl

theorem update_v0 (n : Fin K) : Function.update v0 n .z1 = v0 :=
  Function.update_eq_self n v0

/-- Evaluation at `(v, c)`. -/
def ev {C : Type*} (v : Fin K → Tri) (c : C) : Fn K C → ZMod 2 := fun φ ↦ φ v c

theorem ev_apply {C : Type*} (v : Fin K → Tri) (c : C) (φ : Fn K C) : ev v c φ = φ v c := rfl

/-- The class of the word `q_j ∏_{i ∈ S} A_i` (KMS `l654`). -/
def xCls (M : Minsky.Machine K N) (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) : Cls M :=
  Quot.mk (R M) ⟨j, fun _ ↦ 0, S⟩

/-- The permutations of the model carrier. -/
abbrev MPerm (M : Minsky.Machine K N) : Type := Equiv.Perm (Fn K (Cls M) × ZMod 2)

/-- The model action of the generators (KMS `l789`). -/
def genMap (M : Minsky.Machine K N) : KhGen K N → MPerm M
  | .x j S => tau (ev v0 (xCls M j S))
  | .bigA i => liftP (genH M (.bigA i))
  | .a n => liftP (genH M (.a n))
  | .a' n => liftP (genH M (.a' n))
  | .ta n => liftP (genH M (.ta n))
  | .ta' n => liftP (genH M (.ta' n))

/-- The model homomorphism on the free group. -/
def mF (M : Minsky.Machine K N) : FreeGroup (KhGen K N) →* MPerm M :=
  FreeGroup.lift (genMap M)

/-- The homomorphism of the permutations `genH` of the letters. -/
def mH (M : Minsky.Machine K N) : FreeGroup (KhGen K N) →* Equiv.Perm (Fn K (Cls M)) :=
  FreeGroup.lift (genH M)

variable {M : Minsky.Machine K N}

/-! ## Letters -/

theorem mF_of (s : KhGen K N) : mF M (FreeGroup.of s) = genMap M s :=
  FreeGroup.lift_apply_of

theorem mH_of (s : KhGen K N) : mH M (FreeGroup.of s) = genH M s :=
  FreeGroup.lift_apply_of

theorem mF_gx (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) :
    mF M (gx j S) = tau (ev v0 (xCls M j S)) :=
  FreeGroup.lift_apply_of

theorem mF_gA (i : Fin (K + 1)) : mF M (gA i) = liftP (pB M i) :=
  FreeGroup.lift_apply_of

theorem mF_ga (n : Fin K) : mF M (ga n) = liftP (Small.perm M ⟨n, false, false⟩) :=
  FreeGroup.lift_apply_of

theorem mF_ga' (n : Fin K) : mF M (ga' n) = liftP (Small.perm M ⟨n, false, true⟩) :=
  FreeGroup.lift_apply_of

theorem mF_gta (n : Fin K) : mF M (gta n) = liftP (Small.perm M ⟨n, true, false⟩) :=
  FreeGroup.lift_apply_of

theorem mF_gta' (n : Fin K) : mF M (gta' n) = liftP (Small.perm M ⟨n, true, true⟩) :=
  FreeGroup.lift_apply_of

theorem mH_gA (i : Fin (K + 1)) : mH M (gA (N := N) i) = pB M i :=
  FreeGroup.lift_apply_of

theorem mH_ga (n : Fin K) : mH M (ga (N := N) n) = Small.perm M ⟨n, false, false⟩ :=
  FreeGroup.lift_apply_of

theorem mH_ga' (n : Fin K) : mH M (ga' (N := N) n) = Small.perm M ⟨n, false, true⟩ :=
  FreeGroup.lift_apply_of

theorem mH_gta (n : Fin K) : mH M (gta (N := N) n) = Small.perm M ⟨n, true, false⟩ :=
  FreeGroup.lift_apply_of

theorem mH_gta' (n : Fin K) : mH M (gta' (N := N) n) = Small.perm M ⟨n, true, true⟩ :=
  FreeGroup.lift_apply_of

/-- A letter of a block acts through its permutation. -/
theorem genMap_of_block : ∀ (s : KhGen K N) (i : Fin (K + 1)), s.block = some i →
    genMap M s = liftP (genH M s)
  | .x _ _, _, h => by simp only [KhGen.block, reduceCtorEq] at h
  | .bigA _, _, _ => rfl
  | .a _, _, _ => rfl
  | .a' _, _, _ => rfl
  | .ta _, _, _ => rfl
  | .ta' _, _, _ => rfl

/-! ## The subgroup where the model factors through `genH` -/

/-- The elements on which `mF` is `liftP` of `mH`. -/
def E (M : Minsky.Machine K N) : Subgroup (FreeGroup (KhGen K N)) :=
  (mF M).eqLocus (MonoidHom.comp liftP (mH M))

theorem mem_E {x : FreeGroup (KhGen K N)} : x ∈ E M ↔ mF M x = liftP (mH M x) := Iff.rfl

theorem of_mem_E (s : KhGen K N) (i : Fin (K + 1)) (h : s.block = some i) :
    FreeGroup.of s ∈ E M := by
  rw [mem_E, mF_of, mH_of, genMap_of_block s i h]

theorem mF_eq_one_of {r : FreeGroup (KhGen K N)} (hr : r ∈ E M) (h : mH M r = 1) :
    mF M r = 1 := by
  rw [mem_E.1 hr, h, map_one]

/-! ## Closure of subgroups -/

theorem khConj_mem {G : Type*} [Group G] (S : Subgroup G) {u g : G} (hu : u ∈ S)
    (hg : g ∈ S) : khConj u g ∈ S := by
  show g⁻¹ * u * g ∈ S
  exact S.mul_mem (S.mul_mem (S.inv_mem hg) hu) hg

theorem khComm_mem {G : Type*} [Group G] (S : Subgroup G) {u v : G} (hu : u ∈ S)
    (hv : v ∈ S) : khComm u v ∈ S := by
  show u⁻¹ * v⁻¹ * u * v ∈ S
  exact S.mul_mem (S.mul_mem (S.mul_mem (S.inv_mem hu) (S.inv_mem hv)) hu) hv

theorem zword_mem (S : Subgroup (FreeGroup (KhGen K N))) {t : Fin K → FreeGroup (KhGen K N)}
    (ht : ∀ n, t n ∈ S) (α : Fin K → Fin 3) : zword t α ∈ S := by
  unfold zword
  suffices h : ∀ (L : List (Fin K)) (h0 : FreeGroup (KhGen K N)), h0 ∈ S →
      List.foldl (fun (h : FreeGroup (KhGen K N)) (n : Fin K) ↦
        h * t n ^ (((α n).val : ℤ) - 1)) h0 L ∈ S from
    h _ 1 S.one_mem
  intro L
  induction L with
  | nil => exact fun _ h ↦ h
  | cons n L ih =>
    intro h0 h
    rw [List.foldl_cons]
    exact ih _ (S.mul_mem h (S.zpow_mem (ht n) _))

/-! ## Values at active classes -/

theorem perm_of_act (u : Small K) (φ : Fn K (Cls M)) (v : Fin K → Tri) {c : Cls M}
    (hc : actB M u.blk c) :
    Small.perm M u φ v c =
      u.tab.app (v u.n) (fun s ↦ φ (Function.update v u.n s) c) (φ v (u.sig M c)) := by
  rw [Small.perm_apply]
  exact if_pos hc

theorem perm_inv_of_act (u : Small K) (φ : Fn K (Cls M)) (v : Fin K → Tri) {c : Cls M}
    (hc : actB M u.blk c) :
    (Small.perm M u)⁻¹ φ v c =
      u.tabi.app (v u.n) (fun s ↦ φ (Function.update v u.n s) c) (φ v (u.sig M c)) := by
  rw [Small.perm_inv_apply]
  exact if_pos hc

theorem pB_of_act (i : Fin (K + 1)) (φ : Fn K (Cls M)) (v : Fin K → Tri) {c : Cls M}
    (hc : actB M i c) : pB M i φ v c = φ v c + φ v (Cls.appBig i c) := by
  rw [pB_apply]
  exact if_pos hc

/-- Without the flags `A_0` and `A_{n+1}`, the tilde letters act as the plain ones
(the input for G6). -/
theorem perm_tilde_eq (n : Fin K) (p : Bool) (φ : Fn K (Cls M)) (v : Fin K → Tri)
    {c : Cls M} (h1 : actB M n.succ c) (h0 : actB M 0 c) :
    Small.perm M ⟨n, true, p⟩ φ v c = Small.perm M ⟨n, false, p⟩ φ v c := by
  have e : Cls.appT n c = Cls.appA n c := Cls.appT_eq_appA_of n c h1 h0
  rw [perm_of_act ⟨n, true, p⟩ φ v h0, perm_of_act ⟨n, false, p⟩ φ v h1]
  exact congrArg
    (fun d ↦ (cond p tAp tA).app (v n) (fun s ↦ φ (Function.update v n s) c) (φ v d)) e

end Backward

end KMS

end GroupApproximation.Full.Kharlampovich
