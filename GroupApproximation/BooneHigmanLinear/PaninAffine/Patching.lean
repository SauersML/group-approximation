import GroupApproximation.BooneHigmanLinear.PaninAffine.PatchFrame
import GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29
import GroupApproximation.Meta.AxiomGuard

/-!
# F.4: Zariski excision for `St_r`, from Tulenbaev's `X_{v,w}(t)` (lane k2-panin)

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Math. USSR Sb. 45 (1983), Prop 1.4(b),
read at source (pp. 141–142). Let `r ≥ 5`, and let `a, b ∈ A` be comaximal non-zero-divisors. Then
compatible elements of `St_r(A_a)` and `St_r(A_b)` come from `St_r(A)`. The case `(1, β)` is
`PaninAffine.StZariskiExcisionAt A r`, the input `hExc` of Cor 2.9 (`PaninAffine.Cor29`) and of
Horrocks's monic injectivity (`TulenbaevHorrocks.Reductions`).

**The proof** (`stZariskiExcisionAt_of_tulX`). By `PaninAffine.PatchFrame`, the operators
`T_ij(c)` are well defined on the orbit set `V = St(A_a) × St(A_b) / St(A)`. Here we check the three
Steinberg relations:
* `Tfun_add`: `T_ij(c) T_ij(c') = T_ij(c + c')`;
* `Tfun_comm`: `[T_ij, T_kl] = 1` for `j ≠ k`, `l ≠ i`, via `TulX.commute_X`;
* `Tfun_adj`: `[T_ij(c), T_jk(c')] = T_ik(cc')`. This is the one relation Tulenbaev writes out.
  The `A_b` parts are handled through a matrix frame (`MFrame`). The row change is `TulX.rowAdd`
  (`MFrame.row_split`), the column change is `TulX.colAdd` with Lemma 1.2 (`MFrame.col_split`,
  `K2Found.TwoZero`), and the commutator is `TulX.conj` (`MFrame.conj_jk_ij`).

So `St_r(A_{ab})` acts on `V` (`act`), and `jb(h)·[1, β] = [1, hβ]` (`act_jb`). If `β` dies in
`St_r(A_{ab})`, then `[1, β] = [1, 1]`, which says exactly that `β` comes from some `γ ∈ St(A)`
with `γ_a = 1`.

**Input:** `TulX r`, Tulenbaev's `X_{v,w}(t)` with T 1.1–1.3 (bh-pal-linear-char0). Not root-wired.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman Matrix
open scoped commutatorElement

section Relations

variable {r : ℕ} (T : TulX r) {A : Type} [CommRing A] {a b : A}

theorem mk_pair_eq {P Q : StPair r a b} (h1 : P.1 = Q.1) (h2 : P.2 = Q.2) :
    (Quotient.mk (patchSetoid r a b) P : PatchV r a b) = Quotient.mk _ Q := by
  rw [Prod.ext h1 h2]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.mk_pair_eq

theorem split_rescale {C : Type*} [CommRing C] (y s : C) {N N' n : ℕ} (h : N' + n = N) :
    y ^ N * s = y ^ N' * (y ^ n * s) := by
  rw [← mul_assoc, ← pow_add, h]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.split_rescale

theorem frame_orth (ha : a ∈ nonZeroDivisors A) {α : SteinbergGroup (Fin r) (Localization.Away a)}
    {i j k l : Fin r} {Φ Ψ : Frame A r} (hΦ : IsFrame a Φ (colOf α i) (rowOf α j))
    (hΨ : IsFrame a Ψ (colOf α k) (rowOf α l)) (h : l ≠ i) : Ψ.w ⬝ᵥ Φ.v = 0 := by
  apply loc_injective ha
  rw [map_zero, ← comp_dotProduct, hΨ.2.1, hΦ.1, smul_dotProduct, dotProduct_smul,
    rowOf_dot_colOf, Pi.single_eq_of_ne h, smul_zero, smul_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.frame_orth

theorem Xf_orth (ha : a ∈ nonZeroDivisors A) {α : SteinbergGroup (Fin r) (Localization.Away a)}
    {i j k l : Fin r} {Φ Ψ : Frame A r} (hΦ : IsFrame a Φ (colOf α i) (rowOf α j))
    (hΨ : IsFrame a Ψ (colOf α k) (rowOf α l)) (h : l ≠ i) {C : Type} [CommRing C]
    (f : A →+* C) : (f ∘ (a ^ Ψ.p • Ψ.w)) ⬝ᵥ (f ∘ Φ.v) = 0 := by
  rw [comp_dotProduct, smul_dotProduct, frame_orth ha hΦ hΨ h, smul_zero, map_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Xf_orth

theorem Xf_commute (ha : a ∈ nonZeroDivisors A)
    {α : SteinbergGroup (Fin r) (Localization.Away a)} {i j k l : Fin r} {Φ Ψ : Frame A r}
    (hΦ : IsFrame a Φ (colOf α i) (rowOf α j)) (hΨ : IsFrame a Ψ (colOf α k) (rowOf α l))
    (hli : l ≠ i) (hjk : j ≠ k) {C : Type} [CommRing C] (f : A →+* C) (s t : C) :
    Commute (Xf T a Φ f s) (Xf T a Ψ f t) :=
  T.commute_X _ _ _ _ _ _ (Frame.adm hΦ.2.2.1 hΦ.2.2.2 f) (Frame.param_mem hΦ.2.2.1 f s)
    (Frame.adm hΨ.2.2.1 hΨ.2.2.2 f) (Frame.param_mem hΨ.2.2.1 f t)
    (Xf_orth ha hΦ hΨ hli f) (Xf_orth ha hΨ hΦ hjk f)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Xf_commute

theorem Tfun_zero (hz : ZData a b) {i j : Fin r} (hij : i ≠ j) (ζ : PatchV r a b) :
    Tfun T hz hij 0 ζ = ζ := by
  refine Quotient.inductionOn ζ fun P => ?_
  obtain ⟨Φ, hΦ⟩ := exists_frame hz P.1 hij
  rw [Tfun_mk T hz hij P (Φ := Φ) (c' := 0) (s := 0)
    ⟨hΦ, by rw [map_zero, mul_zero, map_zero, add_zero]⟩]
  unfold opV
  rw [x_zero, one_mul, Xf_zero T hΦ.2.2.1 hΦ.2.2.2, one_mul]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Tfun_zero

/-- **Steinberg relation (1).** -/
theorem Tfun_add (hz : ZData a b) {i j : Fin r} (hij : i ≠ j) (c c₀ : Localization.Away (a * b))
    (ζ : PatchV r a b) : Tfun T hz hij c (Tfun T hz hij c₀ ζ) = Tfun T hz hij (c + c₀) ζ := by
  refine Quotient.inductionOn ζ fun P => ?_
  obtain ⟨Φ, hΦ⟩ := exists_frame hz P.1 hij
  obtain ⟨_, hq⟩ := zariski_split hz.hab c
  obtain ⟨c₁, s₁, -, hc₁, -⟩ := hq Φ.N
  obtain ⟨_, hq'⟩ := zariski_split hz.hab c₀
  obtain ⟨c₂, s₂, -, hc₂, -⟩ := hq' Φ.N
  have hΦ' : IsFrame a Φ (colOf (x i j hij c₂ * P.1) i) (rowOf (x i j hij c₂ * P.1) j) := by
    rw [colOf_x_mul_of_ne hij c₂ P.1 hij.symm, rowOf_x_mul_of_ne hij c₂ P.1 hij.symm]
    exact hΦ
  rw [Tfun_mk T hz hij P (Φ := Φ) (c' := c₂) (s := s₂) ⟨hΦ, hc₂⟩]
  show Tfun T hz hij c (Quotient.mk _ (x i j hij c₂ * P.1, Xf T a Φ (loc b) s₂ * P.2)) = _
  rw [Tfun_mk T hz hij (x i j hij c₂ * P.1, Xf T a Φ (loc b) s₂ * P.2) (Φ := Φ) (c' := c₁)
      (s := s₁) ⟨hΦ', hc₁⟩,
    Tfun_mk T hz hij P (Φ := Φ) (c' := c₁ + c₂) (s := s₁ + s₂)
      ⟨hΦ, by rw [hc₁, hc₂, map_add, mul_add, map_add]; ring⟩]
  unfold opV
  exact mk_pair_eq (by dsimp only; rw [← mul_assoc, x_mul])
    (by dsimp only; rw [← mul_assoc, Xf_add T hΦ.2.2.1 hΦ.2.2.2])

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Tfun_add

/-- **Steinberg relation (2).** -/
theorem Tfun_comm (hz : ZData a b) {i j k l : Fin r} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (c c₀ : Localization.Away (a * b)) (ζ : PatchV r a b) :
    Tfun T hz hij c (Tfun T hz hkl c₀ ζ) = Tfun T hz hkl c₀ (Tfun T hz hij c ζ) := by
  refine Quotient.inductionOn ζ fun P => ?_
  obtain ⟨Φ, hΦ⟩ := exists_frame hz P.1 hij
  obtain ⟨Ψ, hΨ⟩ := exists_frame hz P.1 hkl
  obtain ⟨_, hq⟩ := zariski_split hz.hab c
  obtain ⟨c₁, s₁, -, hc₁, -⟩ := hq Φ.N
  obtain ⟨_, hq'⟩ := zariski_split hz.hab c₀
  obtain ⟨c₂, s₂, -, hc₂, -⟩ := hq' Ψ.N
  have hΦ' : IsFrame a Φ (colOf (x k l hkl c₂ * P.1) i) (rowOf (x k l hkl c₂ * P.1) j) := by
    rw [colOf_x_mul_of_ne hkl c₂ P.1 hli, rowOf_x_mul_of_ne hkl c₂ P.1 hjk]
    exact hΦ
  have hΨ' : IsFrame a Ψ (colOf (x i j hij c₁ * P.1) k) (rowOf (x i j hij c₁ * P.1) l) := by
    rw [colOf_x_mul_of_ne hij c₁ P.1 hjk, rowOf_x_mul_of_ne hij c₁ P.1 hli]
    exact hΨ
  rw [Tfun_mk T hz hkl P ⟨hΨ, hc₂⟩, Tfun_mk T hz hij P ⟨hΦ, hc₁⟩]
  show Tfun T hz hij c (Quotient.mk _ (x k l hkl c₂ * P.1, Xf T a Ψ (loc b) s₂ * P.2)) =
    Tfun T hz hkl c₀ (Quotient.mk _ (x i j hij c₁ * P.1, Xf T a Φ (loc b) s₁ * P.2))
  rw [Tfun_mk T hz hij (x k l hkl c₂ * P.1, Xf T a Ψ (loc b) s₂ * P.2) ⟨hΦ', hc₁⟩,
    Tfun_mk T hz hkl (x i j hij c₁ * P.1, Xf T a Φ (loc b) s₁ * P.2) ⟨hΨ', hc₂⟩]
  unfold opV
  refine mk_pair_eq ?_ ?_
  · dsimp only
    rw [← mul_assoc, ← mul_assoc, (x_commute_of_ne i j k l hij hkl hjk hli c₁ c₂).eq]
  · dsimp only
    rw [← mul_assoc, ← mul_assoc, (Xf_commute T hz.ha hΦ hΨ hli hjk (loc b) s₁ s₂).eq]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Tfun_comm

end Relations

section MFrame

variable {r : ℕ} (T : TulX r) {A : Type} [CommRing A] {a : A}

/-- **A matrix frame** for `α`: integral `P ≈ a^{m₁} π(α)⁻¹` (columns `P l`) and
`Q ≈ a^{m₂} π(α)` (rows `Q l`). -/
structure MFrame (a : A) (α : SteinbergGroup (Fin r) (Localization.Away a)) where
  m1 : ℕ
  m2 : ℕ
  P : Fin r → Fin r → A
  Q : Fin r → Fin r → A
  hP : ∀ l, loc a ∘ P l = loc a a ^ m1 • colOf α l
  hQ : ∀ l, loc a ∘ Q l = loc a a ^ m2 • rowOf α l

theorem exists_mframe (α : SteinbergGroup (Fin r) (Localization.Away a)) :
    Nonempty (MFrame a α) := by
  obtain ⟨m1, v, hv⟩ := exists_clear a (fun p : Fin r × Fin r => colOf α p.1 p.2)
  obtain ⟨m2, w, hw⟩ := exists_clear a (fun p : Fin r × Fin r => rowOf α p.1 p.2)
  exact ⟨⟨m1, m2, fun l k => v (l, k), fun l k => w (l, k), fun l => funext fun k => hv (l, k),
    fun l => funext fun k => hw (l, k)⟩⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.exists_mframe

variable {α : SteinbergGroup (Fin r) (Localization.Away a)}

theorem MFrame.dot_self (ha : a ∈ nonZeroDivisors A) (M : MFrame a α) (l : Fin r) :
    M.Q l ⬝ᵥ M.P l = a ^ (M.m1 + M.m2) := by
  apply loc_injective ha
  rw [← comp_dotProduct, M.hQ, M.hP, smul_dotProduct, dotProduct_smul, rowOf_dot_colOf,
    Pi.single_eq_same, smul_eq_mul, smul_eq_mul, map_pow]
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.MFrame.dot_self

theorem MFrame.dot_ne (ha : a ∈ nonZeroDivisors A) (M : MFrame a α) {l l' : Fin r} (h : l ≠ l') :
    M.Q l ⬝ᵥ M.P l' = 0 := by
  apply loc_injective ha
  rw [← comp_dotProduct, M.hQ, M.hP, smul_dotProduct, dotProduct_smul, rowOf_dot_colOf,
    Pi.single_eq_of_ne h, smul_zero, smul_zero, map_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.MFrame.dot_ne

/-- The vector frame for `(column l, row l')` cut from a matrix frame. -/
def MFrame.vf (M : MFrame a α) (l l' : Fin r) : Frame A r where
  m1 := M.m1
  m2 := M.m2
  p := M.m1 + M.m2
  v := M.P l
  w := M.Q l'
  u := M.Q l

theorem MFrame.vf_isFrame (ha : a ∈ nonZeroDivisors A) (M : MFrame a α) {l l' : Fin r}
    (h : l ≠ l') : IsFrame a (M.vf l l') (colOf α l) (rowOf α l') :=
  ⟨M.hP l, M.hQ l', M.dot_self ha l, M.dot_ne ha h.symm⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.MFrame.vf_isFrame

theorem MFrame.dotC_self (ha : a ∈ nonZeroDivisors A) (M : MFrame a α) {C : Type} [CommRing C]
    (f : A →+* C) (l : Fin r) : (f ∘ M.Q l) ⬝ᵥ (f ∘ M.P l) = f a ^ (M.m1 + M.m2) := by
  rw [comp_dotProduct, M.dot_self ha l, map_pow]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.MFrame.dotC_self

theorem MFrame.dotC_ne (ha : a ∈ nonZeroDivisors A) (M : MFrame a α) {C : Type} [CommRing C]
    (f : A →+* C) {l l' : Fin r} (h : l ≠ l') : (f ∘ M.Q l) ⬝ᵥ (f ∘ M.P l') = 0 := by
  rw [comp_dotProduct, M.dot_ne ha h, map_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.MFrame.dotC_ne

theorem vecMul_one_add_smul_vecMulVec' {B : Type*} [CommRing B] (s : B) (w v' w' : Fin r → B) :
    w ᵥ* (1 + s • vecMulVec v' w') = w + (s * (w ⬝ᵥ v')) • w' := by
  rw [vecMul_add, vecMul_one, vecMul_smul, vecMul_vecMulVec, smul_smul]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.vecMul_one_add_smul_vecMulVec'

/-- **The commutator of the `(j,k)` and `(i,j)` elements** (Tulenbaev's relation (3), `A_b`
side). -/
theorem MFrame.conj_jk_ij (ha : a ∈ nonZeroDivisors A) (M : MFrame a α) {i j k : Fin r}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {C : Type} [CommRing C] (f : A →+* C) (τ σ : C) :
    Xf T a (M.vf j k) f τ * Xf T a (M.vf i j) f σ * (Xf T a (M.vf j k) f τ)⁻¹ =
      Xf T a (M.vf i j) f σ * Xf T a (M.vf i k) f
        (-(f a ^ (M.m1 + M.m2) * τ) * (f a ^ (M.m1 + M.m2) * f a ^ (M.m1 + M.m2)) * σ) := by
  have hij' := M.vf_isFrame ha hij
  have hjk' := M.vf_isFrame ha hjk
  have hik' := M.vf_isFrame ha hik
  have hc := T.conj _ _ _ (Frame.adm hij'.2.2.1 hij'.2.2.2 f) (Frame.param_mem hij'.2.2.1 f σ)
    (Xf T a (M.vf j k) f τ)
  unfold Xf at hc
  rw [T.proj _ _ _ (Frame.adm hjk'.2.2.1 hjk'.2.2.2 f) (Frame.param_mem hjk'.2.2.1 f τ),
    T.pMat_X_inv _ _ _ (Frame.adm hjk'.2.2.1 hjk'.2.2.2 f) (Frame.param_mem hjk'.2.2.1 f τ),
    TulX.mulVec_one_add_smul_vecMulVec _ _ _ _ (Xf_orth ha hij' hjk' hik.symm f),
    vecMul_one_add_smul_vecMulVec'] at hc
  unfold Xf
  simp only [MFrame.vf] at hc ⊢
  have hW : (f ∘ (a ^ (M.m1 + M.m2) • M.Q j)) ⬝ᵥ (f ∘ M.P j) =
      f a ^ (M.m1 + M.m2) * f a ^ (M.m1 + M.m2) := by
    rw [comp_smul', smul_dotProduct, M.dotC_self ha f j, map_pow, smul_eq_mul]
  have hadm_j : AdmRow (f ∘ M.P i) (f ∘ (a ^ (M.m1 + M.m2) • M.Q j)) :=
    Frame.adm hij'.2.2.1 hij'.2.2.2 f
  have hadm_k : AdmRow (f ∘ M.P i) (f ∘ (a ^ (M.m1 + M.m2) • M.Q k)) :=
    Frame.adm hik'.2.2.1 hik'.2.2.2 f
  have hpar : f a ^ (M.m1 + M.m2) * σ ∈ coordIdeal (f ∘ M.P i) :=
    Frame.param_mem hij'.2.2.1 f σ
  rw [hc, hW, ← T.rowAdd _ _ _ _ hadm_j (Submodule.smul_mem _ _ hadm_k) hpar,
    T.smulRow _ _ _ _ hadm_k hpar]
  congr 2
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.MFrame.conj_jk_ij

/-- **The row change** under `x_jk(c')`: the frame with row `aᵠ Q_j + ν Q_k` splits. -/
theorem MFrame.row_split (ha : a ∈ nonZeroDivisors A) (M : MFrame a α) {i j k : Fin r}
    (hij : i ≠ j) (hik : i ≠ k) (q : ℕ) (ν : A) {C : Type} [CommRing C] (f : A →+* C) (s : C) :
    Xf T a ⟨M.m1, M.m2 + q, M.m1 + M.m2, M.P i, a ^ q • M.Q j + ν • M.Q k, M.Q i⟩ f s =
      Xf T a (M.vf i j) f (f a ^ q * s) * Xf T a (M.vf i k) f (f ν * s) := by
  have hij' := M.vf_isFrame ha hij
  have hik' := M.vf_isFrame ha hik
  have hadm_j : AdmRow (f ∘ M.P i) (f ∘ (a ^ (M.m1 + M.m2) • M.Q j)) :=
    Frame.adm hij'.2.2.1 hij'.2.2.2 f
  have hadm_k : AdmRow (f ∘ M.P i) (f ∘ (a ^ (M.m1 + M.m2) • M.Q k)) :=
    Frame.adm hik'.2.2.1 hik'.2.2.2 f
  have hpar : f a ^ (M.m1 + M.m2) * s ∈ coordIdeal (f ∘ M.P i) :=
    Frame.param_mem hij'.2.2.1 f s
  have hrow : f ∘ (a ^ (M.m1 + M.m2) • (a ^ q • M.Q j + ν • M.Q k)) =
      f a ^ q • (f ∘ (a ^ (M.m1 + M.m2) • M.Q j)) + f ν • (f ∘ (a ^ (M.m1 + M.m2) • M.Q k)) := by
    funext m
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
      map_pow]
    ring
  show T.X (f ∘ M.P i) (f ∘ (a ^ (M.m1 + M.m2) • (a ^ q • M.Q j + ν • M.Q k)))
      (f a ^ (M.m1 + M.m2) * s) =
    T.X (f ∘ M.P i) (f ∘ (a ^ (M.m1 + M.m2) • M.Q j)) (f a ^ (M.m1 + M.m2) * (f a ^ q * s)) *
      T.X (f ∘ M.P i) (f ∘ (a ^ (M.m1 + M.m2) • M.Q k)) (f a ^ (M.m1 + M.m2) * (f ν * s))
  rw [hrow, ← T.rowAdd _ _ _ _ (Submodule.smul_mem _ _ hadm_j) (Submodule.smul_mem _ _ hadm_k) hpar,
    T.smulRow _ _ _ _ hadm_j hpar, T.smulRow _ _ _ _ hadm_k hpar,
    mul_left_comm (f a ^ q), mul_left_comm (f ν)]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.MFrame.row_split

/-- **The column change** under `x_ij(c')`: the frame with column `aᵠ P_j - κ P_i` splits
(Tulenbaev's Lemma 1.3(c), via `TulX.colAdd` and Lemma 1.2). -/
theorem MFrame.col_split (ha : a ∈ nonZeroDivisors A) (hr : 5 ≤ r) (M : MFrame a α)
    {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (q : ℕ) (hq : M.m1 + M.m2 ≤ q)
    (κ : A) {C : Type} [CommRing C] (f : A →+* C) (s : C) :
    Xf T a ⟨M.m1 + q, M.m2, q + (M.m1 + M.m2), a ^ q • M.P j + (-κ) • M.P i, M.Q k, M.Q j⟩ f s =
      Xf T a (M.vf j k) f (f a ^ (3 * q) * s) *
        Xf T a (M.vf i k) f (-(f κ) * f a ^ (2 * q) * s) := by
  have hWkVj : (f ∘ M.Q k) ⬝ᵥ (f ∘ M.P j) = 0 := M.dotC_ne ha f hjk.symm
  have hWkVi : (f ∘ M.Q k) ⬝ᵥ (f ∘ M.P i) = 0 := M.dotC_ne ha f hik.symm
  have hμj : f a ^ (M.m1 + M.m2) ∈ coordIdeal (f ∘ M.P j) := by
    rw [← M.dotC_self ha f j]; exact dotProduct_mem_coordIdeal _ _
  have hμi : f a ^ (M.m1 + M.m2) ∈ coordIdeal (f ∘ M.P i) := by
    rw [← M.dotC_self ha f i]; exact dotProduct_mem_coordIdeal _ _
  have hqμ : f a ^ (q + (M.m1 + M.m2)) = f a ^ q * f a ^ (M.m1 + M.m2) := pow_add _ _ _
  -- the three ideal memberships of `colAdd`
  have ht1 : f a ^ (q + (M.m1 + M.m2)) * s ∈ coordIdeal (f a ^ q • (f ∘ M.P j)) := by
    have h := dotProduct_mem_coordIdeal (f ∘ M.Q j) (f a ^ q • (f ∘ M.P j))
    rw [dotProduct_smul, M.dotC_self ha f j, smul_eq_mul, ← hqμ] at h
    exact Ideal.mul_mem_right _ _ h
  have ht2 : -(f κ) * (f a ^ (q + (M.m1 + M.m2)) * s) ∈ coordIdeal (f ∘ M.P i) := by
    rw [hqμ]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hμi))
  have ht3 : f a ^ (q + (M.m1 + M.m2)) * s ∈
      coordIdeal (f a ^ q • (f ∘ M.P j) + (-(f κ)) • (f ∘ M.P i)) := by
    have h := dotProduct_mem_coordIdeal (f ∘ M.Q j) (f a ^ q • (f ∘ M.P j) + (-(f κ)) • (f ∘ M.P i))
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, M.dotC_self ha f j,
      M.dotC_ne ha f hij.symm, smul_eq_mul, smul_zero, add_zero, ← hqμ] at h
    exact Ideal.mul_mem_right _ _ h
  -- Lemma 1.2: the row lies in the span of the two-zero rows orthogonal to both columns
  have hspan : f a ^ (q + (M.m1 + M.m2)) • (f ∘ M.Q k) ∈
      Submodule.span C (K2Found.TwoZero.twoZeroSet (f a ^ q • (f ∘ M.P j)) (f ∘ M.P i)) := by
    have hdet := K2Found.TwoZero.det_smul_mem_span_twoZero (by rw [Fintype.card_fin]; exact hr)
      (f ∘ M.P j) (f ∘ M.P i) (f ∘ M.Q k) (f ∘ M.Q j) (f ∘ M.Q i) hWkVj hWkVi
    rw [M.dotC_self ha f j, M.dotC_self ha f i, M.dotC_ne ha f hij, M.dotC_ne ha f hij.symm,
      mul_zero, sub_zero] at hdet
    have hmono : K2Found.TwoZero.twoZeroSet (f ∘ M.P j) (f ∘ M.P i) ⊆
        K2Found.TwoZero.twoZeroSet (f a ^ q • (f ∘ M.P j)) (f ∘ M.P i) := by
      rintro u ⟨h1, h2, h3⟩
      exact ⟨by rw [dotProduct_smul, h1, smul_zero], h2, h3⟩
    have h := Submodule.smul_mem _ (f a ^ (q - (M.m1 + M.m2))) (Submodule.span_mono hmono hdet)
    rwa [smul_smul, ← pow_add, ← pow_add, show q - (M.m1 + M.m2) + (M.m1 + M.m2 + (M.m1 + M.m2)) =
      q + (M.m1 + M.m2) by omega] at h
  have hadm1 : AdmRow (f ∘ M.P j) (f a ^ (q + (M.m1 + M.m2)) • (f ∘ M.Q k)) := by
    refine admRow_smul ?_ hWkVj
    rw [hqμ]
    exact Ideal.mul_mem_left _ _ hμj
  have hadm_j : AdmRow (f ∘ M.P j) (f a ^ (M.m1 + M.m2) • (f ∘ M.Q k)) := admRow_smul hμj hWkVj
  have hadm_i : AdmRow (f ∘ M.P i) (f a ^ (M.m1 + M.m2) • (f ∘ M.Q k)) := admRow_smul hμi hWkVi
  have hpj : f a ^ q * (f a ^ (q + (M.m1 + M.m2)) * s) ∈ coordIdeal (f ∘ M.P j) := by
    rw [hqμ]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hμj))
  have hsm : f a ^ (q + (M.m1 + M.m2)) • (f ∘ M.Q k) =
      f a ^ q • (f a ^ (M.m1 + M.m2) • (f ∘ M.Q k)) := by
    rw [smul_smul, ← pow_add]
  show T.X (f ∘ (a ^ q • M.P j + (-κ) • M.P i)) (f ∘ (a ^ (q + (M.m1 + M.m2)) • M.Q k))
      (f a ^ (q + (M.m1 + M.m2)) * s) =
    T.X (f ∘ M.P j) (f ∘ (a ^ (M.m1 + M.m2) • M.Q k)) (f a ^ (M.m1 + M.m2) * (f a ^ (3 * q) * s)) *
      T.X (f ∘ M.P i) (f ∘ (a ^ (M.m1 + M.m2) • M.Q k))
        (f a ^ (M.m1 + M.m2) * (-(f κ) * f a ^ (2 * q) * s))
  have hcol : f ∘ (a ^ q • M.P j + (-κ) • M.P i) = f a ^ q • (f ∘ M.P j) + (-(f κ)) • (f ∘ M.P i) := by
    simp only [comp_add', comp_smul', map_pow, map_neg]
  rw [hcol, comp_smul', map_pow, comp_smul', map_pow,
    T.colAdd _ _ _ _ _ hspan ht1 ht2 ht3, T.smulCol _ _ _ _ hadm1 ht1, hsm,
    T.smulRow _ _ _ _ hadm_j hpj, T.smulRow _ _ _ _ hadm_i ht2]
  congr 2 <;> ring

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.MFrame.col_split

end MFrame

section Adjacent

variable {r : ℕ} (T : TulX r) {A : Type} [CommRing A] {a b : A}

/-- **Steinberg relation (3)**, in the form `T_ij(c) T_jk(c') = T_ik(cc') T_jk(c') T_ij(c)`. -/
theorem Tfun_adj (hz : ZData a b) (hr : 5 ≤ r) {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (c c₀ : Localization.Away (a * b)) (ζ : PatchV r a b) :
    Tfun T hz hij c (Tfun T hz hjk c₀ ζ) =
      Tfun T hz hik (c * c₀) (Tfun T hz hjk c₀ (Tfun T hz hij c ζ)) := by
  refine Quotient.inductionOn ζ fun P => ?_
  obtain ⟨M⟩ := exists_mframe (a := a) P.1
  obtain ⟨q₁, hq₁⟩ := zariski_split hz.hab c
  obtain ⟨q₂, hq₂⟩ := zariski_split hz.hab c₀
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = q₁ + q₂ + (M.m1 + M.m2) := ⟨_, rfl⟩
  have hqμ : M.m1 + M.m2 ≤ q := by omega
  obtain ⟨c', s₀, κ₀, hc, hκ₀⟩ := hq₁ (3 * (M.m1 + M.m2) + 3 * q)
  obtain ⟨c'', t₀, ν₀, hc₀, hν₀⟩ := hq₂ (3 * (M.m1 + M.m2) + 3 * q)
  obtain ⟨κ, hκdef⟩ : ∃ κ : A, κ = κ₀ * a ^ (q₂ + (M.m1 + M.m2)) := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν : A, ν = ν₀ * a ^ (q₁ + (M.m1 + M.m2)) := ⟨_, rfl⟩
  have hκ : c' * loc a a ^ q = loc a κ := by
    rw [hκdef, map_mul, map_pow, ← hκ₀, hq]; ring
  have hν : c'' * loc a a ^ q = loc a ν := by
    rw [hνdef, map_mul, map_pow, ← hν₀, hq]; ring
  have ha := hz.ha
  -- the frames
  have hΦij := M.vf_isFrame ha hij
  have hΦjk := M.vf_isFrame ha hjk
  have hΦik := M.vf_isFrame ha hik
  obtain ⟨Φ', hΦ'def⟩ : ∃ Φ' : Frame A r,
      Φ' = ⟨M.m1, M.m2 + q, M.m1 + M.m2, M.P i, a ^ q • M.Q j + ν • M.Q k, M.Q i⟩ := ⟨_, rfl⟩
  obtain ⟨Ψ', hΨ'def⟩ : ∃ Ψ' : Frame A r,
      Ψ' = ⟨M.m1 + q, M.m2, q + (M.m1 + M.m2), a ^ q • M.P j + (-κ) • M.P i, M.Q k, M.Q j⟩ :=
    ⟨_, rfl⟩
  have hNvf : ∀ l l' : Fin r, (M.vf l l').N = M.m1 + M.m2 + 2 * (M.m1 + M.m2) := fun _ _ => rfl
  have hNΦ' : Φ'.N = M.m1 + (M.m2 + q) + 2 * (M.m1 + M.m2) := by rw [hΦ'def]; rfl
  have hNΨ' : Ψ'.N = 3 * (M.m1 + M.m2) + 3 * q := by
    rw [hΨ'def]; show M.m1 + q + M.m2 + 2 * (q + (M.m1 + M.m2)) = _; omega
  -- the points
  have hΦ'fr : IsFrame a Φ' (colOf (x j k hjk c'' * P.1) i) (rowOf (x j k hjk c'' * P.1) j) := by
    rw [colOf_x_mul_of_ne hjk c'' P.1 hik.symm, rowOf_x_mul j k hjk c'' P.1 j, Pi.single_eq_same,
      mul_one, hΦ'def]
    refine ⟨M.hP i, ?_, M.dot_self ha i, ?_⟩
    · funext m
      have e1 := congrFun (M.hQ j) m
      have e2 := congrFun (M.hQ k) m
      simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
        map_pow] at e1 e2 ⊢
      rw [e1, e2, ← hν]
      ring
    · show (a ^ q • M.Q j + ν • M.Q k) ⬝ᵥ M.P i = 0
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, M.dot_ne ha hij.symm,
        M.dot_ne ha hik.symm, smul_zero, smul_zero, add_zero]
  have hΨ'fr : IsFrame a Ψ' (colOf (x i j hij c' * P.1) j) (rowOf (x i j hij c' * P.1) k) := by
    rw [colOf_x_mul i j hij c' P.1 j, Pi.single_eq_same, mul_one,
      rowOf_x_mul_of_ne hij c' P.1 hik.symm, hΨ'def]
    refine ⟨?_, M.hQ k, ?_, ?_⟩
    · funext m
      have e1 := congrFun (M.hP j) m
      have e2 := congrFun (M.hP i) m
      simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
        map_pow, map_neg] at e1 e2 ⊢
      rw [e1, e2, ← hκ]
      ring
    · show M.Q j ⬝ᵥ (a ^ q • M.P j + (-κ) • M.P i) = a ^ (q + (M.m1 + M.m2))
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, M.dot_self ha j, M.dot_ne ha hij.symm,
        smul_eq_mul, smul_zero, add_zero]
      ring
    · show M.Q k ⬝ᵥ (a ^ q • M.P j + (-κ) • M.P i) = 0
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, M.dot_ne ha hjk.symm,
        M.dot_ne ha hik.symm, smul_zero, smul_zero, add_zero]
  have hΦik₃ : IsFrame a (M.vf i k) (colOf (x j k hjk c'' * (x i j hij c' * P.1)) i)
      (rowOf (x j k hjk c'' * (x i j hij c' * P.1)) k) := by
    rw [colOf_x_mul_of_ne hjk c'' _ hik.symm, colOf_x_mul_of_ne hij c' P.1 hij.symm,
      rowOf_x_mul_of_ne hjk c'' _ hjk.symm, rowOf_x_mul_of_ne hij c' P.1 hik.symm]
    exact hΦik
  -- the splitting of `c c₀`
  obtain ⟨σ, hσ⟩ : ∃ σ : Localization.Away b, σ =
      loc b ν * (loc b a ^ (2 * q) * s₀) + loc b κ * (loc b a ^ (2 * q) * t₀) +
        loc b a ^ (M.m1 + M.m2 + 2 * (M.m1 + M.m2)) *
          ((loc b a ^ (3 * q) * t₀) * (loc b a ^ (3 * q) * s₀)) := ⟨_, rfl⟩
  have hprod : c * c₀ = ja a b (c' * c'') +
      jb a b (loc b a ^ (M.vf i k).N * σ) := by
    have m1 := ja_mul_jb hκ (loc b a ^ (3 * (M.m1 + M.m2) + 2 * q) * t₀)
    have m2 := ja_mul_jb hν (loc b a ^ (3 * (M.m1 + M.m2) + 2 * q) * s₀)
    rw [hc, hc₀, hNvf, hσ, split_rescale (loc b a) s₀ (N := 3 * (M.m1 + M.m2) + 3 * q) (N' := q)
      (n := 3 * (M.m1 + M.m2) + 2 * q) (by omega), split_rescale (loc b a) t₀
      (N := 3 * (M.m1 + M.m2) + 3 * q) (N' := q) (n := 3 * (M.m1 + M.m2) + 2 * q) (by omega)]
    simp only [map_mul, map_add, map_pow] at m1 m2 ⊢
    linear_combination m1 + m2
  -- evaluate both sides
  have hV1 : Valid a b P.1 j k c₀ (M.vf j k) c'' (loc b a ^ (3 * q) * t₀) :=
    ⟨hΦjk, by
      rw [hc₀, hNvf, split_rescale (loc b a) t₀ (N := 3 * (M.m1 + M.m2) + 3 * q)
        (N' := M.m1 + M.m2 + 2 * (M.m1 + M.m2)) (n := 3 * q) (by omega)]⟩
  have hV2 : Valid a b (x j k hjk c'' * P.1) i j c Φ' c' (loc b a ^ (2 * q) * s₀) :=
    ⟨hΦ'fr, by
      rw [hc, hNΦ', split_rescale (loc b a) s₀ (N := 3 * (M.m1 + M.m2) + 3 * q)
        (N' := M.m1 + (M.m2 + q) + 2 * (M.m1 + M.m2)) (n := 2 * q) (by omega)]⟩
  have hV3 : Valid a b P.1 i j c (M.vf i j) c' (loc b a ^ (3 * q) * s₀) :=
    ⟨hΦij, by
      rw [hc, hNvf, split_rescale (loc b a) s₀ (N := 3 * (M.m1 + M.m2) + 3 * q)
        (N' := M.m1 + M.m2 + 2 * (M.m1 + M.m2)) (n := 3 * q) (by omega)]⟩
  have hV4 : Valid a b (x i j hij c' * P.1) j k c₀ Ψ' c'' t₀ :=
    ⟨hΨ'fr, by rw [hNΨ']; exact hc₀⟩
  have hV5 : Valid a b (x j k hjk c'' * (x i j hij c' * P.1)) i k (c * c₀) (M.vf i k)
      (c' * c'') σ := ⟨hΦik₃, hprod⟩
  rw [Tfun_mk T hz hjk P hV1, Tfun_mk T hz hij P hV3]
  show Tfun T hz hij c (Quotient.mk _ (x j k hjk c'' * P.1,
      Xf T a (M.vf j k) (loc b) (loc b a ^ (3 * q) * t₀) * P.2)) =
    Tfun T hz hik (c * c₀) (Tfun T hz hjk c₀ (Quotient.mk _ (x i j hij c' * P.1,
      Xf T a (M.vf i j) (loc b) (loc b a ^ (3 * q) * s₀) * P.2)))
  rw [Tfun_mk T hz hij (x j k hjk c'' * P.1,
      Xf T a (M.vf j k) (loc b) (loc b a ^ (3 * q) * t₀) * P.2) hV2,
    Tfun_mk T hz hjk (x i j hij c' * P.1,
      Xf T a (M.vf i j) (loc b) (loc b a ^ (3 * q) * s₀) * P.2) hV4]
  show _ = Tfun T hz hik (c * c₀) (Quotient.mk _ (x j k hjk c'' * (x i j hij c' * P.1),
    Xf T a Ψ' (loc b) t₀ * (Xf T a (M.vf i j) (loc b) (loc b a ^ (3 * q) * s₀) * P.2)))
  rw [Tfun_mk T hz hik (x j k hjk c'' * (x i j hij c' * P.1),
    Xf T a Ψ' (loc b) t₀ * (Xf T a (M.vf i j) (loc b) (loc b a ^ (3 * q) * s₀) * P.2)) hV5]
  unfold opV
  refine mk_pair_eq ?_ ?_
  · -- the `A_a` side: the Steinberg relation in `St(A_a)`
    dsimp only
    have hst := x_commutator i j k hij hjk hik c' c''
    rw [← hst, commutatorElement_def]
    group
  · -- the `A_b` side
    dsimp only
    rw [hΦ'def, MFrame.row_split T ha M hij hik q ν (loc b), hΨ'def,
      MFrame.col_split T ha hr M hij hjk hik q hqμ κ (loc b),
      show loc b a ^ q * (loc b a ^ (2 * q) * s₀) = loc b a ^ (3 * q) * s₀ by ring]
    -- the three root elements, as opaque functions, and the parameters
    obtain ⟨E1, hE1⟩ : ∃ E1 : Localization.Away b → SteinbergGroup (Fin r) (Localization.Away b),
      E1 = Xf T a (M.vf i j) (loc b) := ⟨_, rfl⟩
    obtain ⟨E2, hE2⟩ : ∃ E2 : Localization.Away b → SteinbergGroup (Fin r) (Localization.Away b),
      E2 = Xf T a (M.vf i k) (loc b) := ⟨_, rfl⟩
    obtain ⟨E3, hE3⟩ : ∃ E3 : Localization.Away b → SteinbergGroup (Fin r) (Localization.Away b),
      E3 = Xf T a (M.vf j k) (loc b) := ⟨_, rfl⟩
    rw [← hE1, ← hE2, ← hE3]
    obtain ⟨S, hS⟩ : ∃ S : Localization.Away b, S = loc b a ^ (3 * q) * s₀ := ⟨_, rfl⟩
    obtain ⟨S', hS'⟩ : ∃ S' : Localization.Away b, S' = loc b a ^ (3 * q) * t₀ := ⟨_, rfl⟩
    obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ : Localization.Away b, ρ = loc b ν * (loc b a ^ (2 * q) * s₀) :=
      ⟨_, rfl⟩
    obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ : Localization.Away b, ρ = -(loc b κ) * loc b a ^ (2 * q) * t₀ :=
      ⟨_, rfl⟩
    rw [← hS, ← hS', ← hρ₁, ← hρ₂]
    have C1 : ∀ t t', E2 t * E3 t' = E3 t' * E2 t := fun t t' => by
      rw [hE2, hE3]
      exact (Xf_commute T ha hΦik hΦjk hik.symm hjk.symm (loc b) t t').eq
    have C2 : ∀ t t', E2 t * E1 t' = E1 t' * E2 t := fun t t' => by
      rw [hE2, hE1]
      exact (Xf_commute T ha hΦik hΦij hij.symm hik.symm (loc b) t t').eq
    have Ad : ∀ t t', E2 t * E2 t' = E2 (t + t') := fun t t' => by
      rw [hE2]
      exact Xf_add T hΦik.2.2.1 hΦik.2.2.2 (loc b) t t'
    have C3 : ∀ τ σ', E3 τ * E1 σ' = E1 σ' * E2 (-(loc b a ^ (M.m1 + M.m2) * τ) *
        (loc b a ^ (M.m1 + M.m2) * loc b a ^ (M.m1 + M.m2)) * σ') * E3 τ := fun τ σ' => by
      rw [hE1, hE2, hE3, ← MFrame.conj_jk_ij T ha M hij hjk hik (loc b) τ σ']
      group
    obtain ⟨ρ₃, hρ₃⟩ : ∃ ρ : Localization.Away b, ρ = -(loc b a ^ (M.m1 + M.m2) * S') *
        (loc b a ^ (M.m1 + M.m2) * loc b a ^ (M.m1 + M.m2)) * S := ⟨_, rfl⟩
    have C3' : E3 S' * E1 S = E1 S * E2 ρ₃ * E3 S' := by rw [hρ₃]; exact C3 S' S
    have hρ : σ + ρ₂ + ρ₃ = ρ₁ := by
      rw [hσ, hρ₁, hρ₂, hρ₃, hS, hS']
      ring
    have hword : E1 S * E2 ρ₁ * E3 S' = E2 σ * (E3 S' * E2 ρ₂) * E1 S := by
      symm
      calc E2 σ * (E3 S' * E2 ρ₂) * E1 S = E2 σ * (E2 ρ₂ * E3 S') * E1 S := by rw [C1]
        _ = E2 σ * E2 ρ₂ * (E3 S' * E1 S) := by group
        _ = E2 (σ + ρ₂) * (E1 S * E2 ρ₃ * E3 S') := by rw [Ad, C3']
        _ = E2 (σ + ρ₂) * E1 S * E2 ρ₃ * E3 S' := by group
        _ = E1 S * E2 (σ + ρ₂) * E2 ρ₃ * E3 S' := by rw [C2]
        _ = E1 S * (E2 (σ + ρ₂) * E2 ρ₃) * E3 S' := by group
        _ = E1 S * E2 ρ₁ * E3 S' := by rw [Ad, hρ]
    calc E1 S * E2 ρ₁ * (E3 S' * P.2) = E1 S * E2 ρ₁ * E3 S' * P.2 := by group
      _ = E2 σ * (E3 S' * E2 ρ₂) * E1 S * P.2 := by rw [hword]
      _ = E2 σ * (E3 S' * E2 ρ₂ * (E1 S * P.2)) := by group

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Tfun_adj

end Adjacent

section Action

variable {r : ℕ} (T : TulX r) {A : Type} [CommRing A] {a b : A}

/-- `T_ij(c)` as a permutation of `V`. -/
noncomputable def Tperm (hz : ZData a b) {i j : Fin r} (hij : i ≠ j)
    (c : Localization.Away (a * b)) : Equiv.Perm (PatchV r a b) where
  toFun := Tfun T hz hij c
  invFun := Tfun T hz hij (-c)
  left_inv ζ := by rw [Tfun_add, neg_add_cancel, Tfun_zero]
  right_inv ζ := by rw [Tfun_add, add_neg_cancel, Tfun_zero]

theorem Tperm_apply (hz : ZData a b) {i j : Fin r} (hij : i ≠ j) (c : Localization.Away (a * b))
    (ζ : PatchV r a b) : Tperm T hz hij c ζ = Tfun T hz hij c ζ :=
  rfl

theorem Tperm_kills (hz : ZData a b) (hr : 5 ≤ r)
    (w : FreeGroup (SteinbergGenerator (Fin r) (Localization.Away (a * b))))
    (hw : w ∈ SteinbergGroup.relations (I := Fin r) (R := Localization.Away (a * b))) :
    FreeGroup.lift (fun g => Tperm T hz g.row_ne_column g.coefficient) w = 1 := by
  change SteinbergGroup.IsRelation w at hw
  cases hw with
  | add i j hij a' b' =>
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    change Tperm T hz hij a' * Tperm T hz hij b' * (Tperm T hz hij (a' + b'))⁻¹ = 1
    rw [mul_inv_eq_one]
    ext ζ
    exact Tfun_add T hz hij a' b' ζ
  | commute i j k l hij hkl hjk hli a' b' =>
    simp only [map_commutatorElement, FreeGroup.lift_apply_of]
    change ⁅Tperm T hz hij a', Tperm T hz hkl b'⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    ext ζ
    exact Tfun_comm T hz hij hkl hjk hli a' b' ζ
  | adjacent i j k hij hjk hik a' b' =>
    simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
    change ⁅Tperm T hz hij a', Tperm T hz hjk b'⁆ * (Tperm T hz hik (a' * b'))⁻¹ = 1
    have hperm : Tperm T hz hij a' * Tperm T hz hjk b' =
        Tperm T hz hik (a' * b') * Tperm T hz hjk b' * Tperm T hz hij a' := by
      ext ζ
      exact Tfun_adj T hz hr hij hjk hik a' b' ζ
    rw [mul_inv_eq_one, commutatorElement_def, hperm]
    group

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Tperm_kills

/-- **The action of `St_r(A_{ab})` on the orbit set** (Tulenbaev: `x_ij(c) · z = T_ij(c) z`). -/
noncomputable def act (hz : ZData a b) (hr : 5 ≤ r) :
    SteinbergGroup (Fin r) (Localization.Away (a * b)) →* Equiv.Perm (PatchV r a b) :=
  PresentedGroup.toGroup (Tperm_kills T hz hr)

theorem act_x (hz : ZData a b) (hr : 5 ≤ r) {i j : Fin r} (hij : i ≠ j)
    (c : Localization.Away (a * b)) : act T hz hr (x i j hij c) = Tperm T hz hij c :=
  PresentedGroup.toGroup.of _

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.act_x

/-- The elements `h ∈ St(A_b)` with `jb(h) · [1, β] = [1, h β]` for all `β`. -/
def jbSub (hz : ZData a b) (hr : 5 ≤ r) :
    Subgroup (SteinbergGroup (Fin r) (Localization.Away b)) where
  carrier := {h | ∀ β, act T hz hr (ringMap (jb a b) h) (Quotient.mk _ (1, β)) =
    Quotient.mk _ (1, h * β)}
  one_mem' := by
    show ∀ β, _
    intro β
    rw [map_one, map_one, Equiv.Perm.one_apply, one_mul]
  mul_mem' := by
    intro h₁ h₂ h₁S h₂S
    show ∀ β, _
    intro β
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, h₂S β, h₁S (h₂ * β), mul_assoc]
  inv_mem' := by
    intro h hS
    show ∀ β, _
    intro β
    apply (act T hz hr (ringMap (jb a b) h)).injective
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one,
      Equiv.Perm.one_apply, hS (h⁻¹ * β), mul_inv_cancel_left]

/-- **`A_b`-elements act on the second factor at `α = 1`.** -/
theorem act_jb (hz : ZData a b) (hr : 5 ≤ r) (h : SteinbergGroup (Fin r) (Localization.Away b))
    (β : SteinbergGroup (Fin r) (Localization.Away b)) :
    act T hz hr (ringMap (jb a b) h) (Quotient.mk _ (1, β)) = Quotient.mk _ (1, h * β) := by
  have hgen : ∀ g : SteinbergGenerator (Fin r) (Localization.Away b),
      PresentedGroup.of g ∈ jbSub T hz hr := by
    rintro ⟨k, l, hkl, e⟩
    show ∀ β, act T hz hr (ringMap (jb a b) (x k l hkl e)) (Quotient.mk _ (1, β)) =
      Quotient.mk _ (1, x k l hkl e * β)
    intro β
    rw [ringMap_x, act_x, Tperm_apply]
    have hΦ₀ : IsFrame a (⟨0, 0, 0, Pi.single k 1, Pi.single l 1, Pi.single k 1⟩ : Frame A r)
        (colOf 1 k) (rowOf 1 l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · show loc a ∘ Pi.single k 1 = loc a a ^ 0 • (pMat (1 : SteinbergGroup (Fin r)
          (Localization.Away a))⁻¹ *ᵥ Pi.single k 1)
        rw [comp_single_one, pow_zero, one_smul, inv_one, pMat_one, one_mulVec]
      · show loc a ∘ Pi.single l 1 = loc a a ^ 0 • (Pi.single l 1 ᵥ* pMat (1 : SteinbergGroup
          (Fin r) (Localization.Away a)))
        rw [comp_single_one, pow_zero, one_smul, pMat_one, vecMul_one]
      · show Pi.single k (1 : A) ⬝ᵥ Pi.single k 1 = a ^ 0
        rw [single_one_dotProduct, Pi.single_eq_same, pow_zero]
      · show Pi.single l (1 : A) ⬝ᵥ Pi.single k 1 = 0
        rw [single_one_dotProduct, Pi.single_eq_of_ne hkl.symm]
    rw [Tfun_mk T hz hkl (1, β) (Φ := ⟨0, 0, 0, Pi.single k 1, Pi.single l 1, Pi.single k 1⟩)
      (c' := 0) (s := e) ⟨hΦ₀, by
        show jb a b e = ja a b 0 + jb a b (loc b a ^ (0 + 0 + 2 * 0) * e)
        rw [map_zero, zero_add, show 0 + 0 + 2 * 0 = 0 from rfl, pow_zero, one_mul]⟩]
    unfold opV
    refine mk_pair_eq ?_ ?_
    · show x k l hkl (0 : Localization.Away a) * 1 = 1
      rw [x_zero, one_mul]
    · show T.X (loc b ∘ Pi.single k 1) (loc b ∘ (a ^ 0 • Pi.single l 1)) (loc b a ^ 0 * e) * β =
        x k l hkl e * β
      simp only [pow_zero, one_smul, one_mul, comp_single_one]
      rw [T.single]
  exact PresentedGroup.generated_by _ (jbSub T hz hr) hgen h β

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.act_jb

end Action

/-- **F.4: Zariski excision for `St_r`, `r ≥ 5`** (Tulenbaev, Prop 1.4(b), the case `(1, β)`), from
Tulenbaev's elements `X_{v,w}(t)`. -/
theorem stZariskiExcisionAt_of_tulX {r : ℕ} (T : TulX r) (hr : 5 ≤ r) (A : Type) [CommRing A] :
    StZariskiExcisionAt A r := by
  intro a b ha hb hab β hβ
  have hz : ZData a b := ⟨ha, hb, hab⟩
  have h1 := act_jb T hz hr β 1
  rw [show ringMap (jb a b) β = 1 from hβ, map_one, Equiv.Perm.one_apply, mul_one] at h1
  obtain ⟨γ, hγ1, hγ2⟩ := Quotient.exact h1
  dsimp only at hγ1 hγ2
  rw [one_mul] at hγ1
  refine ⟨γ⁻¹, ?_, ?_⟩
  · rw [map_inv]
    exact inv_eq_one.mpr hγ1.symm
  · rw [map_inv]
    exact inv_eq_of_mul_eq_one_right hγ2.symm

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.stZariskiExcisionAt_of_tulX

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
