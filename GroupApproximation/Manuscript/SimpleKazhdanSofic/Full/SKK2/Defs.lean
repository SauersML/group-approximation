import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZeroCore.Grading
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVK2Route.SubringMV
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Ultramatricial
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Units
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVPolyK2.Localization
import GroupApproximation.Meta.AxiomGuard

/-!
# Stable `K₂(L_{𝔽₂}(1,2)) = 0`: shared objects and step statements (program sk-k2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  The plan is
`board/sk-k2.md` in the swarm workspace.  Write `L = L_{𝔽₂}(1,2)`, graded by length
(`LVLowKZeroCore.grade`: `sᵢ` in degree `1`, `tᵢ` in degree `-1`).  This module fixes

* the subrings `posSubring = L_{≥0}`, `negSubring = L_{≤0}` and
  `zeroSubring = L₊ ⊓ L₋ = L₀`, defined by vanishing of graded components;
* the step statements, one per lane:
  - `SkK2GerstenStatement` (lane sk-k2-gersten): stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0`;
  - `SkK2HalfStatement` (lane sk-k2-loc): stable `K₂(L₊) = K₂(L₋) = 0`.  The route:
    `L₊ = ⋃ₙ Tₙ` with `Tₙ = span{s_α s_w t_β : |α| = |β| = n} ≅ M_{2ⁿ}(𝔽₂⟨x₀,x₁⟩)`, and the
    same for `L₋` with `t`-words;
  - `SkK2ZeroStatement` (lane sk-k2-loc): `L₀` is ultramatricial over `𝔽₂`;
  - `SkK2WeakMVStatement` (lane ms-sk-uncond-a): after padding, every `k ∈ K₂(n, L)` is
    `a · b` with `a ∈ St(L₊)` and `b ∈ St(L₋)`.  This is the Mayer–Vietoris / localization
    core; ABC 2009 obtain it from Yao 1995, Thm 2.1, through the corner-shift colimit of
    Thm 3.6, Step 3;
* the assembly `skK2_stableK2Trivial_of_factorization`: the half statement and the
  Mayer–Vietoris factorization of `LVK2Route.SubringMV` give stable `K₂(L) = 0`.  The reduction
  of `LVK2Route.SubringFactorization` to `SkK2WeakMVStatement` and `SkK2ZeroStatement` (the
  common factor `c` comes from `K₁(L₀) = 0`) is the next item of lane ms-sk-uncond-a.

Every statement is TRUE: stable `K₂(L) = 0` is Ara–Brustenga–Cortiñas 2009, Thm 7.6, and each
step follows from it or is a published input (Gersten 1974).  LOUD: `SkK2WeakMVStatement` is
implied by the target (take `a = b = 1` after padding), so it is not strictly weaker.  It is the
part of the target that remains once the half rings are known.
-/

namespace GroupApproximation.Full.SKK2

open SteinbergGroup

noncomputable section

/-- The binary Leavitt algebra over `𝔽₂`.  (`simple_kazhdan_sofic_group.tex` l.733-735.) -/
abbrev L : Type := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

/-- A product of two elements of `R[ℤ]` supported in an additively closed set `S` vanishes
outside `S`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skK2_coeff_mul_eq_zero {R : Type*} [Semiring R] (x y : AddMonoidAlgebra R ℤ)
    (S : Set ℤ) (hS : ∀ a b : ℤ, a ∈ S → b ∈ S → a + b ∈ S)
    (hx : ∀ d : ℤ, d ∉ S → x.coeff d = 0) (hy : ∀ d : ℤ, d ∉ S → y.coeff d = 0)
    (d : ℤ) (hd : d ∉ S) : (x * y).coeff d = 0 := by
  rw [AddMonoidAlgebra.coeff_mul]
  refine Finset.sum_eq_zero ?_
  intro m₁ hm₁
  refine Finset.sum_eq_zero ?_
  intro m₂ hm₂
  refine if_neg ?_
  intro h
  apply hd
  rw [← h]
  refine hS m₁ m₂ ?_ ?_
  · by_contra hc
    exact (Finsupp.mem_support_iff.mp hm₁) (hx m₁ hc)
  · by_contra hc
    exact (Finsupp.mem_support_iff.mp hm₂) (hy m₂ hc)

/-- The elements of `L` whose graded components vanish outside an additively closed set `S`
containing `0` form a subring.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skK2_supportedSubring (S : Set ℤ) (h0 : (0 : ℤ) ∈ S)
    (hS : ∀ a b : ℤ, a ∈ S → b ∈ S → a + b ∈ S) : Subring L where
  carrier := {x | ∀ d : ℤ, d ∉ S → (LVLowKZeroCore.grade (ZMod 2) x).coeff d = 0}
  mul_mem' := by
    intro x y hx hy d hd
    rw [map_mul]
    exact skK2_coeff_mul_eq_zero _ _ S hS hx hy d hd
  one_mem' := by
    intro d hd
    have hne : d ≠ 0 := fun e => hd (e ▸ h0)
    rw [map_one, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
    exact Finsupp.single_eq_of_ne (by omega)
  add_mem' := by
    intro x y hx hy d hd
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx d hd, hy d hd, add_zero]
  zero_mem' := by
    intro d _
    rw [map_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  neg_mem' := by
    intro x hx d hd
    rw [map_neg, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, hx d hd, neg_zero]

/-- `L₊ = L_{≥0}`, the elements with no components in negative degree.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def posSubring : Subring L :=
  skK2_supportedSubring {d | 0 ≤ d} (le_refl 0) (fun _ _ ha hb => add_nonneg ha hb)

/-- `L₋ = L_{≤0}`, the elements with no components in positive degree.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def negSubring : Subring L :=
  skK2_supportedSubring {d | d ≤ 0} (le_refl 0) (fun _ _ ha hb => add_nonpos ha hb)

/-- `L₀ = L₊ ⊓ L₋`, the degree-zero part.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def zeroSubring : Subring L := posSubring ⊓ negSubring

/-- `L₀ ≤ L₊`.  (`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem zeroSubring_le_pos : zeroSubring ≤ posSubring := inf_le_left

/-- `L₀ ≤ L₋`.  (`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem zeroSubring_le_neg : zeroSubring ≤ negSubring := inf_le_right

/-- **Step K2-1 (lane sk-k2-gersten).**  Stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0` (Gersten 1974).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def SkK2GerstenStatement : Prop :=
  LVH2GL3.StableK2Trivial (FreeAlgebra (ZMod 2) (Fin 2))

/-- **Step K2-2 (lane sk-k2-loc).**  Stable `K₂(L₊) = 0` and stable `K₂(L₋) = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def SkK2HalfStatement : Prop :=
  LVH2GL3.StableK2Trivial posSubring ∧ LVH2GL3.StableK2Trivial negSubring

/-- **Step K2-0 (lane sk-k2-loc).**  `L₀` is ultramatricial over `𝔽₂` (the stages
`span{s_α t_β : |α| = |β| = n} ≅ M_{2ⁿ}(𝔽₂)` of `KOne/LeavittDegreeZeroTower`).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def SkK2ZeroStatement : Prop :=
  LVSkewLaurentK2.IsUltramatricialF2 zeroSubring

/-- **Step K2-3 (lane ms-sk-uncond-a).**  Weak Mayer–Vietoris factorization: after padding,
every `k ∈ K₂(n, L)` is `a · b` with `a ∈ St_N(L₊)` and `b ∈ St_N(L₋)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def SkK2WeakMVStatement : Prop :=
  ∀ (n : ℕ) (k : SteinbergGroup (Fin n) L), projection k = 1 →
    ∃ (N : ℕ) (h : n ≤ N) (a : SteinbergGroup (Fin N) posSubring)
      (b : SteinbergGroup (Fin N) negSubring),
      indexMap (Fin.castLEEmb h) k = ringMap posSubring.subtype a * ringMap negSubring.subtype b

/-- Step K2-0 gives stable `K₂(L₀) = 0` (Morita, finite products, directed unions, and
`K₂(𝔽₂) = 0`).  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skK2_zero_stableK2Trivial (h : SkK2ZeroStatement) :
    LVH2GL3.StableK2Trivial zeroSubring :=
  LVCohnK2.stableK2Trivial_of_isUltramatricialF2 LVFieldK2.stableK2Trivial_zmodTwo h

#audit_axioms GroupApproximation.Full.SKK2.skK2_zero_stableK2Trivial

/-- Step K2-0 gives `K₁(L₀) = 0` in the form `GL_n(L₀) = E_n(L₀)` for `n ≥ 2`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skK2_zero_k1Statement (h : SkK2ZeroStatement) :
    LVSkewLaurentK2.K1Statement zeroSubring :=
  LVSkewLaurentK2.k1Statement_of_ultramatricial h

#audit_axioms GroupApproximation.Full.SKK2.skK2_zero_k1Statement

/-- **Assembly.**  Stable `K₂(L₊) = K₂(L₋) = 0` and the Mayer–Vietoris factorization of the
square `L₀ ≤ L₊, L₋ ≤ L` give stable `K₂(L_{𝔽₂}(1,2)) = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skK2_stableK2Trivial_of_factorization (hH : SkK2HalfStatement)
    (hF : LVK2Route.SubringFactorization posSubring negSubring zeroSubring zeroSubring_le_pos) :
    LVH2GL3.StableK2Trivial L :=
  LVK2Route.stableK2Trivial_of_subringFactorization zeroSubring_le_pos zeroSubring_le_neg hF
    hH.1 hH.2

#audit_axioms GroupApproximation.Full.SKK2.skK2_stableK2Trivial_of_factorization

/-- **tex l.733-735, first clause**, from the half statement and the factorization.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem skK2_manuscriptSentence_of_factorization (hH : SkK2HalfStatement)
    (hF : LVK2Route.SubringFactorization posSubring negSubring zeroSubring zeroSubring_le_pos) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E :=
  (LVPolyK2.skLoc_manuscriptSentence_of_leavittStableK2
    (skK2_stableK2Trivial_of_factorization hH hF)).1

#audit_axioms GroupApproximation.Full.SKK2.skK2_manuscriptSentence_of_factorization

end

end GroupApproximation.Full.SKK2
