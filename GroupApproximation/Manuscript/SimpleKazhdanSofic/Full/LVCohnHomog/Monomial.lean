import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnDegZero.Defs
import Mathlib.LinearAlgebra.Span.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Homogeneous monomials span the Cohn algebra (lane sk-lv-05)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii: stable `K₂` of the
Cohn algebra `C = C_2(𝔽₂)` vanishes.  This file supplies the first step of the homogeneous
elimination route.  The monomials `x_μ y_ν` span `C` over `𝔽₂`, and each of them is homogeneous
of degree `|μ| - |ν|`.

The proof shows that the span `skCohnHo_monoSpan` is stable under left multiplication by the
four generators.  For `y_i`, write `y_i x_j = δ_{ij}` and use `y_i y_ν = y_{ν ++ [i]}`.  The span
contains `1 = x_∅ y_∅`, so it is all of `C`.

* `skCohnHo_monoSpan`: the `𝔽₂`-span of the monomials `x_μ y_ν`.
* `skCohnHo_mem_monoSpan`: every `c : C` lies in it.
-/

namespace GroupApproximation.Full.LVCohnHomog

open LVCohnRelK1

noncomputable section

/-- The `𝔽₂`-span of the homogeneous monomials `x_μ y_ν` of `C_2(𝔽₂)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skCohnHo_monoSpan : Submodule (ZMod 2) CohnTwoF2 :=
  Submodule.span (ZMod 2) (Set.range fun q : List Bool × List Bool => xw q.1 * yw q.2)

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_monoSpan

/-- Monomials lie in the monomial span.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem skCohnHo_mono_mem (μ ν : List Bool) : xw μ * yw ν ∈ skCohnHo_monoSpan := by
  unfold skCohnHo_monoSpan
  exact Submodule.subset_span ⟨(μ, ν), rfl⟩

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_mono_mem

/-- Left multiplication by `c` preserves the span once it sends monomials into it.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnHo_mul_mem_of_forall {c : CohnTwoF2}
    (hc : ∀ μ ν, c * (xw μ * yw ν) ∈ skCohnHo_monoSpan)
    {z : CohnTwoF2} (hz : z ∈ skCohnHo_monoSpan) : c * z ∈ skCohnHo_monoSpan := by
  unfold skCohnHo_monoSpan at hz
  induction hz using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨q, rfl⟩ := hx
    exact hc q.1 q.2
  | zero =>
    rw [mul_zero]
    exact Submodule.zero_mem _
  | add _ _ _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul a _ _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ a hx

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_mul_mem_of_forall

/-- `x_i x_μ y_ν = x_{i μ} y_ν`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem skCohnHo_cx_mul_mem (i : Bool) (μ ν : List Bool) :
    cx i * (xw μ * yw ν) ∈ skCohnHo_monoSpan := by
  have e : cx i * (xw μ * yw ν) = xw (i :: μ) * yw ν := by
    rw [xw_cons, mul_assoc]
  rw [e]
  exact skCohnHo_mono_mem _ _

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_cx_mul_mem

/-- `y_i x_μ y_ν` is `0` or a monomial, by `y_i x_j = δ_{ij}` and `y_i y_ν = y_{ν ++ [i]}`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnHo_cy_mul_mem (i : Bool) (μ ν : List Bool) :
    cy i * (xw μ * yw ν) ∈ skCohnHo_monoSpan := by
  cases μ with
  | nil =>
    have e : cy i * (xw [] * yw ν) = xw [] * yw (ν ++ [i]) := by
      rw [xw_nil, one_mul, one_mul, LVCohnDegZero.yw_append_single]
    rw [e]
    exact skCohnHo_mono_mem _ _
  | cons j μ =>
    have e : cy i * (xw (j :: μ) * yw ν) = cy i * cx j * (xw μ * yw ν) := by
      rw [xw_cons]
      simp only [mul_assoc]
    rw [e]
    by_cases h : i = j
    · rw [h, cy_cx_self, one_mul]
      exact skCohnHo_mono_mem _ _
    · rw [cy_cx_ne h, zero_mul]
      exact Submodule.zero_mem _

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_cy_mul_mem

/-- The four generators preserve the monomial span.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem skCohnHo_gen_mul_mem (μ ν : List Bool) :
    ∀ g : BinaryLeavitt.Generator,
      cmk (FreeAlgebra.ι (ZMod 2) g) * (xw μ * yw ν) ∈ skCohnHo_monoSpan
  | ⟨0, _⟩ => skCohnHo_cx_mul_mem false μ ν
  | ⟨1, _⟩ => skCohnHo_cx_mul_mem true μ ν
  | ⟨2, _⟩ => skCohnHo_cy_mul_mem false μ ν
  | ⟨3, _⟩ => skCohnHo_cy_mul_mem true μ ν
  | ⟨n + 4, h⟩ => absurd h (Nat.not_lt.mpr (Nat.le_add_left 4 n))

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_gen_mul_mem

/-- Left multiplication by any element of the free algebra preserves the monomial span.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnHo_cmk_mul_mem (a : BinaryLeavitt.Free (ZMod 2)) :
    ∀ z : CohnTwoF2, z ∈ skCohnHo_monoSpan → cmk a * z ∈ skCohnHo_monoSpan := by
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    intro z hz
    rw [AlgHom.commutes, ← Algebra.smul_def]
    exact Submodule.smul_mem _ r hz
  | grade1 g =>
    intro z hz
    exact skCohnHo_mul_mem_of_forall (fun μ ν => skCohnHo_gen_mul_mem μ ν g) hz
  | mul _ _ ha hb =>
    intro z hz
    rw [map_mul, mul_assoc]
    exact ha _ (hb z hz)
  | add _ _ ha hb =>
    intro z hz
    rw [map_add, add_mul]
    exact Submodule.add_mem _ (ha z hz) (hb z hz)

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_cmk_mul_mem

/-- **Monomial spanning**: every element of `C_2(𝔽₂)` is an `𝔽₂`-combination of homogeneous
monomials `x_μ y_ν`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnHo_mem_monoSpan (c : CohnTwoF2) : c ∈ skCohnHo_monoSpan := by
  obtain ⟨a, rfl⟩ := mk_surjective c
  have h1 : (1 : CohnTwoF2) ∈ skCohnHo_monoSpan := by
    have h := skCohnHo_mono_mem [] []
    rwa [xw_nil, yw_nil, one_mul] at h
  have h2 := skCohnHo_cmk_mul_mem a 1 h1
  rwa [mul_one] at h2

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_mem_monoSpan

end

end GroupApproximation.Full.LVCohnHomog
