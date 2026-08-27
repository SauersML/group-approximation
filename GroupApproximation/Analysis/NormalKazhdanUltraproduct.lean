import GroupApproximation.Sofic.OmegaKazhdanCompression

/-!
# NK.05--NK.07: the Kazhdan corner of `thm:normal-kazhdan`

The printed proof of `\label{thm:normal-kazhdan}` runs, in the paragraph *The
Kazhdan corner*:

> the classes `π(g) = [V_{g,n}]_ω` define a unitary representation of `H̄` on
> `H_ω`.  Fix a finite symmetric generating Kazhdan set `S ⊆ K̄` with constant
> `ε₀`, put `θ = 1 − ε₀²/(4|S|)`, and let `h = |S|⁻¹ ∑_{a∈S} π(a) ∈ B_ω` …  The
> spectrum of `h` therefore lies in `[−1,θ] ∪ {1}`, the spectral projection
> `P = χ_{\{1\}}(h)` belongs to `B_ω`, and its range is `Fix π(K̄)`.  Put
> `q = 1 − P`.
>
> If `q = 0` then `π(k) = 1` for every `k ∈ K̄`, against the operator-norm
> separation of a fixed nontrivial element of `K̄`.  For `g ∈ H̄` the projection
> `π(g)Pπ(g)*` has range `Fix π(gK̄g⁻¹) = Fix π(K̄)` by normality, so `P` and `q`
> commute with `π(H̄)` exactly.

Rows `NK.05` and `NK.06` were carried by finite-stage substitutes and `NK.07`
was MISSING, with the note that "the exact commutation of the Kazhdan projection
with the ambient representation has no formal counterpart".  This file supplies
the three algebra-internal statements of that paragraph.

## What is proved, and in which algebra

Everything below is stated for the Kazhdan compression bundle
`KazhdanCompressionRep Γ H B` of `Sofic/UltraproductKazhdanProjection.lean` in an
arbitrary unital C-star algebra `B`, because that is all the arguments use, and
then specialised to `B_ω = OmegaAdjointCorona Y ω`, where the finiteness the
normality step needs is an instance and not a hypothesis.

* `nk_05_spectrum_subset` -- the printed inclusion at the printed constant
  `θ = 1 − κ²/(4|S|)`.  The development's own gap is at `1 − κ²/(2|S|)`, the
  sharper of the two, so the printed statement follows; the two constants belong
  to two different printed theorems and this file does not conflate them.
* `nk_06_rep_eq_one_of_q_eq_zero` -- the printed "if `q = 0` then `π(k) = 1` for
  every `k ∈ K̄`", hence `nk_06_q_ne_zero`: a single non-trivially represented
  element of `K̄` makes `q` nonzero.  This is the nonvanishing the printed proof
  draws from operator-norm separation; separation itself is the hypothesis `hγ`,
  which names the element the printed proof fixes.
* `nk_07_conjugate_proj` -- **normality gives `π(g) P π(g)* = P`**, and hence
  `nk_07_commute_proj` and `nk_07_commute_q`: `P` and `q` commute with `π(H̄)`
  *exactly*, not asymptotically.

## Why normality is the whole of NK.07's first sentence

The one-sided compression step KT.10 already proves `V P V* = P` for the single
compressing element `s`, from Dedekind finiteness.  Normality says that *every*
`g` compresses `ι(Γ)`, so the same bundle with `s := g` is available for each
`g`, and the printed exact commutation is that theorem applied along the group.
`reshift` is exactly that re-pointing of the bundle, and it changes no field that
`avg`, `rate` or `proj` reads -- hence `(reshift D g hg).proj = D.proj` by
definitional equality, and no transport of the projection is needed.

The vector half of the paragraph -- that the range of `P` is `Fix π(K̄)`, and the
lifting of `q` to coordinate projections `q_n` in the printed *compression* step
-- is not here; see the accompanying report.
-/

namespace GroupApproximation
namespace NormalKazhdanUltraproduct

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection

noncomputable section

universe u v w'

section Abstract

variable {Γ : Type u} {H : Type w'} {B : Type v}
variable [Group Γ] [Group H] [CStarAlgebra B]

/-! ## NK.05: the printed spectral inclusion -/

/-- **NK.05, the printed inclusion.**  With `θ = 1 − κ²/(4|S|)`,

`sp(h) ⊆ [−1, θ] ∪ {1}`.

The development proves the gap at `1 − κ²/(2|S|)` (`kt_07_spectrum_subset`),
which is the sharper statement; the printed constant of `thm:normal-kazhdan`
follows because `κ²/(4|S|) ≤ κ²/(2|S|)`, so the printed interval contains the
proved one. -/
theorem nk_05_spectrum_subset (D : KazhdanCompressionRep Γ H B) :
    spectrum ℝ D.avg
      ⊆ Set.Icc (-1 : ℝ) (1 - D.kappa ^ 2 / (4 * (D.S.card : ℝ))) ∪ {1} := by
  have hx : (0 : ℝ) ≤ D.kappa ^ 2 / (2 * (D.S.card : ℝ)) := by positivity
  have heq : D.kappa ^ 2 / (4 * (D.S.card : ℝ))
      = D.kappa ^ 2 / (2 * (D.S.card : ℝ)) / 2 := by
    rw [div_div]
    congr 1
    ring
  have hle : D.rate ≤ 1 - D.kappa ^ 2 / (4 * (D.S.card : ℝ)) := by
    rw [heq]
    show (1 : ℝ) - D.kappa ^ 2 / (2 * (D.S.card : ℝ))
      ≤ 1 - D.kappa ^ 2 / (2 * (D.S.card : ℝ)) / 2
    linarith
  intro μ hμ
  rcases D.kt_07_spectrum_subset hμ with hmem | hmem
  · refine Or.inl (Set.mem_Icc.mpr ⟨(Set.mem_Icc.mp hmem).1, ?_⟩)
    exact le_trans (Set.mem_Icc.mp hmem).2 hle
  · exact Or.inr hmem

/-! ## NK.06: `q = 0` would make `π` trivial on `K̄` -/

/-- **NK.06, the printed nonvanishing argument.**  If `q = 1 − P` vanishes then
`π(ι γ) = 1` for every `γ`.

The whole content is that `P` absorbs every image unitary
(`kt_08_rep_mul_proj`), so `P = 1` forces each `π(ι γ)` to be `1`. -/
theorem nk_06_rep_eq_one_of_q_eq_zero (D : KazhdanCompressionRep Γ H B)
    (hq : (1 : B) - D.proj = 0) (γ : Γ) :
    ((D.pi (D.iota γ) : unitary B) : B) = 1 := by
  have hP : D.proj = 1 := (sub_eq_zero.mp hq).symm
  have h := D.kt_08_rep_mul_proj γ
  rw [hP, mul_one] at h
  exact h

/-- **NK.06, as printed.**  `q ≠ 0`, because `q = 0` would make `π` trivial on
the Kazhdan source, against the operator-norm separation of a fixed nontrivial
element. -/
theorem nk_06_q_ne_zero (D : KazhdanCompressionRep Γ H B) {γ : Γ}
    (hγ : ((D.pi (D.iota γ) : unitary B) : B) ≠ 1) :
    (1 : B) - D.proj ≠ 0 :=
  fun hq ↦ hγ (nk_06_rep_eq_one_of_q_eq_zero D hq γ)

/-! ## NK.07: normality gives exact commutation -/

/-- The compression bundle re-pointed at another compressing element.  Every
field `avg`, `rate` and `proj` read is unchanged, which is what makes the
projection the same object. -/
def reshift (D : KazhdanCompressionRep Γ H B) (g : H)
    (hg : ∀ γ : Γ, ∃ δ : Γ, g * D.iota γ * g⁻¹ = D.iota δ) :
    KazhdanCompressionRep Γ H B :=
  { D with s := g, compresses := hg }

@[simp] theorem reshift_proj (D : KazhdanCompressionRep Γ H B) (g : H)
    (hg : ∀ γ : Γ, ∃ δ : Γ, g * D.iota γ * g⁻¹ = D.iota δ) :
    (reshift D g hg).proj = D.proj := rfl

@[simp] theorem reshift_shift (D : KazhdanCompressionRep Γ H B) (g : H)
    (hg : ∀ γ : Γ, ∃ δ : Γ, g * D.iota γ * g⁻¹ = D.iota δ) :
    (reshift D g hg).shift = ((D.pi g : unitary B) : B) := rfl

/-- **NK.07, first sentence, as printed.**  Normality gives
`π(g) P π(g)* = P`.

The hypothesis `hg` is the printed `g K̄ g⁻¹ ⊆ K̄` at the element `g`, read
through `ι`; it is not a stand-in for anything, being the defining property of a
normal subgroup.  Finiteness of the ambient algebra is the same input KT.10
uses, and for `B_ω` it is an instance. -/
theorem nk_07_conjugate_proj [IsDedekindFiniteMonoid B]
    (D : KazhdanCompressionRep Γ H B) (g : H)
    (hg : ∀ γ : Γ, ∃ δ : Γ, g * D.iota γ * g⁻¹ = D.iota δ) :
    ((D.pi g : unitary B) : B) * D.proj * star ((D.pi g : unitary B) : B)
      = D.proj :=
  kt_10_shift_conjugate_proj (reshift D g hg)

/-- **NK.07, the exact commutation of `P` with `π(H̄)`.** -/
theorem nk_07_commute_proj [IsDedekindFiniteMonoid B]
    (D : KazhdanCompressionRep Γ H B) (g : H)
    (hg : ∀ γ : Γ, ∃ δ : Γ, g * D.iota γ * g⁻¹ = D.iota δ) :
    ((D.pi g : unitary B) : B) * D.proj
      = D.proj * ((D.pi g : unitary B) : B) := by
  have hconj := nk_07_conjugate_proj D g hg
  have hsm : star ((D.pi g : unitary B) : B) * ((D.pi g : unitary B) : B) = 1 :=
    (D.pi g).property.1
  calc ((D.pi g : unitary B) : B) * D.proj
      = ((D.pi g : unitary B) : B) * D.proj
          * (star ((D.pi g : unitary B) : B)
            * ((D.pi g : unitary B) : B)) := by
        rw [hsm, mul_one]
    _ = (((D.pi g : unitary B) : B) * D.proj
          * star ((D.pi g : unitary B) : B))
          * ((D.pi g : unitary B) : B) := by noncomm_ring
    _ = D.proj * ((D.pi g : unitary B) : B) := by rw [hconj]

/-- **NK.07, the exact commutation of `q = 1 − P` with `π(H̄)`.**  This is the
printed "so `P` and `q` commute with `π(H̄)` exactly". -/
theorem nk_07_commute_q [IsDedekindFiniteMonoid B]
    (D : KazhdanCompressionRep Γ H B) (g : H)
    (hg : ∀ γ : Γ, ∃ δ : Γ, g * D.iota γ * g⁻¹ = D.iota δ) :
    ((D.pi g : unitary B) : B) * ((1 : B) - D.proj)
      = ((1 : B) - D.proj) * ((D.pi g : unitary B) : B) := by
  rw [mul_sub, sub_mul, one_mul, mul_one, nk_07_commute_proj D g hg]

end Abstract

/-! ## The same three statements in the norm ultraproduct

`B_ω` is a unital C-star algebra and is Dedekind finite
(`OmegaCoronaFinite.omegaAdjointCorona_isDedekindFiniteMonoid`), so the
normality step below carries no `Prop` premise beyond the bundle and the
normality of the source. -/

section Omega

variable {Γ H : Type} [Group Γ] [Group H]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (ω : Ultrafilter ℕ)

/-- **NK.05 in `B_ω`.** -/
theorem nk_05_omega_spectrum_subset
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    spectrum ℝ D.avg
      ⊆ Set.Icc (-1 : ℝ) (1 - D.kappa ^ 2 / (4 * (D.S.card : ℝ))) ∪ {1} :=
  nk_05_spectrum_subset D

/-- **NK.06 in `B_ω`.** -/
theorem nk_06_omega_q_ne_zero
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) {γ : Γ}
    (hγ : ((D.pi (D.iota γ) : unitary (OmegaAdjointCorona Y ω)) :
        OmegaAdjointCorona Y ω) ≠ 1) :
    (1 : OmegaAdjointCorona Y ω) - D.proj ≠ 0 :=
  nk_06_q_ne_zero D hγ

/-- **NK.07 in `B_ω`.**  Normality of the Kazhdan source makes the Kazhdan
projection commute with the whole ambient representation, exactly. -/
theorem nk_07_omega_commute_proj
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (g : H)
    (hg : ∀ γ : Γ, ∃ δ : Γ, g * D.iota γ * g⁻¹ = D.iota δ) :
    ((D.pi g : unitary (OmegaAdjointCorona Y ω)) : OmegaAdjointCorona Y ω)
        * D.proj
      = D.proj
        * ((D.pi g : unitary (OmegaAdjointCorona Y ω)) :
          OmegaAdjointCorona Y ω) :=
  nk_07_commute_proj D g hg

/-- **NK.07 in `B_ω`, for `q = 1 − P`.** -/
theorem nk_07_omega_commute_q
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (g : H)
    (hg : ∀ γ : Γ, ∃ δ : Γ, g * D.iota γ * g⁻¹ = D.iota δ) :
    ((D.pi g : unitary (OmegaAdjointCorona Y ω)) : OmegaAdjointCorona Y ω)
        * ((1 : OmegaAdjointCorona Y ω) - D.proj)
      = ((1 : OmegaAdjointCorona Y ω) - D.proj)
        * ((D.pi g : unitary (OmegaAdjointCorona Y ω)) :
          OmegaAdjointCorona Y ω) :=
  nk_07_commute_q D g hg

end Omega

end

end NormalKazhdanUltraproduct
end GroupApproximation
