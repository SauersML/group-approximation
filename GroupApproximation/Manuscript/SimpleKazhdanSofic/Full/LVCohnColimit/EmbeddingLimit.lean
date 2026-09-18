import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Shift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# The canonical corner-shift colimit of `C_2(𝔽₂) × 𝔽₂` (lane LVCohnColimit2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), route (W1), leaf T1b.iii.  Source:
Ara–Brustenga–Cortiñas, *K-theory of Leavitt path algebras*, Münster J. Math. 2 (2009),
Thm 3.6, Step 3 (`yaoseq6.tex` `thm:skewyao`, l.640-688).  There `η(x) = t₊ x t₋` and
`η^{-1}(R ⊗ A)[t₊, t₋, φ ⊗ 1]` is the colimit of `η`.  On `C = C_2(𝔽₂)`, with its unit adjoined,
the colimit is the direct limit of the unital shifts
`θ_m : C × 𝔽₂ → C × 𝔽₂`, `(c, ε) ↦ (x₀^m c y₀^m + ε (1 - x₀^m y₀^m), ε)`.

This file builds that direct limit with Mathlib's `DirectLimit`:

* `cohnTheta_zero`, `cohnTheta_comp`: `θ_0 = id` and `θ_a ∘ θ_b = θ_{a+b}`;
* `cohnTheta_injective`: `θ_m` is injective, since `y^m (θ_m p).1 x^m = p.1`;
* `CohnLimit`: the direct limit of `C × 𝔽₂` along `θ_{j-i}`, which is a ring;
* `cohnLimitOf M : C × 𝔽₂ →+* CohnLimit`: the canonical maps.  They are injective
  (`cohnLimitOf_injective`), their ranges exhaust the limit (`exists_range_cohnLimitOf`), and
  they are compatible: `ι_M ∘ θ_M = ι_0` (`cohnLimitOf_comp_cohnTheta`);
* `exists_cohnColimit_embedding_of_stableK2Trivial`: if the limit has stable `K₂ = 0`, then
  the statement `exists_cohnColimit_embedding` holds, with `D = CohnLimit`.

So the target reduces to the single statement `LVH2GL3.StableK2Trivial CohnLimit`.
-/

namespace GroupApproximation.Full.LVCohnColimit

noncomputable section

open LVCohnRelK1

section Corner

variable {R : Type*} [Ring R] {K : Type*} [CommRing K] [Algebra K R]

/-- `θ_{u,v}` has the left inverse `c ↦ v c u` on the first coordinate:
`v (u c v + ε (1 - u v)) u = c`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerUnital_fst_left_inv (u v : R) (h : v * u = 1) (c : R × K) :
    v * (cornerUnital u v h c).1 * u = c.1 := by
  rw [cornerUnital_fst]
  have e1 : v * (u * c.1 * v) * u = c.1 := by
    rw [← mul_assoc v (u * c.1) v, ← mul_assoc v u c.1, h, one_mul, mul_assoc, h, mul_one]
  have e2 : v * (algebraMap K R c.2 * (1 - u * v)) * u = 0 := by
    rw [← mul_assoc v (algebraMap K R c.2) (1 - u * v), ← Algebra.commutes c.2 v,
      mul_assoc (algebraMap K R c.2) v (1 - u * v), mul_one_sub_mul_eq_zero h, mul_zero,
      zero_mul]
  rw [mul_add, add_mul, e1, e2, add_zero]

end Corner

/-- `θ_0` is the identity.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnTheta_zero : cohnTheta 0 = RingHom.id (CohnTwoF2 × ZMod 2) := by
  refine RingHom.ext fun c => Prod.ext ?_ rfl
  show cx false ^ 0 * c.1 * cy false ^ 0 +
      algebraMap (ZMod 2) CohnTwoF2 c.2 * (1 - cx false ^ 0 * cy false ^ 0) = c.1
  simp only [pow_zero, one_mul, mul_one, sub_self, mul_zero, add_zero]

/-- `θ_a ∘ θ_b = θ_{a+b}`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnTheta_comp (a b : ℕ) : (cohnTheta a).comp (cohnTheta b) = cohnTheta (a + b) := by
  induction a with
  | zero => rw [cohnTheta_zero, RingHom.id_comp, Nat.zero_add]
  | succ a ih =>
    rw [← cohnTheta_one_comp a, RingHom.comp_assoc, ih, cohnTheta_one_comp]
    exact congrArg cohnTheta (by omega)

/-- `θ_m` is injective.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnTheta_injective (m : ℕ) : Function.Injective (cohnTheta m) := by
  intro p q hpq
  refine Prod.ext ?_ ?_
  · have h1 : cy false ^ m * (cohnTheta m p).1 * cx false ^ m =
        cy false ^ m * (cohnTheta m q).1 * cx false ^ m := by
      rw [hpq]
    rwa [cohnTheta, cornerUnital_fst_left_inv, cornerUnital_fst_left_inv] at h1
  · have h2 : (cohnTheta m p).2 = (cohnTheta m q).2 := by
      rw [hpq]
    rwa [cohnTheta, cornerUnital_snd, cornerUnital_snd] at h2

/-- The transition map from stage `i` to stage `j ≥ i`: `θ_{j-i}`.  (`yaoseq6.tex`
`thm:skewyao`, Step 3, the inductive system of `η`; `simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
def cohnStep (i j : ℕ) (_h : i ≤ j) : CohnTwoF2 × ZMod 2 →+* CohnTwoF2 × ZMod 2 :=
  cohnTheta (j - i)

/-- The transition maps `θ_{j-i}` form a directed system.  (`yaoseq6.tex` `thm:skewyao`,
Step 3; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
instance cohnDirectedSystem :
    DirectedSystem (fun _ : ℕ => CohnTwoF2 × ZMod 2) (fun i j h => ⇑(cohnStep i j h)) where
  map_self := fun i x => by
    show cohnTheta (i - i) x = x
    rw [Nat.sub_self, cohnTheta_zero, RingHom.id_apply]
  map_map := fun {k j i} hij hjk x => by
    show cohnTheta (k - j) (cohnTheta (j - i) x) = cohnTheta (k - i) x
    exact (RingHom.congr_fun (cohnTheta_comp (k - j) (j - i)) x).trans
      (by rw [show k - j + (j - i) = k - i by omega])

/-- **The corner-shift colimit** `D = colim (C × 𝔽₂, θ)`, the unitization of `η^{-1} C`.
(`yaoseq6.tex` `thm:skewyao`, Step 3; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
abbrev CohnLimit : Type :=
  DirectLimit (fun _ : ℕ => CohnTwoF2 × ZMod 2) cohnStep

/-- The canonical map `ι_M : C × 𝔽₂ → D` from stage `M`.  (`yaoseq6.tex` `thm:skewyao`,
Step 3, the maps `φ_n`; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def cohnLimitOf (M : ℕ) : CohnTwoF2 × ZMod 2 →+* CohnLimit where
  toFun x := ⟦⟨M, x⟩⟧
  map_one' := (DirectLimit.one_def (G := fun _ : ℕ => CohnTwoF2 × ZMod 2) (f := cohnStep) M).symm
  map_mul' x y :=
    (DirectLimit.mul_def (G := fun _ : ℕ => CohnTwoF2 × ZMod 2) (f := cohnStep) M x y).symm
  map_zero' :=
    (DirectLimit.zero_def (G := fun _ : ℕ => CohnTwoF2 × ZMod 2) (f := cohnStep) M).symm
  map_add' x y :=
    (DirectLimit.add_def (G := fun _ : ℕ => CohnTwoF2 × ZMod 2) (f := cohnStep) M x y).symm

/-- `ι_{M+k} ∘ θ_k = ι_M`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnLimitOf_comp (M k : ℕ) :
    (cohnLimitOf (M + k)).comp (cohnTheta k) = cohnLimitOf M := by
  refine RingHom.ext fun x => ?_
  have e := DirectLimit.mk_apply (F := fun _ : ℕ => CohnTwoF2 × ZMod 2) (f := cohnStep)
    M (M + k) x (Nat.le_add_right M k)
  rw [cohnStep, Nat.add_sub_cancel_left] at e
  exact e

/-- Compatibility `ι_M ∘ θ_M = ι_0`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnLimitOf_comp_cohnTheta (M : ℕ) :
    (cohnLimitOf M).comp (cohnTheta M) = cohnLimitOf 0 := by
  have e := cohnLimitOf_comp 0 M
  rwa [Nat.zero_add] at e

/-- Each `ι_M` is injective, since every `θ_m` is.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnLimitOf_injective (M : ℕ) : Function.Injective (cohnLimitOf M) :=
  DirectLimit.mk_injective (F := fun _ : ℕ => CohnTwoF2 × ZMod 2) (f := cohnStep)
    (fun i j _ => cohnTheta_injective (j - i)) M

/-- The ranges of the `ι_M` increase.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem mem_range_cohnLimitOf_of_le {N M : ℕ} (h : N ≤ M) {z : CohnLimit}
    (hz : z ∈ (cohnLimitOf N).range) : z ∈ (cohnLimitOf M).range := by
  obtain ⟨x, rfl⟩ := RingHom.mem_range.mp hz
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact RingHom.mem_range.mpr ⟨cohnTheta k x, RingHom.congr_fun (cohnLimitOf_comp N k) x⟩

/-- Every finite subset of `D` lies in the range of one `ι_M`.  (`yaoseq6.tex` `thm:skewyao`,
Step 3; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_range_cohnLimitOf (s : Finset CohnLimit) :
    ∃ M, (s : Set CohnLimit) ⊆ ((cohnLimitOf M).range : Set CohnLimit) := by
  choose ix x hx using fun z : CohnLimit =>
    DirectLimit.exists_eq_mk (F := fun _ : ℕ => CohnTwoF2 × ZMod 2) (f := cohnStep) z
  refine ⟨s.sup ix, fun z hz => ?_⟩
  refine mem_range_cohnLimitOf_of_le (Finset.le_sup (Finset.mem_coe.mp hz)) ?_
  exact RingHom.mem_range.mpr ⟨x z, (hx z).symm⟩

/-- **Reduction of `exists_cohnColimit_embedding`.**  If the corner-shift colimit
`D = colim (C × 𝔽₂, θ)` has stable `K₂ = 0`, then there is a ring `D` with stable `K₂ = 0` and
injective, exhausting, compatible maps `ι_M : C × 𝔽₂ → D` with `ι_M ∘ θ_M = ι_0`.  Take the
canonical maps into the colimit.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, route (W1), leaf T1b.iii.) -/
theorem exists_cohnColimit_embedding_of_stableK2Trivial
    (hD : LVH2GL3.StableK2Trivial CohnLimit) :
    ∃ (D : Type) (_ : Ring D), LVH2GL3.StableK2Trivial D ∧
      ∃ ι : ℕ → (LVCohnRelK1.CohnTwoF2 × ZMod 2 →+* D),
        (∀ M, Function.Injective (ι M)) ∧
        (∀ s : Finset D, ∃ M, (s : Set D) ⊆ ((ι M).range : Set D)) ∧
        ∀ M, (ι M).comp (cohnTheta M) = ι 0 :=
  ⟨CohnLimit, inferInstance, hD, cohnLimitOf, cohnLimitOf_injective, exists_range_cohnLimitOf,
    cohnLimitOf_comp_cohnTheta⟩

end

end GroupApproximation.Full.LVCohnColimit
