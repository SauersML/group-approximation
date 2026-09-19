import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsLeastPeriod
import GroupApproximation.Dynamics.SubshiftFiniteWindow
import GroupApproximation.Pestov91.LEFCrossedProduct
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The asymptotic ring models `φ_ℓ` on the least period

`simple_kazhdan_sofic_group.tex` at e80dcf20a, "Finite models", tex 134–145:

> On $\F_2^{\Z/N_\ell\Z}$ let $P\delta_t=\delta_{t+1}$. For $f$ depending only on coordinates in
> $[-\ell,\ell]$ let $D_\ell(f)\delta_t=f(T^ty_\ell)\delta_t$, where $f(T^ty_\ell)$ is the value of
> $f$ at any point of $X$ that agrees with $T^ty_\ell$ on $[-\ell,\ell]$. When every $f_j$ depends
> only on coordinates in $[-\ell,\ell]$, put $\varphi_\ell(\sum_jf_ju^j)=\sum_jD_\ell(f_j)P^j$. Since
> $PD_\ell(f)P^{-1}=D_\ell(f\circ T^{-1})$, for fixed $r,s\in R$ the identities
> $\varphi_\ell(r+s)=\varphi_\ell(r)+\varphi_\ell(s)$ and $\varphi_\ell(rs)=\varphi_\ell(r)\varphi_\ell(s)$
> hold for large $\ell$. If $r=\sum_jf_ju^j\ne0$, then for large $\ell$ some $D_\ell(f_j)\ne0$, and the
> terms $D_\ell(f_j)P^j$ have disjoint supports once $N_\ell>2|j|$ for all exponents $j$ of $r$, so
> $\varphi_\ell(r)\ne0$.

For a fixed point `x` of an infinite minimal subshift, `m ℓ` is the recurrence position of
`exists_occurrences_of_mem`, `y_ℓ = periodicExt x (m ℓ)` and `N ℓ = leastPeriod y_ℓ`.

* `D ℓ` evaluates a coefficient at a chosen point of `X` agreeing with `T^t y_ℓ` on `[-ℓ, ℓ]`, for
  `t` the representative of a residue mod `N ℓ`.  Clause `hform`: for `f` depending only on
  `[-ℓ, ℓ]`, the value is that of any such point.
* `φ_ℓ = Pestov91.periodicModel (D ℓ)`, which sends `single g a` to `diagonal (D a) * P^{toAdd g}`
  with `P = Pestov91.shiftMatrix k (N ℓ) 1`.  It is additive and unital for every `ℓ`.
* Clause `hcov`: `D ℓ (f ∘ T^{-j})(n) = D ℓ f (n - j)` for `f` depending on `[-ℓ', ℓ']` with
  `ℓ' + |j| ≤ ℓ`; with `Pestov91.shiftMatrix_mul_diagonal` this is `P^j D_ℓ(f) P^{-j} = D_ℓ(f∘T^{-j})`.
* For fixed `r, s`, `φ_ℓ(r s) = φ_ℓ(r) φ_ℓ(s)` for large `ℓ`; for `r ≠ 0`, `φ_ℓ(r) ≠ 0` for large `ℓ`;
  `N ℓ → ∞`.

* `AsymptoticModels X T x k`, `exists_asymptoticModels`, and the closed `printedAsymptoticModels`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift WordGraph Filter
open Multiplicative (toAdd)

/-- **The asymptotic models of the note** (tex 121–145), at a point `x` of `X`: recurrence positions
`m ℓ`, least periods `N ℓ` of `y_ℓ = periodicExt x (m ℓ)`, and diagonal evaluations `D ℓ`, such that
`y_ℓ` has the same words of length `2ℓ + 1` as `X`, `D ℓ` is the printed evaluation, covariance holds,
`N ℓ → ∞`, and `φ_ℓ = periodicModel (D ℓ)` is eventually multiplicative on every pair.  The tip's route
(simple_kazhdan_sofic_group.tex at 696c4b602) no longer uses eventual nonvanishing: nontriviality of words comes
from the ultraproduct kernel argument of thm:general. -/
abbrev AsymptoticModels {A : Type} [TopologicalSpace A] (X : Set (ℤ → A)) (T : ↥X ≃ₜ ↥X)
    (x : ℤ → A) (k : Type) [Ring k] : Prop :=
  ∃ (m N : ℕ → ℕ) (_ : ∀ ℓ, NeZero (N ℓ)) (D : ∀ ℓ, ClopenCoeff T k →+* (ZMod (N ℓ) → k)),
    (∀ ℓ, 2 * ℓ + 1 ≤ m ℓ ∧ word x 0 (2 * ℓ) = word x (m ℓ) (2 * ℓ) ∧
      N ℓ = leastPeriod (periodicExt x (m ℓ)) ∧
      {w | ∃ t : ℤ, word (periodicExt x (m ℓ)) t (2 * ℓ + 1) = w} = language X (2 * ℓ + 1)) ∧
    (∀ (ℓ : ℕ) (f : ClopenCoeff T k),
      (∀ y z : ↥X, (∀ i : ℤ, |i| ≤ ℓ → y.1 i = z.1 i) →
        (ClopenCoeff.of T k).symm f y = (ClopenCoeff.of T k).symm f z) →
      ∀ (t : ℤ) (z : ↥X), (∀ i : ℤ, |i| ≤ ℓ → z.1 i = periodicExt x (m ℓ) (t + i)) →
        D ℓ f (t : ZMod (N ℓ)) = (ClopenCoeff.of T k).symm f z) ∧
    (∀ (ℓ : ℕ) (ℓ' : ℕ) (f : ClopenCoeff T k),
      (∀ y z : ↥X, (∀ i : ℤ, |i| ≤ ℓ' → y.1 i = z.1 i) →
        (ClopenCoeff.of T k).symm f y = (ClopenCoeff.of T k).symm f z) →
      ∀ g : Multiplicative ℤ, (ℓ' : ℤ) + |toAdd g| ≤ (ℓ : ℤ) → ∀ n : ZMod (N ℓ),
        D ℓ (g • f) n = D ℓ f (n - ((toAdd g : ℤ) : ZMod (N ℓ)))) ∧
    Tendsto N atTop atTop ∧
    ∀ r s : ClopenCrossedProduct T k, ∀ᶠ ℓ in atTop,
      Pestov91.periodicModel (D ℓ) (r * s) =
        Pestov91.periodicModel (D ℓ) r * Pestov91.periodicModel (D ℓ) s

/-- **The asymptotic models exist** for every point of an infinite minimal subshift over a finite
alphabet and every ring `k` (tex 121–145). -/
theorem exists_asymptoticModels {A : Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {X : Set (ℤ → A)} (hXc : IsClosed X) (hX : ∀ n : ℤ, Set.MapsTo (shift n) X X)
    (hinf : X.Infinite)
    (hmin : ∀ C : Set (ℤ → A), IsClosed C → C ⊆ X → (∀ g : ℤ, Set.MapsTo (shift g) C C) →
      C = ∅ ∨ C = X)
    (T : ↥X ≃ₜ ↥X) (hT : ∀ x : ↥X, (T x).1 = shift 1 x.1) {x : ℤ → A} (hx : x ∈ X)
    (k : Type) [Ring k] : AsymptoticModels X T x k := by
  classical
  choose m _hm0 hmk hrep hseg using fun ℓ : ℕ => exists_occurrences_of_mem hXc hX hmin hx ℓ 0
  haveI hmz : ∀ ℓ, NeZero (m ℓ) := fun ℓ => ⟨by have := hmk ℓ; omega⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ → ℕ, ∀ ℓ, N ℓ = leastPeriod (periodicExt x (m ℓ)) :=
    ⟨_, fun _ => rfl⟩
  have hNpos : ∀ ℓ, 0 < N ℓ := fun ℓ => by rw [hNdef]; exact leastPeriod_periodicExt_pos x
  haveI hNz : ∀ ℓ, NeZero (N ℓ) := fun ℓ => ⟨(hNpos ℓ).ne'⟩
  have hper : ∀ (ℓ : ℕ) (t : ℤ), periodicExt x (m ℓ) (N ℓ + t) = periodicExt x (m ℓ) t := fun ℓ t => by
    rw [hNdef]
    exact periodicExt_leastPeriod_add x (m ℓ) t
  have hcong : ∀ ℓ {a b : ℤ}, (a : ZMod (N ℓ)) = (b : ZMod (N ℓ)) → ∀ i : ℤ,
      periodicExt x (m ℓ) (a + i) = periodicExt x (m ℓ) (b + i) := by
    intro ℓ a b hab i
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a b (N ℓ)).1 hab
    rw [show b + i = a + i + (N ℓ : ℤ) * q by linarith]
    exact (periodic_add_mul (hper ℓ) (a + i) q).symm
  have hlang : ∀ ℓ, {w | ∃ t : ℤ, word (periodicExt x (m ℓ)) t (2 * ℓ + 1) = w} =
      language X (2 * ℓ + 1) := fun ℓ => language_periodicExt hX hx (hrep ℓ) (hmk ℓ) (hseg ℓ)
  have hpt : ∀ (ℓ : ℕ) (t : ℤ), ∃ z : ↥X, ∀ i : ℤ, |i| ≤ ℓ →
      z.1 i = periodicExt x (m ℓ) (t + i) := by
    intro ℓ t
    have hwin : word (periodicExt x (m ℓ)) (t - ℓ) (2 * ℓ + 1) ∈ language X (2 * ℓ + 1) := by
      rw [← hlang ℓ]
      exact ⟨t - ℓ, rfl⟩
    obtain ⟨z0, hz0, hz0w⟩ := hwin
    refine ⟨⟨shift (ℓ : ℤ) z0, hX ℓ hz0⟩, fun i hi => ?_⟩
    obtain ⟨hi1, hi2⟩ := abs_le.mp hi
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = ℓ + i := ⟨(ℓ + i).toNat, Int.toNat_of_nonneg (by omega)⟩
    have h := congrFun hz0w ⟨j, by omega⟩
    simp only [word_apply, zero_add] at h
    show z0 (ℓ + i) = _
    rw [← hj, h]
    congr 1
    omega
  choose w hw using hpt
  obtain ⟨D, hDdef⟩ : ∃ D : ∀ ℓ, ClopenCoeff T k →+* (ZMod (N ℓ) → k),
      ∀ ℓ f n, D ℓ f n = (ClopenCoeff.of T k).symm f (w ℓ ((n.val : ℕ) : ℤ)) :=
    ⟨fun ℓ =>
      { toFun := fun f n => (ClopenCoeff.of T k).symm f (w ℓ ((n.val : ℕ) : ℤ))
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }, fun _ _ _ => rfl⟩
  have hval : ∀ (ℓ : ℕ) (n : ZMod (N ℓ)), (((n.val : ℕ) : ℤ) : ZMod (N ℓ)) = n := fun ℓ n => by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  choose rad hrad using fun f : ClopenCoeff T k => exists_radius hXc ((ClopenCoeff.of T k).symm f)
  have hdep : ∀ (f : ClopenCoeff T k) (ℓ' : ℕ), rad f ≤ ℓ' → ∀ y z : ↥X,
      (∀ i : ℤ, |i| ≤ ℓ' → y.1 i = z.1 i) →
        (ClopenCoeff.of T k).symm f y = (ClopenCoeff.of T k).symm f z :=
    fun f ℓ' hle y z hyz => hrad f y z fun i hi => hyz i (hi.trans (by exact_mod_cast hle))
  have hform : ∀ (ℓ : ℕ) (f : ClopenCoeff T k),
      (∀ y z : ↥X, (∀ i : ℤ, |i| ≤ ℓ → y.1 i = z.1 i) →
        (ClopenCoeff.of T k).symm f y = (ClopenCoeff.of T k).symm f z) →
      ∀ (t : ℤ) (z : ↥X), (∀ i : ℤ, |i| ≤ ℓ → z.1 i = periodicExt x (m ℓ) (t + i)) →
        D ℓ f (t : ZMod (N ℓ)) = (ClopenCoeff.of T k).symm f z := by
    intro ℓ f hf t z hz
    rw [hDdef]
    refine hf _ _ fun i hi => ?_
    rw [hw ℓ _ i hi, hz i hi]
    exact hcong ℓ (hval ℓ _) i
  have hcovD : ∀ (ℓ : ℕ) (ℓ' : ℕ) (f : ClopenCoeff T k),
      (∀ y z : ↥X, (∀ i : ℤ, |i| ≤ ℓ' → y.1 i = z.1 i) →
        (ClopenCoeff.of T k).symm f y = (ClopenCoeff.of T k).symm f z) →
      ∀ g : Multiplicative ℤ, (ℓ' : ℤ) + |toAdd g| ≤ (ℓ : ℤ) → ∀ n : ZMod (N ℓ),
        D ℓ (g • f) n = D ℓ f (n - ((toAdd g : ℤ) : ZMod (N ℓ))) := by
    intro ℓ ℓ' f hf g hg n
    rw [hDdef, hDdef]
    show (ClopenCoeff.of T k).symm f ((T ^ (-toAdd g)) (w ℓ ((n.val : ℕ) : ℤ))) =
      (ClopenCoeff.of T k).symm f (w ℓ (((n - ((toAdd g : ℤ) : ZMod (N ℓ))).val : ℕ) : ℤ))
    refine hf _ _ fun i hi => ?_
    have h1 := le_abs_self (toAdd g)
    have h2 := neg_abs_le (toAdd g)
    obtain ⟨hi1, hi2⟩ := abs_le.mp hi
    rw [zpow_apply_coord hT, hw ℓ _ (-toAdd g + i) (abs_le.mpr ⟨by omega, by omega⟩),
      hw ℓ _ i (abs_le.mpr ⟨by omega, by omega⟩),
      show ((n.val : ℕ) : ℤ) + (-toAdd g + i) = (((n.val : ℕ) : ℤ) - toAdd g) + i by ring]
    exact hcong ℓ (by simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]) i
  have hNtend : Tendsto N atTop atTop := by
    refine tendsto_atTop_mono (fun ℓ => ?_)
      ((tendsto_ncard_language hX hinf).comp
        (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩ :
          Tendsto (fun ℓ : ℕ => 2 * ℓ + 1) atTop atTop))
    show (language X (2 * ℓ + 1)).ncard ≤ N ℓ
    rw [hNdef]
    exact ncard_language_le_leastPeriod hX hx (hrep ℓ) (hmk ℓ) (hseg ℓ)
  refine ⟨m, N, hNz, D, fun ℓ => ⟨hmk ℓ, hrep ℓ, hNdef ℓ, hlang ℓ⟩, hform, hcovD, hNtend, ?_⟩
  · intro r s
    obtain ⟨B, hbd⟩ : ∃ B : ℕ, ∀ g ∈ SkewMonoidAlgebra.support r, |toAdd g| ≤ B :=
      ⟨(SkewMonoidAlgebra.support r).sup fun g ↦ (toAdd g).natAbs,
        fun g hg ↦ by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast Finset.le_sup (f := fun g : Multiplicative ℤ ↦ (toAdd g).natAbs) hg⟩
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, ∀ h ∈ SkewMonoidAlgebra.support s,
        rad (SkewMonoidAlgebra.coeff s h) ≤ ρ :=
      ⟨(SkewMonoidAlgebra.support s).sup fun h => rad (SkewMonoidAlgebra.coeff s h),
        fun h hh => Finset.le_sup (f := fun h => rad (SkewMonoidAlgebra.coeff s h)) hh⟩
    refine eventually_atTop.2 ⟨ρ + B, fun ℓ hℓ => ?_⟩
    have hℓz : ((ρ : ℕ) : ℤ) + (B : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
    exact Pestov91.periodicModel_mul (D ℓ) r s fun g hg h hh n =>
      hcovD ℓ ρ _ (hdep _ ρ (hρ h hh)) g (by have := hbd g hg; omega) n

/-- **The asymptotic models of the note** (tex 121–145), as a closed statement: for an infinite
minimal subshift `X` over a finite alphabet with shift `T`, every point `x ∈ X` and every ring `k`. -/
def PrintedAsymptoticModels : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (X : Set (ℤ → A)),
    IsClosed X → (∀ n : ℤ, Set.MapsTo (shift n) X X) → X.Infinite →
    (∀ C : Set (ℤ → A), IsClosed C → C ⊆ X → (∀ g : ℤ, Set.MapsTo (shift g) C C) →
      C = ∅ ∨ C = X) →
    ∀ (T : ↥X ≃ₜ ↥X), (∀ x : ↥X, (T x).1 = shift 1 x.1) →
    ∀ x ∈ X, ∀ (k : Type) [Ring k], AsymptoticModels X T x k

theorem printedAsymptoticModels : PrintedAsymptoticModels :=
  fun _ _ _ _ _ hXc hX hinf hmin T hT _ hx k _ =>
    exists_asymptoticModels hXc hX hinf hmin T hT hx k

end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_asymptoticModels
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedAsymptoticModels
