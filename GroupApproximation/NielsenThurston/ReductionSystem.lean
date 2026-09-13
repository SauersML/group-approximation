import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.OrderOfElement

/-!
# Canonical reduction systems over an abstract curve system

Chen–Salter (arXiv:1804.11235v1, §2.1) apply canonical reduction systems of mapping classes
through their Propositions 2.2–2.4. This file proves those properties for any action of a group
`G` on a type `C` with a crossing relation. In the intended instance:
- `G` is a mapping class group;
- `C` is the set of isotopy classes of essential nonperipheral simple closed curves;
- `cross c d` means that the geometric intersection number `i(c, d)` is nonzero.

The only geometric input is that pairwise non-crossing sets of curves are finite.

## The definition used
We use Ivanov's characterization of the canonical reduction system:
- **Ivanov's version.** `c ∈ CRS(f)` iff some positive power of `f` fixes `c`, and no positive
  power of `f` fixes a curve crossing `c`.
- **Sources.** N. V. Ivanov, *Subgroups of Teichmüller Modular Groups*, Transl. Math. Monographs
  115 (1992), Ch. 7; Farb–Margalit, *A Primer on Mapping Class Groups*, §13.2.
- **The other version.** Birman–Lubotzky–McCarthy define CRS(f) as the intersection of all
  maximal reduction systems (Chen–Salter, Definition 2.1). Their equality is Ivanov's theorem.
  It is neither used nor claimed here.

Chen–Salter's definition of pseudo-Anosov is recorded as `IsPseudoAnosov`: infinite order, and
no positive power fixes a curve.

## Main results
* `CurveSystem.crs_pow`, `CurveSystem.crs_inv`, `CurveSystem.crs_zpow`: Chen–Salter
  Proposition 2.2, `CRS(f ^ n) = CRS(f)` for `n ≠ 0`.
* `CurveSystem.smul_mem_crs_conj_iff`: `CRS(g f g⁻¹) = g · CRS(f)`.
* `CurveSystem.not_periodicCurve_of_mem_crs_of_cross`: Chen–Salter Proposition 2.3.
* `CurveSystem.crs_finite`, `CurveSystem.crs_pairwise`: `CRS(f)` is a finite multicurve.
* `CurveSystem.periodicCurve_of_commute_of_mem_crs`,
  `CurveSystem.exists_pow_fix_crs_of_commute`: an element commuting with `f` permutes `CRS(f)`,
  and a positive power of it fixes every curve of `CRS(f)`.
* `CurveSystem.not_cross_of_commute`: Chen–Salter Proposition 2.4.
-/

namespace GroupApproximation
namespace NielsenThurston

/-- **An abstract curve system**: a type `C` of curves with a `G`-action and a crossing relation.
- `cross` is symmetric and `G`-invariant;
- every set of pairwise non-crossing curves is finite.

In the intended instance `cross c d` is `i(c, d) ≠ 0`, and the finiteness bound is `3g − 3 + n`
for a surface of genus `g` with `n` punctures (Farb–Margalit, §8.3.1). -/
structure CurveSystem (G C : Type*) [Group G] [MulAction G C] where
  /-- `cross c d`: the curves `c` and `d` have nonzero geometric intersection number. -/
  cross : C → C → Prop
  /-- Crossing is symmetric. -/
  cross_symm : ∀ c d, cross c d → cross d c
  /-- Crossing is invariant under the action. -/
  cross_smul : ∀ (g : G) (c d : C), cross (g • c) (g • d) ↔ cross c d
  /-- Pairwise non-crossing sets of curves are finite. -/
  finite_of_pairwise : ∀ s : Set C, s.Pairwise (fun a b => ¬ cross a b) → s.Finite

variable {G C : Type*} [Group G] [MulAction G C]

/-- A fixed point of `g` is fixed by every power of `g`. -/
theorem pow_smul_eq_of_smul_eq {g : G} {c : C} (h : g • c = c) (n : ℕ) : g ^ n • c = c :=
  MulAction.mem_stabilizer_iff.mp (pow_mem (MulAction.mem_stabilizer_iff.mpr h) n)

/-- **Periodic curve**: some positive power of `f` fixes `c`. In Chen–Salter's terms, `f` is
reducible along `c`. -/
def PeriodicCurve (f : G) (c : C) : Prop :=
  ∃ m : ℕ, 0 < m ∧ f ^ m • c = c

namespace PeriodicCurve

/-- A curve is periodic for `f ^ n` (`n > 0`) iff it is periodic for `f`. -/
theorem pow_iff {f : G} {c : C} {n : ℕ} (hn : 0 < n) :
    PeriodicCurve (f ^ n) c ↔ PeriodicCurve f c := by
  constructor
  · rintro ⟨m, hm, h⟩
    exact ⟨n * m, Nat.mul_pos hn hm, by rwa [pow_mul]⟩
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    rw [← pow_mul, pow_mul']
    exact pow_smul_eq_of_smul_eq h n

/-- A curve is periodic for `f⁻¹` iff it is periodic for `f`. -/
theorem inv_iff {f : G} {c : C} : PeriodicCurve f⁻¹ c ↔ PeriodicCurve f c := by
  constructor
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    rw [inv_pow] at h
    exact (inv_smul_eq_iff.mp h).symm
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    rw [inv_pow]
    exact inv_smul_eq_iff.mpr h.symm

/-- A curve is periodic for `f ^ n` (`n ≠ 0`) iff it is periodic for `f`. -/
theorem zpow_iff {f : G} {c : C} {n : ℤ} (hn : n ≠ 0) :
    PeriodicCurve (f ^ n) c ↔ PeriodicCurve f c := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast]
    exact PeriodicCurve.pow_iff (by omega)
  · rw [zpow_neg, zpow_natCast, PeriodicCurve.inv_iff]
    exact PeriodicCurve.pow_iff (by omega)

/-- `g • c` is periodic for `g f g⁻¹` iff `c` is periodic for `f`. -/
theorem conj_smul_iff {f : G} {c : C} (g : G) :
    PeriodicCurve (g * f * g⁻¹) (g • c) ↔ PeriodicCurve f c := by
  have key : ∀ m : ℕ, (g * f * g⁻¹) ^ m • (g • c) = g • c ↔ f ^ m • c = c := by
    intro m
    rw [conj_pow, mul_smul, mul_smul, inv_smul_smul, smul_left_cancel_iff]
  show (∃ m : ℕ, 0 < m ∧ (g * f * g⁻¹) ^ m • (g • c) = g • c) ↔
    ∃ m : ℕ, 0 < m ∧ f ^ m • c = c
  exact exists_congr fun m => and_congr_right fun _ => key m

end PeriodicCurve

variable (C) in
/-- **Pseudo-Anosov** in Chen–Salter's sense (arXiv:1804.11235v1, §2.1): neither periodic
(`f` has infinite order) nor reducible (no positive power of `f` fixes a curve). -/
def IsPseudoAnosov (f : G) : Prop :=
  ¬ IsOfFinOrder f ∧ ∀ c : C, ¬ PeriodicCurve f c

namespace CurveSystem

variable (S : CurveSystem G C)

/-- **The canonical reduction system** `CRS(f)`, by Ivanov's characterization: the curves fixed
by some positive power of `f` such that no curve crossing them is fixed by a positive power
of `f`. -/
def crs (f : G) : Set C :=
  {c | PeriodicCurve f c ∧ ∀ d, S.cross c d → ¬ PeriodicCurve f d}

theorem mem_crs {f : G} {c : C} :
    c ∈ S.crs f ↔ PeriodicCurve f c ∧ ∀ d, S.cross c d → ¬ PeriodicCurve f d :=
  Iff.rfl

/-- **Chen–Salter Proposition 2.2**, for positive powers: `CRS(f ^ n) = CRS(f)`. -/
theorem crs_pow {f : G} {n : ℕ} (hn : 0 < n) : S.crs (f ^ n) = S.crs f := by
  ext c
  simp only [mem_crs, PeriodicCurve.pow_iff hn]

/-- `CRS(f⁻¹) = CRS(f)`. -/
theorem crs_inv (f : G) : S.crs f⁻¹ = S.crs f := by
  ext c
  simp only [mem_crs, PeriodicCurve.inv_iff]

/-- **Chen–Salter Proposition 2.2**: `CRS(f ^ n) = CRS(f)` for `n ≠ 0`. -/
theorem crs_zpow {f : G} {n : ℤ} (hn : n ≠ 0) : S.crs (f ^ n) = S.crs f := by
  ext c
  simp only [mem_crs, PeriodicCurve.zpow_iff hn]

/-- **Chen–Salter Proposition 2.3**: a curve crossing a curve of `CRS(f)` is fixed by no
positive power of `f`. -/
theorem not_periodicCurve_of_mem_crs_of_cross {f : G} {c d : C} (hc : c ∈ S.crs f)
    (hcd : S.cross c d) : ¬ PeriodicCurve f d :=
  (S.mem_crs.mp hc).2 d hcd

/-- The curves of `CRS(f)` are pairwise non-crossing. -/
theorem crs_pairwise (f : G) : (S.crs f).Pairwise (fun a b => ¬ S.cross a b) := by
  intro a ha b hb _ hab
  exact (S.mem_crs.mp ha).2 b hab (S.mem_crs.mp hb).1

/-- `CRS(f)` is finite. -/
theorem crs_finite (f : G) : (S.crs f).Finite :=
  S.finite_of_pairwise _ (S.crs_pairwise f)

/-- **Equivariance**: `g • c ∈ CRS(g f g⁻¹)` iff `c ∈ CRS(f)`. -/
theorem smul_mem_crs_conj_iff {f : G} {c : C} (g : G) :
    g • c ∈ S.crs (g * f * g⁻¹) ↔ c ∈ S.crs f := by
  rw [mem_crs, mem_crs]
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨(PeriodicCurve.conj_smul_iff g).mp hp, fun d hcd hpd => ?_⟩
    exact hd (g • d) ((S.cross_smul g c d).mpr hcd) ((PeriodicCurve.conj_smul_iff g).mpr hpd)
  · rintro ⟨hp, hd⟩
    refine ⟨(PeriodicCurve.conj_smul_iff g).mpr hp, fun d hcd hpd => ?_⟩
    have hd' : S.cross c (g⁻¹ • d) := by
      rw [← S.cross_smul g, smul_inv_smul]
      exact hcd
    have hpd' : PeriodicCurve f (g⁻¹ • d) := by
      rw [← PeriodicCurve.conj_smul_iff g, smul_inv_smul]
      exact hpd
    exact hd (g⁻¹ • d) hd' hpd'

/-- An element commuting with `f` maps `CRS(f)` into itself. -/
theorem smul_mem_crs_of_commute {h f : G} (hhf : Commute h f) {c : C} (hc : c ∈ S.crs f) :
    h • c ∈ S.crs f := by
  have e : h * f * h⁻¹ = f := by rw [hhf.eq, mul_inv_cancel_right]
  have hc' := (S.smul_mem_crs_conj_iff (f := f) (c := c) h).mpr hc
  rwa [e] at hc'

/-- Powers of an element commuting with `f` map `CRS(f)` into itself. -/
theorem pow_smul_mem_crs_of_commute {h f : G} (hhf : Commute h f) {c : C} (hc : c ∈ S.crs f)
    (n : ℕ) : h ^ n • c ∈ S.crs f := by
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    rw [pow_succ', mul_smul]
    exact S.smul_mem_crs_of_commute hhf ih

/-- **Commuting elements permute the CRS.** If `h` commutes with `f`, some positive power of `h`
fixes each curve of `CRS(f)`: its `⟨h⟩`-orbit lies in the finite set `CRS(f)`. -/
theorem periodicCurve_of_commute_of_mem_crs {h f : G} (hhf : Commute h f) {c : C}
    (hc : c ∈ S.crs f) : PeriodicCurve h c := by
  haveI : Finite (S.crs f) := (S.crs_finite f).to_subtype
  obtain ⟨p, q, hpq, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨h ^ n • c, S.pow_smul_mem_crs_of_commute hhf hc n⟩ : S.crs f))
  have he' : h ^ p • c = h ^ q • c := congrArg Subtype.val he
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · refine ⟨q - p, by omega, ?_⟩
    have hq : h ^ q = h ^ p * h ^ (q - p) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hq, mul_smul] at he'
    exact ((smul_left_cancel_iff _).mp he').symm
  · refine ⟨p - q, by omega, ?_⟩
    have hp : h ^ p = h ^ q * h ^ (p - q) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp, mul_smul] at he'
    exact (smul_left_cancel_iff _).mp he'

/-- Finitely many periodic curves share a common positive period. -/
theorem exists_pow_smul_eq_of_forall_mem {f : G} (s : Finset C)
    (hs : ∀ c ∈ s, PeriodicCurve f c) : ∃ m : ℕ, 0 < m ∧ ∀ c ∈ s, f ^ m • c = c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Nat.one_pos, fun c hc => by simp at hc⟩
  | insert a s _ ih =>
    obtain ⟨m₁, hm₁, h₁⟩ := ih (fun c hc => hs c (Finset.mem_insert_of_mem hc))
    obtain ⟨m₂, hm₂, h₂⟩ := hs a (Finset.mem_insert_self a s)
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun c hc => ?_⟩
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rw [pow_mul']
      exact pow_smul_eq_of_smul_eq h₂ m₁
    · rw [pow_mul]
      exact pow_smul_eq_of_smul_eq (h₁ c hc) m₂

/-- **A common power fixes the CRS.** If `h` commutes with `f`, a positive power of `h` fixes
every curve of `CRS(f)`. -/
theorem exists_pow_fix_crs_of_commute {h f : G} (hhf : Commute h f) :
    ∃ m : ℕ, 0 < m ∧ ∀ c ∈ S.crs f, h ^ m • c = c := by
  obtain ⟨m, hm, hfix⟩ := exists_pow_smul_eq_of_forall_mem (S.crs_finite f).toFinset
    (fun c hc => S.periodicCurve_of_commute_of_mem_crs hhf ((S.crs_finite f).mem_toFinset.mp hc))
  exact ⟨m, hm, fun c hc => hfix c ((S.crs_finite f).mem_toFinset.mpr hc)⟩

/-- **Chen–Salter Proposition 2.4**: commuting elements have non-crossing canonical reduction
systems. -/
theorem not_cross_of_commute {h f : G} (hhf : Commute h f) {c d : C} (hc : c ∈ S.crs h)
    (hd : d ∈ S.crs f) : ¬ S.cross c d := fun hcd =>
  S.not_periodicCurve_of_mem_crs_of_cross hc hcd (S.periodicCurve_of_commute_of_mem_crs hhf hd)

/-- A pseudo-Anosov element has empty canonical reduction system. -/
theorem crs_eq_empty_of_isPseudoAnosov {f : G} (hf : IsPseudoAnosov C f) : S.crs f = ∅ :=
  Set.eq_empty_of_forall_notMem fun c hc => hf.2 c (S.mem_crs.mp hc).1

end CurveSystem

end NielsenThurston
end GroupApproximation
