import GroupApproximation.GGT.PNaiveChain
import GroupApproximation.GGT.AcylindricalEllipticOrEscaping

/-!
# One transversality constant for every nontrivial element of a cyclic subgroup

Fifth module of property `P_naive` (Abbott--Dahmani, arXiv:1610.04143,
Proposition 1.3 and Theorem 2.2).  Let `h₀` have a strong local gap at `o`, and
let `f` be an element no nontrivial power of which lies in `E(h₀)`.  Put
`h = h₀ᴹ`.  The ping-pong of `GGT/PNaivePingPong.lean` needs, for every
nontrivial `g ∈ ⟨f⟩`, transversality of `g` against the two ends `h·o`,
`h⁻¹·o`.  `GGT/PNaiveTransversal.lean` derives it from one of two regimes:

* **bounded** — `d(o, g·o) ≤ E` and `(g·z | z')_o ≤ D` for the ends `z, z'`;
* **far** — `d(o, g·o) > 2(I + δ)`, and `g·o`, `g⁻¹·o` are transverse to the
  ends with constant `I`.

`exists_uniform_regimes` produces `E`, `D`, `I` and a threshold `M₀`, the same
for every nontrivial `g ∈ ⟨f⟩` and every `M ≥ M₀`.  The action is isometric,
four-point hyperbolic and acylindrical, and independence of loxodromic elements
without common powers is taken as the hypothesis
`Elementary.IndependentOfNoCommonZpow`, which the repository proves on Hull's
Cayley graph (`ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic`).

## The two cases

* `f` **elliptic** (bounded orbit, constant `E`).  There are infinitely many `g`,
  all moving `o` by at most `E`.  Fix a vertex `pᵢ = h₀ⁱ·o` at acylindricity's
  radius.  If some product `(g·z | z')_o` reaches `r = d(o, pᵢ)`, fellow
  travelling (`dist_smul_le_of_fellow`) puts `g` in one of four sets of elements
  that move `o` little and carry `pᵢ` or `qᵢ = h₀⁻ⁱ·o` near `pᵢ` or `qᵢ`; all four
  are finite by acylindricity (`finite_of_carry`).  Outside them `D = r`; on them
  the constant comes from independence of `g h₀ g⁻¹` and `h₀`, since `g ∉ E(h₀)`.
* `f` **loxodromic**.  Independence of `f` and `h₀` gives `I`.  Only finitely
  many powers of `f` move `o` by at most `2(I+δ)`, and those are in the bounded
  regime by conjugate independence again.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` through property `P_naive`;
certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace PNaive

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## Conjugate independence -/

/-- **Products of a translated power orbit, from conjugate independence.** -/
theorem gromovProduct_smul_zpow_le {h₀ g : G} {o : X} (hiso : IsIsometricAction G X)
    {Cg : ℝ} (hCg : ∀ n m : ℤ,
      gromovProduct (((g * h₀ * g⁻¹) ^ n) • o) ((h₀ ^ m) • o) o ≤ Cg) (n m : ℤ) :
    gromovProduct (g • (h₀ ^ n) • o) ((h₀ ^ m) • o) o ≤ Cg + dist o (g • o) := by
  have hmove : dist (g • (h₀ ^ n) • o) (((g * h₀ * g⁻¹) ^ n) • o) = dist o (g • o) := by
    rw [conj_zpow, smul_smul, mul_smul (g * h₀ ^ n) g⁻¹ o, hiso (g * h₀ ^ n) o (g⁻¹ • o),
      dist_inv_smul hiso]
  have hle := gromovProduct_le_add_dist_left (g • (h₀ ^ n) • o) (((g * h₀ * g⁻¹) ^ n) • o)
    ((h₀ ^ m) • o) o
  rw [hmove] at hle
  linarith [hCg n m]

/-- **A conjugate by an element outside `E(h₀)` is independent of `h₀`.** -/
theorem independent_conj_of_notMem {h₀ g : G} {o : X} (hiso : IsIsometricAction G X)
    (hind : Elementary.IndependentOfNoCommonZpow G o) (hlox : IsLoxodromic h₀ o)
    (hg : g ∉ Elementary.elementaryClosure h₀) : Independent (g * h₀ * g⁻¹) h₀ o := by
  refine hind _ _ (isLoxodromic_conj hiso hlox) hlox ?_
  intro p q hp hq heq
  apply hg
  refine Elementary.mem_elementaryClosure.mpr ⟨p, q, hp, hq, ?_⟩
  rw [← conj_zpow]
  exact heq

/-! ## Distances of negative powers -/

theorem dist_zpow_neg_smul (hiso : IsIsometricAction G X) (f : G) (o : X) (k : ℕ) :
    dist o ((f ^ (-(k : ℤ))) • o) = dist o ((f ^ k) • o) := by
  rw [zpow_neg, zpow_natCast]
  exact dist_inv_smul hiso (f ^ k) o

/-- **Only finitely many powers of a loxodromic element move the basepoint
boundedly.** -/
theorem finite_setOf_dist_zpow_le {f : G} {o : X} (hiso : IsIsometricAction G X)
    (hlox : IsLoxodromic f o) (T : ℝ) :
    {a : ℤ | dist o ((f ^ a) • o) ≤ T}.Finite := by
  obtain ⟨l, hl, B, _hB, hlin⟩ := hlox
  obtain ⟨K, hK⟩ := exists_nat_gt ((T + B) / l)
  refine (Set.finite_Icc (-(K : ℤ)) K).subset ?_
  intro a ha
  have ha' : dist o ((f ^ a) • o) ≤ T := ha
  have hnat : l * (a.natAbs : ℝ) - B ≤ dist o ((f ^ a) • o) := by
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg a
    · simpa using hlin k
    · simpa [dist_zpow_neg_smul hiso f o k] using hlin k
  have hbound : (a.natAbs : ℝ) < K := by
    rw [div_lt_iff₀ hl] at hK
    have hmul : l * (a.natAbs : ℝ) < l * (K : ℝ) := by linarith
    exact lt_of_mul_lt_mul_left hmul hl.le
  have hbound' : a.natAbs < K := by exact_mod_cast hbound
  constructor <;> omega

/-! ## The uniform regimes -/

/-- **One set of constants for every nontrivial element of `⟨f⟩`.** -/
theorem exists_uniform_regimes {δ C₀ : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {o : X}
    (hind : Elementary.IndependentOfNoCommonZpow G o) {h₀ f : G}
    (hloc : gromovProduct (h₀ • o) (h₀⁻¹ • o) o ≤ C₀) (hC₀ : 0 ≤ C₀)
    (hgap : 2 * (C₀ + 2 * δ) < dist o (h₀ • o))
    (hf : IsElliptic f o ∨ IsLoxodromic f o)
    (hnot : ∀ g ∈ Subgroup.zpowers f, g ≠ 1 → g ∉ Elementary.elementaryClosure h₀) :
    ∃ (E D I : ℝ) (M₀ : ℕ), 0 ≤ E ∧ 0 ≤ D ∧ 0 ≤ I ∧ ∀ M : ℕ, M₀ ≤ M →
      ∀ g ∈ Subgroup.zpowers f, g ≠ 1 →
        (dist o (g • o) ≤ E ∧
          ∀ z ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set X),
            ∀ z' ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set X),
              gromovProduct (g • z) z' o ≤ D) ∨
        (2 * (I + δ) < dist o (g • o) ∧
          ∀ z ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set X),
            gromovProduct z (g⁻¹ • o) o ≤ I ∧ gromovProduct (g • o) z o ≤ I) := by
  classical
  have hlox₀ : IsLoxodromic h₀ o :=
    isLoxodromic_of_local_gap hδ hiso (by linarith) hloc (by linarith)
  -- conjugate independence constants
  have hconj : ∀ g : G, g ∈ Subgroup.zpowers f ∧ g ≠ 1 → ∃ Cg : ℝ, ∀ n m : ℤ,
      gromovProduct (((g * h₀ * g⁻¹) ^ n) • o) ((h₀ ^ m) • o) o ≤ Cg := by
    rintro g ⟨hg, hg1⟩
    exact independent_conj_of_notMem hiso hind hlox₀ (hnot g hg hg1)
  choose! Cg hCg using hconj
  -- the ends of `h₀ᴹ` as integer powers
  have hends : ∀ M : ℕ, ∀ z ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set X),
      ∃ n : ℤ, z = (h₀ ^ n) • o := by
    intro M z hz
    rcases hz with rfl | hz
    · exact ⟨M, by rw [zpow_natCast]⟩
    · rw [Set.mem_singleton_iff] at hz
      exact ⟨-(M : ℤ), by rw [hz, zpow_neg, zpow_natCast]⟩
  have hboundedC : ∀ g : G, g ∈ Subgroup.zpowers f ∧ g ≠ 1 → ∀ M : ℕ,
      ∀ z ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set X),
        ∀ z' ∈ ({(h₀ ^ M) • o, (h₀ ^ M)⁻¹ • o} : Set X),
          gromovProduct (g • z) z' o ≤ max (Cg g) 0 + dist o (g • o) := by
    intro g hg M z hz z' hz'
    obtain ⟨n, rfl⟩ := hends M z hz
    obtain ⟨m, rfl⟩ := hends M z' hz'
    have := gromovProduct_smul_zpow_le hiso (hCg g hg) n m
    linarith [le_max_left (Cg g) 0]
  rcases hf with ⟨Ef, hEf⟩ | hflox
  · ------------------------------------------------------------ elliptic `f`
    set E : ℝ := max Ef 0 with hEdef
    have hE0 : 0 ≤ E := le_max_right Ef 0
    have hgE : ∀ g ∈ Subgroup.zpowers f, dist o (g • o) ≤ E := by
      intro g hg
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact le_trans (hEf a) (le_max_left Ef 0)
    set ε' : ℝ := 2 * C₀ + 8 * δ + 3 * E with hε'def
    have hε'0 : 0 ≤ ε' := by rw [hε'def]; linarith
    set ε₂ : ℝ := 2 * max E ε' + 1 with hε₂def
    have hε₂ : 0 < ε₂ := by
      rw [hε₂def]
      have : 0 ≤ max E ε' := le_trans hE0 (le_max_left E ε')
      linarith
    obtain ⟨R, Nb, hRN⟩ := hacy ε₂ hε₂
    -- a vertex at acylindricity's radius
    have hκ : 0 < dist o (h₀ • o) - 2 * (C₀ + δ) := by linarith
    obtain ⟨i₀, hi₀⟩ := exists_nat_gt (max R 0 / (dist o (h₀ • o) - 2 * (C₀ + δ)))
    set i : ℕ := i₀ + 1 with hidef
    have hi1 : 1 ≤ i := by omega
    have hprog := le_dist_pow_smul hδ hδ0 hiso hloc hC₀ hgap i
    have hRi : R ≤ dist o ((h₀ ^ i) • o) := by
      have h1 : max R 0 < (dist o (h₀ • o) - 2 * (C₀ + δ)) * (i₀ : ℝ) := by
        rw [div_lt_iff₀ hκ] at hi₀
        linarith
      have h2 : (dist o (h₀ • o) - 2 * (C₀ + δ)) * (i₀ : ℝ) ≤
          (dist o (h₀ • o) - 2 * (C₀ + δ)) * (i : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hκ.le
        rw [hidef]
        push_cast
        linarith
      linarith [le_max_left R 0]
    set r : ℝ := dist o ((h₀ ^ i) • o) with hrdef
    have hrq : dist o ((h₀ ^ i)⁻¹ • o) = r := dist_inv_smul hiso (h₀ ^ i) o
    -- the finite exceptional sets
    have hS₀p := (hRN o ((h₀ ^ i) • o) hRi).1
    have hS₀q := (hRN o ((h₀ ^ i)⁻¹ • o) (by rw [hrq]; exact hRi)).1
    have hmaxle : 2 * max E ε' ≤ ε₂ := by rw [hε₂def]; linarith
    have hS₀p' : {s : G | dist o (s • o) ≤ 2 * max E ε' ∧
        dist ((h₀ ^ i) • o) (s • (h₀ ^ i) • o) ≤ 2 * max E ε'}.Finite :=
      hS₀p.subset fun s hs => ⟨le_trans hs.1 hmaxle, le_trans hs.2 hmaxle⟩
    have hS₀q' : {s : G | dist o (s • o) ≤ 2 * max E ε' ∧
        dist ((h₀ ^ i)⁻¹ • o) (s • (h₀ ^ i)⁻¹ • o) ≤ 2 * max E ε'}.Finite :=
      hS₀q.subset fun s hs => ⟨le_trans hs.1 hmaxle, le_trans hs.2 hmaxle⟩
    have hEmax : E ≤ ε₂ := by
      rw [hε₂def]; linarith [le_max_left E ε', le_max_right E ε']
    have hε'max : ε' ≤ ε₂ := by
      rw [hε₂def]; linarith [le_max_left E ε', le_max_right E ε']
    have hSpp : {g : G | dist o (g • o) ≤ E ∧
        dist ((h₀ ^ i) • o) (g • (h₀ ^ i) • o) ≤ ε'}.Finite :=
      hS₀p.subset fun s hs => ⟨le_trans hs.1 hEmax, le_trans hs.2 hε'max⟩
    have hSqq : {g : G | dist o (g • o) ≤ E ∧
        dist ((h₀ ^ i)⁻¹ • o) (g • (h₀ ^ i)⁻¹ • o) ≤ ε'}.Finite :=
      hS₀q.subset fun s hs => ⟨le_trans hs.1 hEmax, le_trans hs.2 hε'max⟩
    have hSpq : {g : G | dist o (g • o) ≤ E ∧
        dist ((h₀ ^ i)⁻¹ • o) (g • (h₀ ^ i) • o) ≤ ε'}.Finite :=
      finite_of_carry hiso hS₀p'
    have hSqp : {g : G | dist o (g • o) ≤ E ∧
        dist ((h₀ ^ i) • o) (g • (h₀ ^ i)⁻¹ • o) ≤ ε'}.Finite :=
      finite_of_carry hiso hS₀q'
    set S : Set G := {g : G | dist o (g • o) ≤ E ∧
        dist ((h₀ ^ i) • o) (g • (h₀ ^ i) • o) ≤ ε'} ∪
      {g : G | dist o (g • o) ≤ E ∧
        dist ((h₀ ^ i)⁻¹ • o) (g • (h₀ ^ i)⁻¹ • o) ≤ ε'} ∪
      {g : G | dist o (g • o) ≤ E ∧
        dist ((h₀ ^ i)⁻¹ • o) (g • (h₀ ^ i) • o) ≤ ε'} ∪
      {g : G | dist o (g • o) ≤ E ∧
        dist ((h₀ ^ i) • o) (g • (h₀ ^ i)⁻¹ • o) ≤ ε'} with hSdef
    have hSfin : S.Finite := ((hSpp.union hSqq).union hSpq).union hSqp
    let ψ : G → ℝ := fun g =>
      if g ∈ Subgroup.zpowers f ∧ g ≠ 1 then max (Cg g) 0 + E else 0
    have hψ0 : ∀ g, 0 ≤ ψ g := by
      intro g
      simp only [ψ]
      split_ifs
      · linarith [le_max_right (Cg g) 0]
      · exact le_refl 0
    set Dexc : ℝ := ∑ g ∈ hSfin.toFinset, ψ g with hDexc
    refine ⟨E, max r Dexc, 0, i + 1, hE0, le_trans dist_nonneg (le_max_left _ _),
      le_refl 0, ?_⟩
    intro M hM g hg hg1
    refine Or.inl ⟨hgE g hg, ?_⟩
    by_cases hgS : g ∈ S
    · intro z hz z' hz'
      have hb := hboundedC g ⟨hg, hg1⟩ M z hz z' hz'
      have hψg : ψ g = max (Cg g) 0 + E := by simp only [ψ, if_pos (And.intro hg hg1)]
      have hsingle : ψ g ≤ Dexc :=
        Finset.single_le_sum (fun s _ => hψ0 s) (hSfin.mem_toFinset.mpr hgS)
      have hdo := hgE g hg
      linarith [le_max_right r Dexc]
    · -- outside the exceptional sets every product stays below `r`
      have hM1 : i < M := by omega
      have hCδ : 0 ≤ C₀ + 2 * δ := by linarith
      have hEg := hgE g hg
      -- the q-chain data from `h₀⁻¹`
      have hloc' : gromovProduct (h₀⁻¹ • o) (h₀⁻¹⁻¹ • o) o ≤ C₀ := by
        rw [gromovProduct_inv_turn]; exact hloc
      have hgap' : 2 * (C₀ + 2 * δ) < dist o (h₀⁻¹ • o) := by
        rw [dist_inv_smul hiso]; exact hgap
      have hbp : r - (C₀ + 2 * δ) ≤ gromovProduct ((h₀ ^ i) • o) ((h₀ ^ M) • o) o :=
        le_gromovProduct_pow_pow hδ hδ0 hiso hloc hC₀ hgap hi1 hM1
      have hbq : r - (C₀ + 2 * δ) ≤
          gromovProduct ((h₀ ^ i)⁻¹ • o) ((h₀ ^ M)⁻¹ • o) o := by
        have key := le_gromovProduct_pow_pow hδ hδ0 hiso hloc' hC₀ hgap' hi1 hM1
        rw [inv_pow, inv_pow, dist_inv_smul hiso] at key
        exact key
      intro z hz z' hz'
      by_contra hlarge
      have hT : r ≤ gromovProduct (g • z) z' o :=
        le_trans (le_max_left r Dexc) (not_le.mp hlarge).le
      have hrp : dist o ((h₀ ^ i) • o) = r := rfl
      apply hgS
      rcases hz with rfl | hz <;> rcases hz' with rfl | hz'
      · -- z = p, z' = p
        refine Or.inl (Or.inl (Or.inl ⟨hEg, ?_⟩))
        exact dist_smul_le_of_fellow hδ hiso (a := (h₀ ^ i) • o) (a' := (h₀ ^ M) • o)
          (b := (h₀ ^ i) • o) (c := (h₀ ^ M) • o) hEg hrp hrp hbp hbp hT hCδ hδ0
      · rw [Set.mem_singleton_iff] at hz'
        subst hz'
        refine Or.inl (Or.inr ⟨hEg, ?_⟩)
        exact dist_smul_le_of_fellow hδ hiso (a := (h₀ ^ i) • o) (a' := (h₀ ^ M) • o)
          (b := (h₀ ^ i)⁻¹ • o) (c := (h₀ ^ M)⁻¹ • o) hEg hrp hrq hbq hbp hT hCδ hδ0
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        refine Or.inr ⟨hEg, ?_⟩
        exact dist_smul_le_of_fellow hδ hiso (a := (h₀ ^ i)⁻¹ • o) (a' := (h₀ ^ M)⁻¹ • o)
          (b := (h₀ ^ i) • o) (c := (h₀ ^ M) • o) hEg hrq hrp hbp hbq hT hCδ hδ0
      · rw [Set.mem_singleton_iff] at hz hz'
        subst hz
        subst hz'
        refine Or.inl (Or.inl (Or.inr ⟨hEg, ?_⟩))
        exact dist_smul_le_of_fellow hδ hiso (a := (h₀ ^ i)⁻¹ • o) (a' := (h₀ ^ M)⁻¹ • o)
          (b := (h₀ ^ i)⁻¹ • o) (c := (h₀ ^ M)⁻¹ • o) hEg hrq hrq hbq hbq hT hCδ hδ0
  · ------------------------------------------------------------ loxodromic `f`
    have hinf : ¬ IsOfFinOrder f := not_isOfFinOrder_of_isLoxodromic hflox
    have hinj : Function.Injective (fun n : ℤ => f ^ n) :=
      injective_zpow_iff_not_isOfFinOrder.mpr hinf
    have hindf : Independent f h₀ o := by
      refine hind f h₀ hflox hlox₀ ?_
      intro p q hp hq heq
      have hne1 : f ^ p ≠ 1 := by
        intro h1
        exact hp (hinj (by simpa using h1))
      refine hnot (f ^ p) (Subgroup.zpow_mem_zpowers f p) hne1 ?_
      rw [heq]
      exact Subgroup.zpow_mem _ (Elementary.self_mem_elementaryClosure h₀) q
    obtain ⟨I₀, hI₀⟩ := hindf
    set I : ℝ := max I₀ 0 with hIdef
    have hI0 : 0 ≤ I := le_max_right I₀ 0
    have hAfin := finite_setOf_dist_zpow_le hiso hflox (2 * (I + δ))
    have hNfin := hAfin.image fun a : ℤ => f ^ a
    let ψ : G → ℝ := fun g =>
      if g ∈ Subgroup.zpowers f ∧ g ≠ 1 then max (Cg g) 0 + 2 * (I + δ) else 0
    have hψ0 : ∀ g, 0 ≤ ψ g := by
      intro g
      simp only [ψ]
      split_ifs
      · linarith [le_max_right (Cg g) 0]
      · exact le_refl 0
    set Dnear : ℝ := ∑ g ∈ hNfin.toFinset, ψ g with hDnear
    have hDnear0 : 0 ≤ Dnear := Finset.sum_nonneg fun g _ => hψ0 g
    refine ⟨2 * (I + δ), Dnear, I, 0, by linarith, hDnear0, hI0, ?_⟩
    intro M _hM g hg hg1
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    by_cases hnear : dist o ((f ^ a) • o) ≤ 2 * (I + δ)
    · refine Or.inl ⟨hnear, ?_⟩
      intro z hz z' hz'
      have hb := hboundedC (f ^ a) ⟨hg, hg1⟩ M z hz z' hz'
      have hmem : f ^ a ∈ hNfin.toFinset := hNfin.mem_toFinset.mpr ⟨a, hnear, rfl⟩
      have hψg : ψ (f ^ a) = max (Cg (f ^ a)) 0 + 2 * (I + δ) := by
        simp only [ψ, if_pos (And.intro hg hg1)]
      have hsingle : ψ (f ^ a) ≤ Dnear := Finset.single_le_sum (fun s _ => hψ0 s) hmem
      linarith
    · refine Or.inr ⟨lt_of_not_ge hnear, ?_⟩
      intro z hz
      obtain ⟨n, rfl⟩ := hends M z hz
      constructor
      · rw [gromovProduct_comm, ← zpow_neg]
        exact le_trans (hI₀ (-a) n) (le_max_left I₀ 0)
      · exact le_trans (hI₀ a n) (le_max_left I₀ 0)

end PNaive
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.PNaive.gromovProduct_smul_zpow_le
#audit_axioms GroupApproximation.GGT.PNaive.independent_conj_of_notMem
#audit_axioms GroupApproximation.GGT.PNaive.finite_setOf_dist_zpow_le
#audit_axioms GroupApproximation.GGT.PNaive.exists_uniform_regimes
