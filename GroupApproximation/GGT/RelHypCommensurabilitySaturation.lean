import GroupApproximation.GGT.RelHypHyperbolicPairReduction
import GroupApproximation.GGT.HullSCUnionGeometryWitness

/-!
# Commensurability as conjugacy saturation of the elementary closure

For a torsion-free hyperbolic group, the conjugator in Osin's definition of
commensurability can be isolated completely.  If `g` is loxodromic and `h` is
nontrivial, then

    `OsinCommensurable g h`

is equivalent to saying that one conjugate of `h` lies in the subgroup-valued
elementary closure `E(g)`.

The forward implication is elementary: a commensurability equation makes a
power of the conjugate equal to a power of `g`.  The reverse implication is
the substantive direction, but all its geometry is already proved in
`HullSCUnionGeometryWitness`: over a finite hyperbolic Cayley alphabet, every
nontrivial member of `E(g)` shares a nonzero power with `g`.

This gives an exact reformulation of the Fournier--Facio pair residue.  The
remaining assertion is no longer a statement with two integer exponents and an
ambient conjugator: it says that the conjugacy saturation of one elementary
closure does not contain every nontrivial element.  No prescribed first axis is
needed, and torsion-freeness is retained exactly where the consumer supplies
it.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## 1.  Conjugacy saturation -/

/-- The union of all conjugates of a subgroup, expressed by conjugating the
element into the subgroup.  It is generally only a set, not a subgroup. -/
def ConjugacySaturation {G : Type*} [Group G] (K : Subgroup G) : Set G :=
  {h | ∃ c : G, c * h * c⁻¹ ∈ K}

theorem mem_conjugacySaturation_iff {G : Type*} [Group G]
    {K : Subgroup G} {h : G} :
    h ∈ ConjugacySaturation K ↔ ∃ c : G, c * h * c⁻¹ ∈ K := Iff.rfl

theorem one_mem_conjugacySaturation {G : Type*} [Group G] (K : Subgroup G) :
    (1 : G) ∈ ConjugacySaturation K := by
  exact ⟨1, by simp⟩

/-- Because every conjugacy saturation contains `1`, failure to cover the
group is exactly the existence of a nontrivial element outside it. -/
theorem exists_ne_one_notMem_conjugacySaturation_iff_ne_univ
    {G : Type*} [Group G] (K : Subgroup G) :
    (∃ h : G, h ≠ 1 ∧ h ∉ ConjugacySaturation K) ↔
      ConjugacySaturation K ≠ Set.univ := by
  constructor
  · rintro ⟨h, -, hh⟩ heq
    exact hh (by rw [heq]; exact Set.mem_univ h)
  · intro hproper
    by_contra hnone
    push Not at hnone
    apply hproper
    ext h
    constructor
    · intro _
      exact Set.mem_univ h
    · intro _
      by_cases hh : h = 1
      · subst h
        exact one_mem_conjugacySaturation K
      · exact hnone h hh

/-! ## 2.  Exact commensurability criterion -/

/-- A commensurability witness puts a conjugate of the second element in the
elementary closure of the first.  This direction is pure group theory. -/
theorem mem_conjugacySaturation_elementaryClosure_of_osinCommensurable
    {G : Type*} [Group G] {g h : G} (hcomm : OsinCommensurable g h) :
    h ∈ ConjugacySaturation (Elementary.elementaryClosure g) := by
  obtain ⟨k, l, c, hk, _hl, heq⟩ := hcomm
  refine ⟨c, Elementary.mem_elementaryClosure_of_common_zpow
    (q := l) hk ?_⟩
  calc
    g ^ k = c * h ^ l * c⁻¹ := by
      rw [← heq]
      group
    _ = (c * h * c⁻¹) ^ l := by
      exact Elementary.conj_zpow_eq c h l

/-- At a finite hyperbolic Cayley alphabet, a nontrivial element in the
conjugacy saturation of `E(g)` is Osin-commensurable with `g`.

The finite-Cayley common-power theorem is the only geometric ingredient. -/
theorem osinCommensurable_of_mem_conjugacySaturation_elementaryClosure
    {G : Type} [Group G] (A : Alphabet G) (hfin : A.carrier.Finite)
    {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A))
    (htf : IsPowerTorsionFree G) {g h : G}
    (hg : IsLoxodromic g (Cayley.base A)) (hh : h ≠ 1)
    (hmem : h ∈ ConjugacySaturation (Elementary.elementaryClosure g)) :
    OsinCommensurable g h := by
  obtain ⟨c, hc⟩ := hmem
  have hch : c * h * c⁻¹ ≠ 1 := by
    intro heq
    apply hh
    have : h = c⁻¹ * (c * h * c⁻¹) * c := by group
    rw [heq] at this
    simpa using this
  obtain ⟨i, m, hi, hm, hpow⟩ :=
    HullSCUnionGeometry.exists_common_zpow_of_mem_elementaryClosure_cayley
      A hfin hδ htf (not_isOfFinOrder_of_isLoxodromic hg) hc hch
  refine ⟨i, m, c, hi, hm, ?_⟩
  calc
    c⁻¹ * g ^ i * c = c⁻¹ * (c * h * c⁻¹) ^ m * c := by rw [hpow]
    _ = h ^ m := by
      rw [← Elementary.conj_zpow_eq c h m]
      group

/-- **Exact criterion.**  In the torsion-free finite-Cayley setting, `g` and a
nontrivial `h` are commensurable exactly when the conjugacy saturation of
`E(g)` contains `h`. -/
theorem osinCommensurable_iff_mem_conjugacySaturation_elementaryClosure
    {G : Type} [Group G] (A : Alphabet G) (hfin : A.carrier.Finite)
    {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A))
    (htf : IsPowerTorsionFree G) {g h : G}
    (hg : IsLoxodromic g (Cayley.base A)) (hh : h ≠ 1) :
    OsinCommensurable g h ↔
      h ∈ ConjugacySaturation (Elementary.elementaryClosure g) := by
  constructor
  · exact mem_conjugacySaturation_elementaryClosure_of_osinCommensurable
  · exact osinCommensurable_of_mem_conjugacySaturation_elementaryClosure
      A hfin hδ htf hg hh

/-- Negating the exact criterion: non-commensurability means that every
conjugate of `h` misses `E(g)`. -/
theorem not_osinCommensurable_iff_forall_conj_notMem_elementaryClosure
    {G : Type} [Group G] (A : Alphabet G) (hfin : A.carrier.Finite)
    {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A))
    (htf : IsPowerTorsionFree G) {g h : G}
    (hg : IsLoxodromic g (Cayley.base A)) (hh : h ≠ 1) :
    (¬ OsinCommensurable g h) ↔
      ∀ c : G, c * h * c⁻¹ ∉ Elementary.elementaryClosure g := by
  rw [osinCommensurable_iff_mem_conjugacySaturation_elementaryClosure
    A hfin hδ htf hg hh]
  simp only [ConjugacySaturation, Set.mem_setOf_eq, not_exists]

/-! ## 3.  The exact Fournier--Facio pair residue -/

/-- The pair residue with all power and order bookkeeping removed: some
nontrivial `h` has every conjugate outside the elementary closure of some
nontrivial `g`.

This is deliberately not prescribed-axis.  The manuscript asks for one pair,
and adding `∀ g` would strengthen its obligation. -/
def HyperbolicConjugacySaturationPairEscape : Prop :=
  ∀ (H : Type) (_ : Group H),
    IsNonElementaryHyperbolic H → IsPowerTorsionFree H →
      ∃ g h : H, g ≠ 1 ∧ h ≠ 1 ∧
        ∀ c : H, c * h * c⁻¹ ∉ Elementary.elementaryClosure g

/-- The final residue in set-theoretic form: at least one nontrivial
elementary closure has proper conjugacy saturation. -/
def HyperbolicElementaryClosureConjugacySaturationProper : Prop :=
  ∀ (H : Type) (_ : Group H),
    IsNonElementaryHyperbolic H → IsPowerTorsionFree H →
      ∃ g : H, g ≠ 1 ∧
        ConjugacySaturation (Elementary.elementaryClosure g) ≠ Set.univ

/-- Pair escape is exactly properness of one conjugacy saturation. -/
theorem hyperbolicConjugacySaturationPairEscape_iff_saturationProper :
    HyperbolicConjugacySaturationPairEscape ↔
      HyperbolicElementaryClosureConjugacySaturationProper := by
  constructor
  · intro hpair H instH hne htf
    obtain ⟨g, h, hg, hh, hescape⟩ := hpair H instH hne htf
    refine ⟨g, hg,
      (exists_ne_one_notMem_conjugacySaturation_iff_ne_univ
        (Elementary.elementaryClosure g)).mp ⟨h, hh, ?_⟩⟩
    simpa only [ConjugacySaturation, Set.mem_setOf_eq, not_exists] using hescape
  · intro hproper H instH hne htf
    obtain ⟨g, hg, hsat⟩ := hproper H instH hne htf
    obtain ⟨h, hh, hmem⟩ :=
      (exists_ne_one_notMem_conjugacySaturation_iff_ne_univ
        (Elementary.elementaryClosure g)).mpr hsat
    refine ⟨g, h, hg, hh, ?_⟩
    simpa only [ConjugacySaturation, Set.mem_setOf_eq, not_exists] using hmem

/-- The Fournier--Facio non-commensurable-pair residue is exactly conjugacy-
saturation escape. -/
theorem hyperbolicNonCommensurablePairStatement_iff_conjugacySaturationEscape :
    HyperbolicNonCommensurablePairStatement ↔
      HyperbolicConjugacySaturationPairEscape := by
  constructor
  · intro hpair H instH hne htf
    letI := instH
    obtain ⟨g, h, hgord, hhord, hnc⟩ := hpair H instH hne htf
    obtain ⟨T, hT, δ, hδ⟩ := hne.1
    let A : Alphabet H := ⟨(T : Set H), hT⟩
    have hAfin : A.carrier.Finite := T.finite_toSet
    have hAδ : IsHyperbolicSpace (δ : ℝ) (Cayley A) :=
      isHyperbolicSpace_cayley_of_fourPoint A hδ
    have hg1 : g ≠ 1 := by
      intro hg
      exact hgord 1 one_pos (by simp [hg])
    have hh1 : h ≠ 1 := by
      intro hh
      exact hhord 1 one_pos (by simp [hh])
    have hglox : IsLoxodromic g (Cayley.base A) :=
      HullSCUnionGeometry.isLoxodromic_cayley_of_not_isOfFinOrder
        A hAfin hAδ (htf.not_isOfFinOrder hg1)
    exact ⟨g, h, hg1, hh1,
      (not_osinCommensurable_iff_forall_conj_notMem_elementaryClosure
        A hAfin hAδ htf hglox hh1).mp hnc⟩
  · intro hsat H instH hne htf
    letI := instH
    obtain ⟨g, h, hg1, hh1, hescape⟩ := hsat H instH hne htf
    obtain ⟨T, hT, δ, hδ⟩ := hne.1
    let A : Alphabet H := ⟨(T : Set H), hT⟩
    have hAfin : A.carrier.Finite := T.finite_toSet
    have hAδ : IsHyperbolicSpace (δ : ℝ) (Cayley A) :=
      isHyperbolicSpace_cayley_of_fourPoint A hδ
    have hglox : IsLoxodromic g (Cayley.base A) :=
      HullSCUnionGeometry.isLoxodromic_cayley_of_not_isOfFinOrder
        A hAfin hAδ (htf.not_isOfFinOrder hg1)
    refine ⟨g, h, ?_, ?_,
      (not_osinCommensurable_iff_forall_conj_notMem_elementaryClosure
        A hAfin hAδ htf hglox hh1).mpr hescape⟩
    · intro n hn hpow
      exact hg1 (htf g n hn hpow)
    · intro n hn hpow
      exact hh1 (htf h n hn hpow)

/-- The shortest exact statement of the remaining Fournier--Facio pair
theorem: one loxodromic elementary closure has conjugacy saturation different
from the whole group. -/
theorem hyperbolicNonCommensurablePairStatement_iff_saturationProper :
    HyperbolicNonCommensurablePairStatement ↔
      HyperbolicElementaryClosureConjugacySaturationProper :=
  hyperbolicNonCommensurablePairStatement_iff_conjugacySaturationEscape.trans
    hyperbolicConjugacySaturationPairEscape_iff_saturationProper

/-! ## 4.  A prescribed-axis sufficient condition, with the exact hypotheses -/

/-- A source-faithful prescribed-axis strengthening.  Unlike the older
`HyperbolicLoxodromicCommensurabilityEscape`, this proposition retains the
torsion-free premise that the Fournier--Facio consumer has and the reverse
commensurability criterion uses. -/
def TorsionFreeHyperbolicElementaryClosureConjugacyEscape : Prop :=
  ∀ (H : Type) (_ : Group H) (A : Alphabet H), A.carrier.Finite →
    ∀ δ : ℝ, IsHyperbolicSpace δ (Cayley A) →
      ¬ IsElementaryGroup H → IsPowerTorsionFree H →
        ∀ g : H, IsLoxodromic g (Cayley.base A) →
          ∃ h : H, h ≠ 1 ∧
            ∀ c : H, c * h * c⁻¹ ∉ Elementary.elementaryClosure g

/-- The prescribed-axis saturation theorem implies the exact pair residue. -/
theorem hyperbolicConjugacySaturationPairEscape_of_prescribed
    (hescape : TorsionFreeHyperbolicElementaryClosureConjugacyEscape) :
    HyperbolicConjugacySaturationPairEscape := by
  intro H instH hne htf
  letI := instH
  haveI : Nontrivial H := nontrivial_of_not_isElementaryGroup hne.2
  obtain ⟨g, hg1⟩ := exists_ne (1 : H)
  obtain ⟨T, hT, δ, hδ⟩ := hne.1
  let A : Alphabet H := ⟨(T : Set H), hT⟩
  have hAfin : A.carrier.Finite := T.finite_toSet
  have hAδ : IsHyperbolicSpace (δ : ℝ) (Cayley A) :=
    isHyperbolicSpace_cayley_of_fourPoint A hδ
  have hglox : IsLoxodromic g (Cayley.base A) :=
    HullSCUnionGeometry.isLoxodromic_cayley_of_not_isOfFinOrder
      A hAfin hAδ (htf.not_isOfFinOrder hg1)
  obtain ⟨h, hh1, hsat⟩ :=
    hescape H instH A hAfin (δ : ℝ) hAδ hne.2 htf g hglox
  exact ⟨g, h, hg1, hh1, hsat⟩

/-- Consequently the prescribed-axis saturation theorem closes the original
non-commensurable-pair statement. -/
theorem hyperbolicNonCommensurablePairStatement_of_conjugacySaturationEscape
    (hescape : TorsionFreeHyperbolicElementaryClosureConjugacyEscape) :
    HyperbolicNonCommensurablePairStatement :=
  hyperbolicNonCommensurablePairStatement_iff_conjugacySaturationEscape.mpr
    (hyperbolicConjugacySaturationPairEscape_of_prescribed hescape)

end RelHyp
end GGT
end GroupApproximation
