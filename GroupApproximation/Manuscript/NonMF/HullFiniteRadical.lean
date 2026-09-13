import GroupApproximation.GGT.HullYiFiniteRadicalDetector
import GroupApproximation.Manuscript.NonMF.TorsionFreeRelativeQuotient
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's finite radical `K(G)` and the class `AH₀`

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, arXiv:1308.4345, §5.
`non_mf_groups_exist.tex` cites Hull's Corollary 7.4 (tex line 1682), whose statement uses
the finite radical and the class `AH₀`:

> In [DGO], it is shown that every `G ∈ AH` contains a maximal finite normal subgroup, called
> the finite radical of `G` and denoted by `K(G)`.

> Notice that a group `G ∈ AH` will contain suitable subgroups if and only if `K(G) = {1}`.
> [...] `AH₀` denotes the class of `G ∈ AH` such that `G` has no finite normal subgroups, or
> equivalently `K(G) = {1}`.

## The proof

`finiteRadical G` is the join of the finite normal subgroups.  The argument of Hull's
Lemma 5.5 makes it finite for `G ∈ AH`.  A finite subgroup `N` normalized by `h` is centralized
by a positive power of `h`, since there are only finitely many maps `N → N`, so
`N ≤ C_G(hⁿ) ≤ E(h)`.  Two independent loxodromics `f₁, f₂` have finite `E(f₁) ∩ E(f₂)`
(`Elementary.not_infinite_le_inf_elementaryClosure`, with Osin's Theorem 6.8 proved as
`HullSC.elementaryClosureVirtuallyCyclic_hullGeneratingSet`).  So the join lies in a finite
subgroup.

`K(G) = {1}` is spelled `TorsionFreePrinted.HasTrivialFiniteRadical G`, and
`hasTrivialFiniteRadical_iff_finiteRadical_eq_bot` proves it equivalent to
`finiteRadical G = ⊥`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace HullFiniteRadical

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

universe u

/-! ## A finite subgroup normalized by `h` lies in `E(h)` -/

/-- **A finite subgroup normalized by `h` is centralized by a positive power of `h`.**
Conjugation by `hⁿ` maps `N` into itself for every `n`, and there are only finitely many maps
`N → N`, so two powers of `h` induce the same map. -/
theorem exists_pow_commute_of_finite {G : Type u} [Group G] {N : Subgroup G} [Finite N]
    {h : G} (hN : ∀ x ∈ N, h * x * h⁻¹ ∈ N) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ N, Commute (h ^ k) x := by
  have hpow : ∀ n : ℕ, ∀ x ∈ N, h ^ n * x * (h ^ n)⁻¹ ∈ N := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have heq : h ^ (n + 1) * x * (h ^ (n + 1))⁻¹ = h * (h ^ n * x * (h ^ n)⁻¹) * h⁻¹ := by
        simp only [pow_succ', mul_inv_rev, mul_assoc]
      rw [heq]
      exact hN _ (ih x hx)
  let f : ℕ → (N → N) := fun n x => ⟨h ^ n * (x : G) * (h ^ n)⁻¹, hpow n x x.2⟩
  have key : ∀ a b : ℕ, a < b → f a = f b →
      ∃ k : ℕ, 0 < k ∧ ∀ x ∈ N, Commute (h ^ k) x := by
    intro a b hab hfab
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    refine ⟨k + 1, Nat.succ_pos k, fun x hx => ?_⟩
    have hval : h ^ a * x * (h ^ a)⁻¹ = h ^ (a + k + 1) * x * (h ^ (a + k + 1))⁻¹ :=
      congrArg Subtype.val (congrFun hfab ⟨x, hx⟩)
    have hsplit : h ^ (a + k + 1) = h ^ a * h ^ (k + 1) := by
      rw [add_assoc, pow_add]
    rw [hsplit] at hval
    have hconj : x = h ^ (k + 1) * x * (h ^ (k + 1))⁻¹ := by
      calc x = (h ^ a)⁻¹ * (h ^ a * x * (h ^ a)⁻¹) * h ^ a := by group
        _ = (h ^ a)⁻¹ * (h ^ a * h ^ (k + 1) * x * (h ^ a * h ^ (k + 1))⁻¹) * h ^ a := by
          rw [hval]
        _ = h ^ (k + 1) * x * (h ^ (k + 1))⁻¹ := by group
    show h ^ (k + 1) * x = x * h ^ (k + 1)
    calc h ^ (k + 1) * x = h ^ (k + 1) * x * (h ^ (k + 1))⁻¹ * h ^ (k + 1) := by group
      _ = x * h ^ (k + 1) := by rw [← hconj]
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · exact key a b hlt hfab
  · exact key b a hlt hfab.symm

/-- **A finite subgroup normalized by `h` lies in the elementary closure `E(h)`.**  This is
the step *"there exists `n` such that `N ≤ C_G(hⁿ)`, and thus `N ≤ E_G(h)`"* of Hull's proof
of Lemma 5.5; no hypothesis on `h` is needed. -/
theorem le_elementaryClosure_of_finite {G : Type u} [Group G] {N : Subgroup G} [Finite N]
    {h : G} (hN : ∀ x ∈ N, h * x * h⁻¹ ∈ N) : N ≤ elementaryClosure h := by
  obtain ⟨k, hk, hcomm⟩ := exists_pow_commute_of_finite hN
  intro x hx
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  refine mem_elementaryClosure.mpr ⟨k, k, hk0, hk0, ?_⟩
  rw [zpow_natCast, (hcomm x hx).symm.eq, mul_inv_cancel_right]

#audit_axioms le_elementaryClosure_of_finite

/-! ## The finite radical -/

/-- **Hull's finite radical `K(G)`**: the join of the finite normal subgroups of `G`. -/
def finiteRadical (G : Type u) [Group G] : Subgroup G :=
  ⨆ N : {N : Subgroup G // N.Normal ∧ Finite N}, (N : Subgroup G)

/-- `K(G)` is normal: a join of normal subgroups is normal. -/
instance finiteRadical_normal (G : Type u) [Group G] : (finiteRadical G).Normal := by
  haveI : ∀ N : {N : Subgroup G // N.Normal ∧ Finite N}, (N : Subgroup G).Normal :=
    fun N => N.2.1
  exact Subgroup.iSup_normal (fun N : {N : Subgroup G // N.Normal ∧ Finite N} =>
    (N : Subgroup G))

/-- Every finite normal subgroup lies in `K(G)`. -/
theorem le_finiteRadical {G : Type u} [Group G] {N : Subgroup G} (hN : N.Normal)
    (hfin : Finite N) : N ≤ finiteRadical G :=
  le_iSup (fun N : {N : Subgroup G // N.Normal ∧ Finite N} => (N : Subgroup G))
    ⟨N, hN, hfin⟩

/-- **`K(G) = {1}` is `HasTrivialFiniteRadical G`**, in every group. -/
theorem hasTrivialFiniteRadical_iff_finiteRadical_eq_bot {G : Type u} [Group G] :
    HasTrivialFiniteRadical G ↔ finiteRadical G = ⊥ := by
  constructor
  · intro h
    exact iSup_eq_bot.mpr fun N => h N N.2.1 N.2.2
  · intro h N hN hfin
    have hle := le_finiteRadical hN hfin
    rw [h] at hle
    exact le_bot_iff.mp hle

#audit_axioms hasTrivialFiniteRadical_iff_finiteRadical_eq_bot

/-- Every elementary closure contains `K(G)`: a finite normal subgroup is normalized by
every element. -/
theorem finiteRadical_le_elementaryClosure {G : Type u} [Group G] (g : G) :
    finiteRadical G ≤ elementaryClosure g := by
  refine iSup_le fun N => ?_
  haveI : Finite (N : Subgroup G) := N.2.2
  exact le_elementaryClosure_of_finite fun x hx => N.2.1.conj_mem x hx g

/-- **`K(G)` is finite for `G ∈ AH`.**  It lies in `E(f₁) ∩ E(f₂)` for two independent
loxodromics of Hull's generating set, and no infinite subgroup lies in both. -/
theorem finite_finiteRadical (G : Type u) [Group G] [IsAcylindricallyHyperbolic G] :
    Finite (finiteRadical G) := by
  obtain ⟨A⟩ := exists_hullGeneratingSet G
  obtain ⟨g₁, -, g₂, -, hlox₁, hlox₂, hind⟩ := A.nonElementary
  have hfin : ((finiteRadical G : Subgroup G) : Set G).Finite := by
    refine Set.not_infinite.mp fun hinf => ?_
    exact not_infinite_le_inf_elementaryClosure (isIsometricAction_cayley A.alphabet)
      (HullSC.elementaryClosureVirtuallyCyclic_hullGeneratingSet A) hlox₁ hlox₂ hind
      (finiteRadical_le_elementaryClosure g₁) (finiteRadical_le_elementaryClosure g₂) hinf
  exact hfin.to_subtype

#audit_axioms finite_finiteRadical

/-! ## Hull's sentences -/

/-- **Hull, §5, after Lemma 5.5.**  *"Every `G ∈ AH` contains a maximal finite normal
subgroup, called the finite radical of `G` and denoted by `K(G)`."*  `K(G)` is normal and
finite, contains every finite normal subgroup, and so is maximal among them. -/
def PrintedHullFiniteRadical : Prop :=
  ∀ {G : Type u} [Group G], IsAcylindricallyHyperbolic G →
    (finiteRadical G).Normal ∧ Finite (finiteRadical G) ∧
      (∀ N : Subgroup G, N.Normal → Finite N → N ≤ finiteRadical G) ∧
        ∀ N : Subgroup G, N.Normal → Finite N → finiteRadical G ≤ N → N = finiteRadical G

theorem printedHullFiniteRadical : PrintedHullFiniteRadical.{u} := by
  intro G _ hG
  have hfin : Finite (finiteRadical G) := @finite_finiteRadical G _ hG
  refine ⟨finiteRadical_normal G, hfin, fun N hN hNfin => le_finiteRadical hN hNfin, ?_⟩
  intro N hN hNfin hle
  exact le_antisymm (le_finiteRadical hN hNfin) hle

#audit_closed_axioms printedHullFiniteRadical

/-- **Hull's class `AH₀`**: *"the class of `G ∈ AH` such that `G` has no finite normal
subgroups"*, nontrivial ones being meant. -/
def IsAH0 (G : Type u) [Group G] : Prop :=
  IsAcylindricallyHyperbolic G ∧ HasTrivialFiniteRadical G

/-- **Hull, §5, before Lemma 5.10.**  *"`AH₀` denotes the class of `G ∈ AH` such that `G`
has no finite normal subgroups, or equivalently `K(G) = {1}`."* -/
def PrintedHullAH0 : Prop :=
  ∀ {G : Type u} [Group G], IsAH0 G ↔ IsAcylindricallyHyperbolic G ∧ finiteRadical G = ⊥

theorem printedHullAH0 : PrintedHullAH0.{u} := by
  intro G _
  exact ⟨fun h => ⟨h.1, hasTrivialFiniteRadical_iff_finiteRadical_eq_bot.mp h.2⟩,
    fun h => ⟨h.1, hasTrivialFiniteRadical_iff_finiteRadical_eq_bot.mpr h.2⟩⟩

#audit_closed_axioms printedHullAH0

/-- A subgroup suitable for some alphabet normalizes the finite normal subgroup `K(G)`, so
`K(G)` is trivial once it is finite. -/
theorem finiteRadical_eq_bot_of_suitable {G : Type u} [Group G]
    [IsAcylindricallyHyperbolic G] {A : Alphabet G} {S : Subgroup G} (hS : Suitable A S) :
    finiteRadical G = ⊥ :=
  hS.normalizesNoNontrivialFinite (finiteRadical G) (finite_finiteRadical G)
    (fun _ _ x hx => (finiteRadical_normal G).conj_mem x hx _)

#audit_axioms finiteRadical_eq_bot_of_suitable

/-- With `K(G) = {1}`, the whole group is suitable for Hull's alphabet: it acts
non-elementarily, and a finite subgroup it normalizes is a finite normal subgroup. -/
theorem suitable_top_of_finiteRadical_eq_bot {G : Type u} [Group G]
    (A : HullGeneratingSet G) (h : finiteRadical G = ⊥) :
    Suitable A.alphabet (⊤ : Subgroup G) := by
  refine ⟨A.nonElementary, ?_⟩
  intro F hF hnorm
  exact hasTrivialFiniteRadical_iff_finiteRadical_eq_bot.mpr h F
    ⟨fun n hn g => hnorm g (Subgroup.mem_top g) n hn⟩ hF

#audit_axioms suitable_top_of_finiteRadical_eq_bot

/-- **Hull, §5, before Lemma 5.10.**  *"a group `G ∈ AH` will contain suitable subgroups if
and only if `K(G) = {1}`"*, for Hull's generating set `A`. -/
def PrintedHullSuitableIffFiniteRadical : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G),
    (∃ S : Subgroup G, Suitable A.alphabet S) ↔ finiteRadical G = ⊥

theorem printedHullSuitableIffFiniteRadical : PrintedHullSuitableIffFiniteRadical.{u} := by
  intro G _ A
  haveI : IsAcylindricallyHyperbolic G :=
    ⟨⟨A.alphabet, A.delta, A.hyperbolic, A.acylindrical, A.nonElementary⟩⟩
  exact ⟨fun ⟨_, hS⟩ => finiteRadical_eq_bot_of_suitable hS,
    fun h => ⟨⊤, suitable_top_of_finiteRadical_eq_bot A h⟩⟩

#audit_closed_axioms printedHullSuitableIffFiniteRadical

end HullFiniteRadical
end NonMF
end Manuscript
end GroupApproximation
