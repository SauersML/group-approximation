import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic
import GroupApproximation.Manuscript.NonMF.SimpleInDefect
import GroupApproximation.Algebra.GroupTorsionFree
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.Data.ZMod.QuotientGroup

/-!
# The Fournier-Facio paragraph of `thm:torsion-free`

`non_mf_groups_exist.tex`, section `sec:torsion-free`, the paragraph that opens
the construction:

> Fournier-Facio constructs a finitely presented torsion-free group `G₀` with
> property (T), a subgroup `Γ ≤ G₀` with property (T), an element `t ∈ G₀` with
> `tΓt⁻¹ ≤ Γ`, and a subgroup `J ≤ G₀` isomorphic to a finitely presented
> infinite simple group, such that `[Γ,J] = 1` and `tJt⁻¹ ≤ Γ` [FFF, §2].  The
> group `G₀` is obtained there as a common quotient of two finitely generated
> acylindrically hyperbolic groups by Hull's theorem [Hull, Corollary 7.4],
> which allows the quotient to be chosen acylindrically hyperbolic; we take
> `G₀` to be such a quotient.  Put `S = tJt⁻¹`.  Since `J` is simple and
> nonabelian, `J` and `S` are perfect.

`FournierFacioParagraph` is that paragraph as **one closed proposition**, with
no declaration inputs: the group, the subgroups and the element are all
existentially quantified inside it.  It is a citation of

* F. Fournier-Facio, **§2**, for `G₀`, `Γ`, `t` and `J` with the four printed
  relations, and
* M. Hull, *Small cancellation in acylindrically hyperbolic groups*,
  **Corollary 7.4**, for the clause that `G₀` may be taken acylindrically
  hyperbolic.

Nothing in this repository inhabits it, and nothing should: it is the printed
paragraph's literature input and it travels as an explicit hypothesis of
`TorsionFreePrintedTheorem.manuscriptTorsionFreeTheorem`.

## The relation to `PrintedFournierFacioData`

The four printed relations are exactly the fields `conj_core_mem`,
`simpleFactor_centralizes`, `conj_simpleFactor_mem` and `simple` of
`Manuscript.NonMF.PrintedFournierFacioData`, over which
`SimpleInDefect.manuscriptLemmaCommutatorInDefect` proves
`lem:commutator-in-defect` by the printed proof.  That structure carries one
further field, `nonabelian`, and the printed paragraph does **not** cite it:
the print derives nonabelianness from the cited words *infinite simple*.  So
does this module.  `exists_not_commute_of_isSimpleGroup_of_infinite` proves that
an infinite simple group is nonabelian, and
`printedFournierFacioDataOfInfiniteSimple` builds the datum from the printed
clauses alone, with no `nonabelian` argument.  The paragraph therefore asks for
nothing the print does not cite, even though the structure it produces has a
field the print does not mention.

`Group.IsFinitelyPresented ↥F.simpleFactor` and `Infinite ↥F.simpleFactor`
render *"isomorphic to a finitely presented infinite simple group"*: both
properties, like simplicity, are invariants of the isomorphism type, so naming
them at `↥J` is the same assertion as naming an isomorphism with such a group.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## "Since `J` is simple and nonabelian" -/

/-- **An infinite simple group is nonabelian.**

The printed paragraph cites *"a finitely presented infinite simple group"* and
then uses the word *nonabelian* without citing it, because an abelian simple
group is cyclic of prime order and so is finite.

The proof is that argument.  If every pair of elements commuted then every
subgroup would be normal, so for `x ≠ 1` the subgroup `⟨x⟩` is everything and
`⟨x²⟩` is `1` or everything.  In the first case `x² = 1`; in the second
`x = x^{2k}` for some `k`, and `2k = 1` is impossible — so in either case `x`
has finite order, `⟨x⟩ = G` is finite, and the group is not infinite. -/
theorem exists_not_commute_of_isSimpleGroup_of_infinite (J : Type u) [Group J]
    [IsSimpleGroup J] [Infinite J] : ∃ x y : J, ¬ Commute x y := by
  by_contra hcon
  -- Every pair commutes.
  have hcomm : ∀ a b : J, a * b = b * a := by
    intro a b
    by_contra h
    exact hcon ⟨a, b, fun hc => h hc.eq⟩
  -- So every subgroup is normal.
  have hnormal : ∀ H : Subgroup J, H.Normal := by
    intro H
    refine ⟨fun n hn g => ?_⟩
    have hg : g * n * g⁻¹ = n := by
      calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [hcomm g n]
        _ = n := by group
    rw [hg]
    exact hn
  obtain ⟨x, hx⟩ := exists_ne (1 : J)
  -- "`⟨x⟩ = G`."
  have hxtop : Subgroup.zpowers x = ⊤ := by
    refine ((hnormal _).eq_bot_or_eq_top).resolve_left ?_
    intro h
    exact hx (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers x))
  -- "`x` has finite order."
  have hfin : IsOfFinOrder x := by
    by_contra hnot
    have hinj : Function.Injective fun n : ℤ => x ^ n :=
      injective_zpow_iff_not_isOfFinOrder.mpr hnot
    rcases (hnormal (Subgroup.zpowers (x * x))).eq_bot_or_eq_top with h | h
    · -- `⟨x²⟩ = 1`, so `x² = 1`.
      have h2 : x * x = 1 :=
        Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers (x * x))
      have hz : (fun n : ℤ => x ^ n) (2 : ℤ) = (fun n : ℤ => x ^ n) (0 : ℤ) := by
        simp only [zpow_two, h2, zpow_zero]
      have := hinj hz
      norm_num at this
    · -- `⟨x²⟩ = G`, so `x = x^{2k}`.
      have hmem : x ∈ Subgroup.zpowers (x * x) := h ▸ Subgroup.mem_top x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hz : (fun n : ℤ => x ^ n) (2 * k) = (fun n : ℤ => x ^ n) (1 : ℤ) := by
        simp only [zpow_mul, zpow_two, hk, zpow_one]
      have hk1 := hinj hz
      omega
  -- "so `G = ⟨x⟩` is finite."
  have hset : (Subgroup.zpowers x : Set J) = Set.univ := by
    rw [hxtop, Subgroup.coe_top]
  have hufin : (Set.univ : Set J).Finite := hset ▸ hfin.finite_zpowers
  haveI : Finite J := Set.finite_univ_iff.mp hufin
  exact not_finite J

/-- **The printed configuration, built from the printed clauses only.**

Every argument is a sentence of the Fournier-Facio paragraph.  The structure's
`nonabelian` field is supplied by
`exists_not_commute_of_isSimpleGroup_of_infinite` rather than asked for, so
this constructor takes exactly what the paragraph cites. -/
def printedFournierFacioDataOfInfiniteSimple {G₀ : Type u} [Group G₀]
    (core : Subgroup G₀) (t : G₀) (simpleFactor : Subgroup G₀)
    (conj_core_mem : ∀ γ ∈ core, t * γ * t⁻¹ ∈ core)
    (simpleFactor_centralizes : ∀ c ∈ simpleFactor, ∀ γ ∈ core, Commute c γ)
    (conj_simpleFactor_mem : ∀ c ∈ simpleFactor, t * c * t⁻¹ ∈ core)
    (hsimple : IsSimpleGroup ↥simpleFactor) (hinf : Infinite ↥simpleFactor) :
    PrintedFournierFacioData G₀ where
  core := core
  t := t
  simpleFactor := simpleFactor
  conj_core_mem := conj_core_mem
  simpleFactor_centralizes := simpleFactor_centralizes
  conj_simpleFactor_mem := conj_simpleFactor_mem
  simple := hsimple
  nonabelian :=
    @exists_not_commute_of_isSimpleGroup_of_infinite _ _ hsimple hinf

/-! ## The paragraph -/

/-- **The Fournier-Facio paragraph of `sec:torsion-free`, as one closed
proposition.**

> Fournier-Facio constructs a finitely presented torsion-free group `G₀` with
> property (T), a subgroup `Γ ≤ G₀` with property (T), an element `t ∈ G₀` with
> `tΓt⁻¹ ≤ Γ`, and a subgroup `J ≤ G₀` isomorphic to a finitely presented
> infinite simple group, such that `[Γ,J] = 1` and `tJt⁻¹ ≤ Γ` [FFF, §2].  The
> group `G₀` is obtained there as a common quotient of two finitely generated
> acylindrically hyperbolic groups by Hull's theorem [Hull, Corollary 7.4],
> which allows the quotient to be chosen acylindrically hyperbolic; we take
> `G₀` to be such a quotient.

Clause by clause: `Group.IsFinitelyPresented G₀`, `IsPowerTorsionFree G₀`,
`HasKazhdanPropertyT G₀` and `IsAcylindricallyHyperbolic G₀` are the four
adjectives on `G₀`; the datum `F` carries `Γ = F.core`, `t = F.t`, `J =
F.simpleFactor` and the four relations `tΓt⁻¹ ≤ Γ`, `[Γ,J] = 1`, `tJt⁻¹ ≤ Γ`
and simplicity of `J`; and the last three conjuncts are property (T) of `Γ`
together with *"finitely presented infinite"* for `J`.

Torsion-freeness is `IsPowerTorsionFree` — *a positive power is the identity
only for the identity* — the ordinary group-theoretic notion, as everywhere
else in this development.  Acylindrical hyperbolicity is
`TorsionFree.IsAcylindricallyHyperbolic`, the Cayley-graph class that
`lem:saturation` consumes. -/
def FournierFacioParagraph : Prop :=
  ∃ (G₀ : Type) (_ : Group G₀), Group.IsFinitelyPresented G₀ ∧
    IsPowerTorsionFree G₀ ∧ HasKazhdanPropertyT.{0, 0} G₀ ∧
      IsAcylindricallyHyperbolic G₀ ∧
        ∃ F : PrintedFournierFacioData G₀,
          HasKazhdanPropertyT.{0, 0} ↥F.core ∧
            Group.IsFinitelyPresented ↥F.simpleFactor ∧
              Infinite ↥F.simpleFactor

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation
