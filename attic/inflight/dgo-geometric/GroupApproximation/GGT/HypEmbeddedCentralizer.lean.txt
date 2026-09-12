import GroupApproximation.GGT.DGOProposition433Finite
import GroupApproximation.Manuscript.NonMF.TorsionFreeRelativeQuotient
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Tactic.Group

/-!
# The centraliser of a normal subgroup that carries a hyperbolically embedded element

Step 3 of Dahmani--Guirardel--Osin's proof of their Theorem 2.35 is the
computation `C_G(N) = 1` for the normal subgroup `N` their steps 1 and 2
produce; they run it as three applications of their Proposition 4.33.  This
module proves it, unconditionally, from the repository's own
`GGT.dgoProposition433`.

## The argument

Let `N ⊴ G` contain an element `c` whose elementary closure `E(c)` is
hyperbolically embedded in `G`, and suppose `E(c)` is proper.  Put
`A = C_G(N)`.

* `A` is normal in `G`, because `N` is (`centralizer_normal_of_normal`).
* `A ≤ E(c)`: an element centralising `N` centralises `c ∈ N`, and an element
  commuting with `c` lies in `E(c)` by the definition of the elementary
  closure (`centralizer_le_elementaryClosure`).  The main theorem is proved at
  the general containment `A ≤ H` for a hyperbolically embedded `H`
  (`centralizer_eq_bot_of_le_isHypEmbedded`), since which subgroup `H` is plays
  no role; the elementary closure is one supply of it.
* Hence for any `a ∉ E(c)`, every `x ∈ A` lies in `E(c)` *and* has
  `a⁻¹ x a ∈ A ≤ E(c)`, by normality of `A`.  So `A` is contained in the set
  Proposition 4.33 declares finite, and `A` is finite.
* A finite normal subgroup of a group with trivial finite radical is trivial.

Nothing here is geometric: the geometry is entirely inside
`dgoProposition433`, which the repository proves, and inside the hypothesis
that `E(c)` is hyperbolically embedded, which is Dahmani--Guirardel--Osin's
Theorem 6.8 and is *not* proved here — it is a hypothesis of the statement,
supplied by whatever produces the loxodromic element.

## Where it is used

`Manuscript/NonMF/DGOTheorem235Slice.FreeNormalSubgroupAtHypEmbedded` asks for a
normal subgroup that is free of rank at least two **and has trivial
centraliser**.  This module discharges the second conjunct outright, so that the
residue of that Prop is the first: their Theorem 6.14 and their Theorem 7.19(e).

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` through DGO 2.35; certifies no
printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.GGT.Elementary
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

universe u

variable {G : Type u} [Group G]

/-! ## Almost malnormality, for a single hyperbolically embedded subgroup -/

/-- **A hyperbolically embedded subgroup is almost malnormal.**  For `a ∉ H`
the set of `h ∈ H` whose conjugate `a⁻¹ h a` is again in `H` is finite.  This
is `dgoProposition433` read through `IsHypEmbedded`. -/
theorem finite_mem_inter_conj_of_isHypEmbedded {H : Subgroup G}
    (hH : IsHypEmbedded G H) {a : G} (ha : a ∉ H) :
    {h : G | h ∈ H ∧ a⁻¹ * h * a ∈ H}.Finite := by
  obtain ⟨X, D, _, hfam, hemb⟩ := hH
  have hfam' : D.fam () = H := by rw [hfam]
  have hmain := dgoProposition433 G D hemb a (by rw [hfam']; exact ha)
  rwa [hfam'] at hmain

/-! ## The centraliser of a normal subgroup is normal -/

/-- The centraliser of a normal subgroup is normal. -/
theorem centralizer_normal_of_normal {N : Subgroup G} (hN : N.Normal) :
    (Subgroup.centralizer (N : Set G)).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro n hn
  have hg : g⁻¹ * n * g ∈ (N : Set G) := by
    have := hN.conj_mem n hn g⁻¹
    simpa using this
  have hcomm := hx _ hg
  calc n * (g * x * g⁻¹) = g * ((g⁻¹ * n * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * n * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * x * g⁻¹) * n := by group

/-! ## The centraliser is trivial -/

/-- **The general form of step 3.**  A normal subgroup whose centraliser lies
inside a proper hyperbolically embedded subgroup has trivial centraliser, as
soon as the ambient group has no nontrivial finite normal subgroup.

Only three things are used: normality of `N`, so that its centraliser is
normal; containment of that centraliser in `H`; and almost malnormality of `H`.
Which `H` is irrelevant, so a construction may supply whichever hyperbolically
embedded subgroup it has. -/
theorem centralizer_eq_bot_of_le_isHypEmbedded
    {N : Subgroup G} (hN : N.Normal) {H : Subgroup G}
    (hle : Subgroup.centralizer (N : Set G) ≤ H) (hH : IsHypEmbedded G H)
    {a : G} (ha : a ∉ H) (hrad : HasTrivialFiniteRadical G) :
    Subgroup.centralizer (N : Set G) = ⊥ := by
  have hAnormal : (Subgroup.centralizer (N : Set G)).Normal :=
    centralizer_normal_of_normal hN
  have hsub : (Subgroup.centralizer (N : Set G) : Set G) ⊆
      {h : G | h ∈ H ∧ a⁻¹ * h * a ∈ H} := by
    intro x hx
    refine ⟨hle hx, hle ?_⟩
    have := hAnormal.conj_mem x hx a⁻¹
    simpa using this
  have hfin : (Subgroup.centralizer (N : Set G) : Set G).Finite :=
    (finite_mem_inter_conj_of_isHypEmbedded hH ha).subset hsub
  have hfinite : Finite (Subgroup.centralizer (N : Set G)) := hfin.to_subtype
  exact hrad _ hAnormal hfinite

/-- **The centraliser of `N` lies in `E(c)` for every `c ∈ N`.**  An element
centralising `N` centralises `c`, and a commuting element lies in the
elementary closure. -/
theorem centralizer_le_elementaryClosure {N : Subgroup G} {c : G} (hcN : c ∈ N) :
    Subgroup.centralizer (N : Set G) ≤ elementaryClosure c := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  exact mem_elementaryClosure_of_commute (hx c (SetLike.mem_coe.mpr hcN)).symm

/-- **Step 3 of Dahmani--Guirardel--Osin's proof of Theorem 2.35.**

If `N` is normal, contains an element `c` whose elementary closure is
hyperbolically embedded and proper, and `G` has no nontrivial finite normal
subgroup, then `C_G(N) = 1`. -/
theorem centralizer_eq_bot_of_isHypEmbedded_elementaryClosure
    {N : Subgroup G} (hN : N.Normal) {c : G} (hcN : c ∈ N)
    (hE : IsHypEmbedded G (elementaryClosure c))
    {a : G} (ha : a ∉ elementaryClosure c)
    (hrad : HasTrivialFiniteRadical G) :
    Subgroup.centralizer (N : Set G) = ⊥ :=
  centralizer_eq_bot_of_le_isHypEmbedded hN
    (centralizer_le_elementaryClosure hcN) hE ha hrad

end GGT
end GroupApproximation

open GroupApproximation.GGT

#audit_axioms finite_mem_inter_conj_of_isHypEmbedded
#audit_axioms centralizer_normal_of_normal
#audit_axioms centralizer_eq_bot_of_le_isHypEmbedded
#audit_axioms centralizer_le_elementaryClosure
#audit_axioms centralizer_eq_bot_of_isHypEmbedded_elementaryClosure
