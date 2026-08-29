import GroupApproximation.GGT.OsinLemma512Torsion
import Mathlib.Data.ZMod.QuotientGroup

/-!
# The elementary closure of a loxodromic misses the relative ball

A consumer needs, for a loxodromic `a` and a radius `eps`,

  `E(a) ∩ D.relBall lam eps = {1}`,

and asked whether it can be ARRANGED by choosing `a`.  It does not have to be
arranged: **in a torsion-free group it holds for every loxodromic `a`, with no
choice and no new hypothesis.**  The reason is ellipticity, and it is short.

Every element `h` of `H_lam` is a letter of `X ⊔ ℋ`, so the whole cyclic group
it generates sits in the radius-one ball around the basepoint --- every power
`h^n` is again in `H_lam`, hence again a letter.  So `⟨h⟩` has a bounded orbit,
and `h` is elliptic.  But `E(a)` for a loxodromic `a` is virtually cyclic, so a
subgroup of it with a bounded orbit and infinite order cannot exist: that is
`exists_notMem_elementaryClosure_of_infinite_bounded`, which produces an element
of the subgroup outside `E(a)` and so contradicts containment.  Hence every
element of `H_lam ∩ E(a)` has finite order, and `D.relBall lam eps ⊆ H_lam`.

So the obstruction is torsion and nothing else:

* `notMem_elementaryClosure_of_mem_fam'` --- an element of the family of infinite
  order is never in the elementary closure of a loxodromic.  No torsion
  hypothesis, no choice of `a`.  This is the general-`Λ` form of
  `GGT.notMem_elementaryClosure_of_mem_fam` (GGT/WPDDGOReduction.lean), which
  states it at `Λ = Unit`; the proof here is different and **needs no
  hyperbolicity hypothesis** --- the `Unit` version goes through
  `exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder'`, which carries
  a `δ`, while the bounded-orbit route does not.  The primed name is deliberate:
  `OsinComponents` sits inside `GGT`, so an unprimed one would silently shadow
  the existing lemma at every unqualified use site.
* `eq_one_of_mem_relBall_of_mem_elementaryClosure` --- with torsion-freeness,
  the intersection is trivial.

With torsion the residue is exactly the finite part: `E(a) ∩ relBall lam eps`
consists of torsion elements, so it is trivial as soon as `a` is chosen with
`E(a) = ⟨a⟩ × K(G)` and `K(G) = 1` --- that is, whenever `G` has no nontrivial
finite normal subgroup.  Arranging it is then a choice of `a`, but in the
torsion-free program there is nothing to arrange.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A letter of the family moves the basepoint by at most one**, at a general
index.  The `Λ = Unit` form is `GGT.dist_base_le_one_of_mem_fam`. -/
theorem dist_base_le_one_of_mem_fam' (D : RelGenSet G Λ) (lam : Λ) {h : G}
    (hh : h ∈ D.fam lam) :
    dist (Cayley.base D.alphabet) (h • Cayley.base D.alphabet) ≤ (1 : ℝ) := by
  have hmem : h ∈ D.alphabet.carrier := RelGenSet.fam_subset_alphabet D lam hh
  have hnorm : WordMetric.wordNorm D.alphabet.carrier h ≤ 1 :=
    WordMetric.wordNorm_le_one_of_mem hmem
  have hdist : dist (Cayley.base D.alphabet) (h • Cayley.base D.alphabet)
      = (WordMetric.wordDist D.alphabet.carrier 1 h : ℝ) := by simp
  rw [hdist, WordMetric.wordDist_one_left]
  exact_mod_cast hnorm

/-- **An element of the peripheral family of infinite order is never in the
elementary closure of a loxodromic.**

Its cyclic group is infinite and has a bounded orbit --- every power is again a
letter --- so `exists_notMem_elementaryClosure_of_infinite_bounded` produces an
element of it outside `E(a)`, contradicting containment.

No choice of `a` and no hypothesis on `G` beyond the acylindricity already in
play. -/
theorem notMem_elementaryClosure_of_mem_fam' (D : RelGenSet G Λ) (lam : Λ)
    (hacy : IsAcylindrical G (Cayley D.alphabet)) {g : G}
    (hg : IsLoxodromic g (Cayley.base D.alphabet)) {x : G}
    (hx : x ∈ D.fam lam) (hord : ¬ IsOfFinOrder x) :
    x ∉ Elementary.elementaryClosure g := by
  intro hmem
  have hsub : Subgroup.zpowers x ≤ Elementary.elementaryClosure g :=
    Subgroup.zpowers_le.mpr hmem
  have hinf : ((Subgroup.zpowers x : Subgroup G) : Set G).Infinite :=
    infinite_zpowers.mpr hord
  have hbdd : ∀ h ∈ Subgroup.zpowers x,
      dist (Cayley.base D.alphabet) (h • Cayley.base D.alphabet) ≤ (1 : ℝ) := by
    intro h hh
    obtain ⟨n, rfl⟩ := hh
    exact dist_base_le_one_of_mem_fam' D lam (zpow_mem hx n)
  obtain ⟨h, hh, hnot⟩ := OsinLemma512.exists_notMem_elementaryClosure_of_infinite_bounded
    (isIsometricAction_cayley D.alphabet) hacy hg hinf hbdd
  exact hnot (hsub hh)

/-- **`E(a) ∩ relBall lam eps = {1}` in a torsion-free group**, for every
loxodromic `a`.

The relative ball lies in the family, so this is
`notMem_elementaryClosure_of_mem_fam'` plus torsion-freeness.  Nothing is
arranged: the clause a consumer wanted to impose on its choice of loxodromic is
a consequence of the setting it is already in. -/
theorem eq_one_of_mem_relBall_of_mem_elementaryClosure (D : RelGenSet G Λ)
    (lam : Λ) (hacy : IsAcylindrical G (Cayley D.alphabet)) {g : G}
    (hg : IsLoxodromic g (Cayley.base D.alphabet))
    (htf : ∀ y : G, IsOfFinOrder y → y = 1) {eps : ℕ} {x : G}
    (hx : x ∈ D.relBall lam eps)
    (hmem : x ∈ Elementary.elementaryClosure g) : x = 1 := by
  refine htf x ?_
  by_contra hord
  exact notMem_elementaryClosure_of_mem_fam' D lam hacy hg hx.1 hord hmem

end OsinComponents
end GGT
end GroupApproximation
