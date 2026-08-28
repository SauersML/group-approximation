import GroupApproximation.GGT.ElementaryProjectionCriterion
import GroupApproximation.GGT.WPDAcylindricalHyperbolicity

/-!
# `E(h) ≠ ⊤` reduces to the finite-index half, not to non-elementarity

`GGT.WPDElementaryEmbedding` splits Dahmani--Guirardel--Osin's Theorem 6.8 into a
cone-off half and `GGT.ElementaryClosureProper`, which asks for

    ∀ G [Group G] (D : AH3Data G), ¬ IsVirtuallyCyclic G →
      Elementary.elementaryClosure D.elt ≠ ⊤.

**The route through non-elementarity does not work, and the reason is a genuine
counterexample rather than a gap.**  It would go: `¬ IsVirtuallyCyclic G` gives a
pair with no common nonzero power, that pair gives `ActsNonElementarily ⊤`, and
`exists_notMem_elementaryClosure_of_centralizer` then gives an element outside
`E(h)`.  The first step is false.  A Tarski monster of exponent `p` is infinite
and torsion, hence not virtually cyclic, and every pair `a, b` in it satisfies
`a^p = b^p = 1` --- so *every* pair has a common nonzero power and none is
common-power-free.  Non-virtual-cyclicity alone therefore supplies nothing, and
any proof of `ElementaryClosureProper` has to use the loxodromic element that the
`(AH₃)` datum records, whose infinite order is what excludes the monster.

## The route that does work, and where it lands

Contrapositively: if `E(h) = ⊤` then every element of `G` translates the
`h`-orbit along itself, and `exists_finite_transversal_of_coarseTranslation`
(proved in `GGT.ElementaryProjectionCriterion` from `IsWPDAt` alone) puts all of
`G` into finitely many cosets of `⟨h⟩` --- which is `IsVirtuallyCyclic G`
verbatim, in the coset form `GGT.IsVirtuallyCyclic` already carries.

So `ElementaryClosureProper` is not a separate obligation: it is the finite-index
half of Lemma 6.5 read contrapositively.  That is worth recording, because it
means the leaf `ElementaryClosureCoarseTranslation` and the orientation-reversing
sign case are the *only* things between here and it --- the same two items
already blocking the finite-index half, and no new geometry.

## What is proved here

* `isVirtuallyCyclic_of_finite_transversal` --- finitely many cosets of a cyclic
  subgroup covering `G` is `GGT.IsVirtuallyCyclic` on the nose.
* `false_of_forall_shift_of_not_isVirtuallyCyclic` --- if every element of a
  non-virtually-cyclic group shifted the orbit of `h` along itself, that would be
  a contradiction.  This is the reduction above, with the shift hypothesis left
  explicit because supplying it for every element of `E(h)` is exactly what the
  leaf plus the sign case do.

Neither uses loxodromy, acylindricity or hyperbolicity: as with the transversal
theorem itself, `IsWPDAt` and the isometry of the action carry all of it.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

section Transversal

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **Finitely many cosets of a cyclic subgroup covering `G` is virtual
cyclicity.**  `GGT.IsVirtuallyCyclic` is stated in exactly this coset form, so
the transversal produced by the WPD argument is already the required datum. -/
theorem isVirtuallyCyclic_of_finite_transversal {h : G} {F : Set G}
    (hFfin : F.Finite)
    (hall : ∀ a : G, ∃ (c : ℤ) (f : G), f ∈ F ∧ a = h ^ c * f) :
    IsVirtuallyCyclic G := by
  classical
  refine ⟨h, hFfin.toFinset, ?_⟩
  intro a
  obtain ⟨c, f, hfF, ha⟩ := hall a
  exact ⟨f, hFfin.mem_toFinset.mpr hfF, c, ha⟩

/-- **The contrapositive of the finite-index half.**  If every element of `G`
carried the `h`-orbit along itself with a bounded error, `G` would be virtually
cyclic.

The shift hypothesis is left explicit rather than derived from `E(h) = ⊤`,
because producing it for every element of `E(h)` is precisely what
`ElementaryClosureCoarseTranslation` and the orientation-reversing sign case
supply; everything after it is the transversal theorem, which needs only
`IsWPDAt`. -/
theorem false_of_forall_shift_of_not_isVirtuallyCyclic
    (hiso : IsIsometricAction G X) {h : G} {x : X} (hwpd : IsWPDAt h x)
    {K : ℝ} (hK : 0 ≤ K)
    (hall : ∀ a : G, ∃ c : ℤ, ∀ m : ℤ,
      dist ((a * h ^ m) • x) ((h ^ (m + c)) • x) ≤ K)
    (hnvc : ¬ IsVirtuallyCyclic G) : False := by
  obtain ⟨F, hFfin, hF⟩ :=
    exists_finite_transversal_of_coarseTranslation hiso hwpd hK
  exact hnvc (isVirtuallyCyclic_of_finite_transversal hFfin
    (fun a => hF a (hall a)))

/-- The same in the form `ElementaryClosureProper` consumes: a group in which
every element shifts the orbit is virtually cyclic, so a non-virtually-cyclic
one has an element that does not. -/
theorem exists_not_shift_of_not_isVirtuallyCyclic
    (hiso : IsIsometricAction G X) {h : G} {x : X} (hwpd : IsWPDAt h x)
    {K : ℝ} (hK : 0 ≤ K) (hnvc : ¬ IsVirtuallyCyclic G) :
    ∃ a : G, ¬ ∃ c : ℤ, ∀ m : ℤ,
      dist ((a * h ^ m) • x) ((h ^ (m + c)) • x) ≤ K := by
  by_contra hcon
  push_neg at hcon
  exact false_of_forall_shift_of_not_isVirtuallyCyclic hiso hwpd hK hcon hnvc

end Transversal

end Elementary
end GGT
end GroupApproximation
