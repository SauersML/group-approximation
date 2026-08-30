import GroupApproximation.GGT.HullSCConeOffHeavyHyperbolic
import GroupApproximation.GGT.HyperbolicFreeGroupAH

/-!
# Geometric separation of a family, and what its shape has to survive

Hull's Theorem 3.9 (`crit`) takes three hypotheses — `Γ(G,X)` hyperbolic, each
`H_λ` quasi-convex in it, and `{H_λ}` geometrically separated — and returns the
whole of `{H_λ} ↪_h (G,X)` once the `H_λ` are locally finite for `d_X`.  The
first is `HullGeneratingSet.hyperbolic`, the second is `IsWordQuasiconvex` of
`GGT/HullSCConeOffHeavyHyperbolic.lean`.  This module states the third and
model-tests it; nothing is proved about elementary closures here.

## The rendering, and the two choices in it

`IsGeometricallySeparated` is Dahmani--Guirardel--Osin's Definition 4.40 for a
**family**, written in the word metric at the identity basepoint.

Two points of the transcription are load-bearing.  The `λ = μ` half of the
conclusion is vacuous for a single subgroup and is exactly what a family needs,
so this is not `ElementaryProjectionCriterion.GeometricallySeparatedAt` with an
index added — that predicate cannot express it.  And `diam ≥ R` is rendered as
`∀ D < R, ∃ a b, D ≤ d(a,b)`, with a **strict** `<`, following the correction
already recorded in that module: `∀ D ≤ R` would strengthen the hypothesis of
the implication, hence weaken the predicate, hence make anything proved from it
claim more than the source does.

Fixing the basepoint at the identity rather than quantifying over all of them is
licensed by Dahmani--Guirardel--Osin's Remark 4.41.

## Model tests

Both are proved below rather than asserted, and the first is sharper than it
looks.

**At the trivial family the predicate holds — but only just.**
`isGeometricallySeparated_bot` needs `R = 2`, and `R = 1` genuinely fails: at
`R = 1` the only `D` is `0`, the required pair may be taken `a = b = 1` with
`0 ≤ d(1,1)`, and both approximation clauses hold with the only available
`c = 1` whenever `|g|_A ≤ ε`.  The conclusion would then demand `g = 1` for
every `g` of the `ε`-ball, which fails in any nontrivial group at `ε ≥ 1`.  So
the predicate is not vacuously true at `⊥`, the existential `∃ R` is doing real
work, and the strict `<` is what lets `R = 2` exclude the degenerate witness.  A
rendering that passed at `R = 1` would have been the wrong one.

**At the full family the predicate fails**, `not_isGeometricallySeparated_top`,
whenever the word metric is unbounded and the index type has two elements: every
clause of the hypothesis is satisfiable — take `c = g⁻¹a` — so the implication
must deliver `λ = μ`, which is false.  This is the test that matters, because
`⊤` is never hyperbolically embedded when infinite
(`GGT.RelGenSet.not_isHyperbolicallyEmbedded_of_fam_subset_base`), and a
separation predicate that accepted it would prove that statement false.
`unbounded_freeGroupAlphabet` supplies the unboundedness, so the test is run
against an actual alphabet and not against a hypothesis nothing satisfies.

## What is not here

That the elementary closures of pairwise non-commensurable loxodromic elements
satisfy this — the content Hull takes from the proof of
Dahmani--Guirardel--Osin's Theorem 6.8.  Its analytic core is already in the
tree as `HullGeometry.exists_common_zpow_of_forward_fellow_travel` (their Lemma
6.7 in the acylindrical form); what is owed is the packaging of `diam ≥ R` into
long fellow-travel of translated quasi-axes and back.  That is the next module,
not this one.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The predicate -/

/-- **Geometric separation of a family** (Dahmani--Guirardel--Osin, Definition
4.40), in the word metric at the identity basepoint.

If some translate `g·H_λ` and some `H_μ` have orbits that come `ε`-close along a
set of diameter at least `R`, then the two indices agree and `g` already lies in
the subgroup.  See the module header for the two transcription choices and for
the model tests. -/
def IsGeometricallySeparated {G : Type u} [Group G] {Λ : Type w} (A : Alphabet G)
    (K : Λ → Subgroup G) : Prop :=
  ∀ eps : ℕ, ∃ R : ℕ, ∀ (g : G) (lam mu : Λ),
    (∀ D : ℕ, D < R → ∃ a b : G, a ∈ K mu ∧ b ∈ K mu ∧
      D ≤ wordDist A.carrier a b ∧
      (∃ c : G, c ∈ K lam ∧ wordDist A.carrier a (g * c) ≤ eps) ∧
      (∃ c : G, c ∈ K lam ∧ wordDist A.carrier b (g * c) ≤ eps)) →
    lam = mu ∧ g ∈ K lam

/-! ## Model test: the trivial family -/

/-- **The trivial family is geometrically separated**, at `R = 2`.

Two elements of `⊥` are both `1`, so their distance is `0` and no `D ≥ 1`
witnesses the hypothesis.  See the module header for why `R = 1` would *not*
work, which is what makes this test informative rather than decorative. -/
theorem isGeometricallySeparated_bot {G : Type u} [Group G] {Λ : Type w}
    (A : Alphabet G) :
    IsGeometricallySeparated A (fun _ : Λ => (⊥ : Subgroup G)) := by
  intro _eps
  refine ⟨2, ?_⟩
  intro g lam mu hhyp
  obtain ⟨a, b, ha, hb, hab, -, -⟩ := hhyp 1 (by omega)
  have ha1 : a = 1 := Subgroup.mem_bot.mp ha
  have hb1 : b = 1 := Subgroup.mem_bot.mp hb
  rw [ha1, hb1, wordDist_self] at hab
  exact absurd hab (by omega)

/-! ## Model test: the full family -/

/-- **The word metric of the free group's basis alphabet is unbounded**, which
is what the second model test needs of the ambient. -/
theorem unbounded_freeGroupAlphabet (D : ℕ) :
    ∃ a b : FreeGroup (Fin 2),
      D ≤ wordDist (GGT.freeGroupAlphabet (Fin 2)).carrier a b := by
  refine ⟨1, (FreeGroup.of (0 : Fin 2)) ^ D, ?_⟩
  rw [wordDist_one_left]
  have h := GGT.le_wordNorm_zpow_of (a := (0 : Fin 2)) (b := (1 : Fin 2))
    (by decide) (D : ℤ)
  rw [zpow_natCast] at h
  simpa using h

/-- **The full family is not geometrically separated**, whenever the word metric
is unbounded and the index type has two distinct elements.

Every clause of the hypothesis is satisfiable at `⊤` — the approximation
clauses by `c = g⁻¹ a`, the diameter clause by unboundedness — so the
implication is forced to deliver `λ = μ`, which is false at `false ≠ true`.

This is the test with content: `⊤` is never hyperbolically embedded when
infinite, so a separation predicate that accepted it would be strong enough to
contradict a theorem already in the tree. -/
theorem not_isGeometricallySeparated_top {G : Type u} [Group G] (A : Alphabet G)
    (hunb : ∀ D : ℕ, ∃ a b : G, D ≤ wordDist A.carrier a b) :
    ¬ IsGeometricallySeparated A (fun _ : Bool => (⊤ : Subgroup G)) := by
  intro h
  obtain ⟨R, hR⟩ := h 0
  have hkey : (false : Bool) = true := by
    refine (hR 1 false true ?_).1
    intro D _hD
    obtain ⟨a, b, hab⟩ := hunb D
    refine ⟨a, b, Subgroup.mem_top _, Subgroup.mem_top _, hab, ?_, ?_⟩
    · exact ⟨a, Subgroup.mem_top _, by rw [one_mul, wordDist_self]⟩
    · exact ⟨b, Subgroup.mem_top _, by rw [one_mul, wordDist_self]⟩
  exact absurd hkey (by decide)

/-- The second model test, run against an actual alphabet rather than against a
hypothesis nothing is known to satisfy. -/
theorem not_isGeometricallySeparated_top_free :
    ¬ IsGeometricallySeparated (GGT.freeGroupAlphabet (Fin 2))
      (fun _ : Bool => (⊤ : Subgroup (FreeGroup (Fin 2)))) :=
  not_isGeometricallySeparated_top _ unbounded_freeGroupAlphabet

end HullSC
end GroupApproximation
