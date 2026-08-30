import GroupApproximation.GGT.HullSCCyclicDisjointness
import GroupApproximation.GGT.HullSCRelatorSeparation2ConeOff

/-!
# Hull's §5 for a pair, with everything but the embedding discharged

`HullSC.ExistsHypEmbeddedConeOff₂` -- Hull's Corollary 5.7 with Lemma 5.8, over
a pair -- asks for five things at once: two subgroups **inside** the suitable
`N`, whose cone-off over Hull's alphabet is hyperbolically embedded, containing
independent loxodromic elements, and meeting trivially.

**Four of the five are free**, and this module proves it.  Take the subgroups to
be the cyclic groups on the two loxodromics themselves:

* `⟨hᵢ⟩ ≤ N` because `hᵢ ∈ N`, which is `Subgroup.zpowers_le`;
* `hᵢ ∈ ⟨hᵢ⟩`;
* the loxodromy and the independence are hypotheses about the `hᵢ` and are
  carried through unchanged;
* **Hull's (W4)**, that the two subgroups meet trivially, is
  `GGT.Elementary.zpowers_disjoint_of_independent` -- a common element is
  `h₀^p = h₁^q`, and nonzero exponents contradict independence.

And the two loxodromics themselves are free: `Suitable` *is*
`ActsNonElementarily N` together with the finite-subgroup clause, and the first
conjunct hands back exactly a pair of independent loxodromics in `N`.

So the citation reduces to its one geometric clause,
`existsHypEmbeddedConeOff₂_of_zpowers`:

> for a suitable `N` **there are** independent loxodromic `h₀, h₁ ∈ N` with
> `{⟨h₀⟩, ⟨h₁⟩} ↪_h (G, A)`.

## The existential is not decoration: the universal form is FALSE

An earlier version of this module also offered the clause with the pair
universally quantified -- *for **any** two independent loxodromics the cone-off
along their cyclic subgroups is hyperbolically embedded* -- as the "sharpest"
residue.  **That statement is false**, and the second half of this module proves
the mechanism that kills it.

`subset_relBall_three_of_normalizes`: if a base letter `a` of the relative
generating set lies **outside** `H λ` but **normalises** it, then every element
of `H λ` is at relative distance at most three from `1`.  The word is
`a · (a⁻¹ k a) · a⁻¹`, which spells `k`, is admissible, and reads its one
`λ`-letter at the vertex `a`, which is not in `H λ` -- so it avoids `Γ_{H λ}`
and the avoidance condition, which is the whole content of the relative metric,
never bites.  With `H λ` infinite, local finiteness fails.

The cyclic case is `not_isHyperbolicallyEmbedded_zpowers_pow`: coning off
`⟨a^n⟩` for `n ≥ 2` along an alphabet that contains `a` is never hyperbolically
embedded, because `a` normalises `⟨a^n⟩` and is not in it.

**The witness.**  Take `G = F₂` free on `{a, b}` with `A = {a, a⁻¹, b, b⁻¹}`:
`Γ(G,A)` is a tree, so it is `0`-hyperbolic, the action is free and hence
acylindrical, and `a`, `b` are independent loxodromics -- an honest
`HullGeneratingSet`.  Now `a²` and `b` are independent loxodromics too, and the
theorem below says `{⟨a²⟩, ⟨b⟩}` is **not** hyperbolically embedded over `A`:
the relative ball of radius three about `1` in `⟨a²⟩` is all of `⟨a²⟩`, by the
word `a · a^{2m} · a⁻¹`.  So the universally quantified clause fails at
`(F₂, A, (a², b))`.  Only the exhibition of that `HullGeneratingSet` is left
unformalised here, and it is the acylindricity of a free action on a tree.

## What this says about the remaining clause, and about the descent

The pair has to be **chosen**, and what the choice must achieve is
`⟨hᵢ⟩ = E(hᵢ)`: the failure above is exactly the gap between `⟨a²⟩` and its
elementary closure `⟨a⟩`, and the offending word travels through the letter `a`
of the closure that the smaller subgroup omits.  Over a torsion-free ambient
group that is root-freeness of `hᵢ`, and it is the true content of Hull's
Lemma 5.8 -- which therefore does **not** come off the board.

The same example refutes the finite-index descent that would otherwise have
replaced Lemma 5.8: `{⟨a⟩, ⟨b⟩} ↪_h (F₂, A)` holds -- they are free factors --
while `{⟨a²⟩, ⟨b⟩}` does not, and `⟨a²⟩ ≤ ⟨a⟩` has index two.  **A finite-index
subgroup of a hyperbolically embedded subgroup need not be hyperbolically
embedded**, over any base, so no enlargement by a finite transversal repairs it
and `GGT.DGOCorollary427` has nothing to strip.  The descent goes up, not down.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The four free clauses -/

/-- **The two independent loxodromics of a suitable subgroup**, which is the
first conjunct of Hull's Definition 1.4 read back. -/
theorem exists_independent_lox_of_suitable {G : Type u} [Group G]
    {A : Alphabet G} {N : Subgroup G} (hN : Suitable A N) :
    ∃ g : Bool → G, (∀ b : Bool, g b ∈ N) ∧
      (∀ b : Bool, IsLoxodromic (g b) (Cayley.base A)) ∧
        Independent (g false) (g true) (Cayley.base A) := by
  obtain ⟨a, ha, b, hb, halox, hblox, hind⟩ := hN.actsNonElementarily
  refine ⟨fun c => bif c then b else a, ?_, ?_, hind⟩
  · intro c
    cases c
    · exact ha
    · exact hb
  · intro c
    cases c
    · exact halox
    · exact hblox

/-- **Hull's §5 for a pair, from its geometric clause alone.**

The hypothesis is the embedding for *some* pair and nothing else; the four
remaining clauses of `ExistsHypEmbeddedConeOff₂` are discharged here.  The
existential over the pair is essential -- see the module header, and
`not_isHyperbolicallyEmbedded_zpowers_pow` below. -/
theorem existsHypEmbeddedConeOff₂_of_zpowers
    (hemb : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G)
      {N : Subgroup G}, Suitable A.alphabet N →
        ∃ g : Bool → G, (∀ b : Bool, g b ∈ N) ∧
          (∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet)) ∧
            Independent (g false) (g true) (Cayley.base A.alphabet) ∧
              (coneOffFamily A.alphabet
                (fun b => Subgroup.zpowers (g b))).IsHyperbolicallyEmbedded) :
    ExistsHypEmbeddedConeOff₂.{u} := by
  intro G _ A N hN
  obtain ⟨g, hgN, hglox, hind, hembK⟩ := hemb A hN
  refine ⟨fun b => Subgroup.zpowers (g b), ?_, hembK, g, ?_, hglox, hind, ?_⟩
  · intro b
    exact Subgroup.zpowers_le.mpr (hgN b)
  · intro b
    exact Subgroup.mem_zpowers (g b)
  · exact GGT.Elementary.zpowers_disjoint_of_independent
      (isIsometricAction_cayley A.alphabet) (hglox false) hind

/-! ## Why the pair has to be chosen -/

/-- **A base letter outside a family member that normalises it collapses the
relative metric.**

Every `k ∈ H λ` is spelled by `a · (a⁻¹ k a) · a⁻¹`: three admissible letters,
whose one `λ`-letter is read at the vertex `a`, which is outside `H λ`.  So the
word avoids `Γ_{H λ}` and `k` lies in the relative ball of radius three.

This is the length-three companion of
`GGT.RelGenSet.not_isHyperbolicallyEmbedded_of_fam_subset_base`, which is the
same phenomenon at length one, and it belongs beside it. -/
theorem subset_relBall_three_of_normalizes {G : Type u} [Group G] {Λ : Type w}
    (D : GGT.RelGenSet G Λ) (lam : Λ) {a : G} (ha : a ∈ D.base)
    (hainv : a⁻¹ ∈ D.base) (hnot : a ∉ D.fam lam)
    (hnorm : ∀ k ∈ D.fam lam, a⁻¹ * k * a ∈ D.fam lam) :
    (D.fam lam : Set G) ⊆ D.relBall lam 3 := by
  intro k hk
  have hkmem : k ∈ D.fam lam := hk
  have hconj : a⁻¹ * k * a ∈ D.fam lam := hnorm k hkmem
  rw [GGT.RelGenSet.mem_relBall]
  refine ⟨hkmem, [GGT.RelLetter.base a, GGT.RelLetter.comp lam (a⁻¹ * k * a),
    GGT.RelLetter.base a⁻¹], ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hconj
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hainv
    exact absurd hx (by simp)
  · show a * ((a⁻¹ * k * a) * (a⁻¹ * 1)) = k
    group
  · refine ⟨?_, ?_, ?_, trivial⟩
    · rintro ⟨hc, -⟩
      exact hc
    · rintro ⟨-, hv⟩
      rw [one_mul] at hv
      exact hnot hv
    · rintro ⟨hc, -⟩
      exact hc
  · simp

/-- **So such a family is not hyperbolically embedded**, once the member it
collapses is infinite. -/
theorem not_isHyperbolicallyEmbedded_of_normalizes {G : Type u} [Group G]
    {Λ : Type w} (D : GGT.RelGenSet G Λ) (lam : Λ) {a : G} (ha : a ∈ D.base)
    (hainv : a⁻¹ ∈ D.base) (hnot : a ∉ D.fam lam)
    (hnorm : ∀ k ∈ D.fam lam, a⁻¹ * k * a ∈ D.fam lam)
    (hinf : (D.fam lam : Set G).Infinite) : ¬ D.IsHyperbolicallyEmbedded := by
  intro hD
  exact hinf (Set.Finite.subset (hD.locallyFinite lam 3)
    (subset_relBall_three_of_normalizes D lam ha hainv hnot hnorm))

/-- **Coning off a proper power is never hyperbolically embedded**, along an
alphabet containing the root.

`a` normalises `⟨a^n⟩` and, having infinite order, does not lie in it for
`n ≥ 2`; so `subset_relBall_three_of_normalizes` applies.  This is what makes
the universally quantified form of the residual clause false: `a^n` is
loxodromic whenever `a` is, and independence is untouched by passing to a
power. -/
theorem not_isHyperbolicallyEmbedded_zpowers_pow {G : Type u} [Group G]
    {Λ : Type w} (A : Alphabet G) (K : Λ → Subgroup G) (lam : Λ) {a : G}
    (ha : a ∈ A.carrier) (hord : ¬ IsOfFinOrder a) {n : ℕ} (hn : 2 ≤ n)
    (hK : K lam = Subgroup.zpowers (a ^ n)) :
    ¬ (coneOffFamily A K).IsHyperbolicallyEmbedded := by
  have hinj : Function.Injective (fun m : ℤ => a ^ m) :=
    injective_zpow_iff_not_isOfFinOrder.mpr hord
  have hpow : ¬ IsOfFinOrder (a ^ n) := by
    intro hfin
    obtain ⟨m, hm, hpm⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    refine hord (isOfFinOrder_iff_pow_eq_one.mpr ⟨n * m, ?_, ?_⟩)
    · exact Nat.mul_pos (by omega) hm
    · rw [pow_mul]
      exact hpm
  refine not_isHyperbolicallyEmbedded_of_normalizes _ lam ha
    (A.symmetricGenerating.inv_mem a ha) ?_ ?_ ?_
  · rw [coneOffFamily_fam, hK]
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hjj : a ^ ((n : ℤ) * j) = a ^ (1 : ℤ) := by
      rw [zpow_mul, zpow_natCast, hj, zpow_one]
    have hmul : (n : ℤ) * j = 1 := hinj hjj
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hmul with h1 | h1
    · omega
    · omega
  · rw [coneOffFamily_fam, hK]
    intro k hk
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hc : Commute a ((a ^ n) ^ j) := ((Commute.refl a).pow_right n).zpow_right j
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    rw [← hj, mul_assoc, ← hc.eq, inv_mul_cancel_left]
  · rw [coneOffFamily_fam, hK]
    exact GGT.infinite_zpowers_of_not_isOfFinOrder hpow

end HullSC
end GroupApproximation
