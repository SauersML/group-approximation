import GroupApproximation.GGT.GeodesicChainThrough
import GroupApproximation.GGT.GuessingGeodesicsUniform
import GroupApproximation.GGT.OsinLemma55GuessingGeodesics

/-!
# Bowditch's criterion, proved; and Osin's Lemma 5.5 with it

`GGT/GuessingGeodesicsUniform.lean` ends with one constant `s` bounding every
path vertex against every geodesic, at every scale.  This module spends that
bound on the remaining half --- every point of a geodesic is close to the path
--- and reads the two together as slim triangles, which
`Hyperbolic.isFourPointHyperbolic_of_isSlimTriangles` turns into the four-point
condition.  That discharges `GuessingGeodesics`, and with it
`osinLemma55_of_guessingGeodesics` becomes unconditional.

## Where the connectivity clause is spent

`GuessingData.step` is used **once in this file and nowhere else in the proof**,
in `exists_path_near_chain`.  Index each path vertex by a geodesic vertex within
`s` of it; consecutive path vertices are one step apart, so the indices move by
at most `2s + 1`, and an index cannot jump over `m` without landing within `2s`
of it.  Take the first path vertex whose index has reached `m`: it is within
`2s + s = 3s` of `c m`.

The `ℤ²` configuration recorded in `GGT/GuessingGeodesicsSubdivision.lean`
satisfies every other clause and is not hyperbolic, so this really is the step
that carries the criterion's content.  Everything before it --- subdivision,
bootstrap, closure --- runs on `short` and `thin` alone.

## The constants

`3s` from the crossing, `K` from one application of `thin`, and `s` again from
the bound at the third vertex give slim triangles at `4s + K`, hence the
four-point condition at `12s + 3K + 1`.

## What it cost

The estimate when this build was scoped was 1200--2500 lines, and the nine
modules of the criterion come to 1204 --- the bottom of the range rather than
half of it, and a good deal of that is prose.  What the recon rounds bought was
not a smaller number but a straighter path: the mechanism read before writing
(the recursion is self-applied, not halving), the outer estimates stated as
inequalities rather than contradictions, and each layer's interfaces fixed
before the layer above it was written.  Of the nine modules, one needed a second
probe.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## The first crossing -/

/-- **Every geodesic vertex is within `3s` of a path vertex.**

The only place `GuessingData.step` is used.  See the module header. -/
theorem exists_path_near_chain {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} {D : GuessingData S K} {s : ℕ} (hs : ∀ n : ℕ, Bnd D n s) {x y : G}
    {c : ℕ → G} (hc0 : c 0 = x) (hcN : c (wordDist S x y) = y)
    (hchain : IsGeodesicChain S c (wordDist S x y)) {m : ℕ}
    (hm : m ≤ wordDist S x y) :
    ∃ i : ℕ, i ≤ D.len x y ∧ wordDist S (c m) (D.path x y i) ≤ 3 * s := by
  have hb := hs (wordDist S x y) x y le_rfl c hc0 hcN hchain
  have key : ∀ i : ℕ, i ≤ D.len x y →
      (∃ i' : ℕ, i' ≤ D.len x y ∧
          wordDist S (c m) (D.path x y i') ≤ 3 * s) ∨
        (∃ k : ℕ, k ≤ wordDist S x y ∧ k < m ∧
          wordDist S (D.path x y i) (c k) ≤ s) := by
    intro i
    induction i with
    | zero =>
        intro h0
        obtain ⟨k, hkN, hkd⟩ := hb 0 h0
        rcases Nat.lt_or_ge k m with hkm | hkm
        · exact Or.inr ⟨k, hkN, hkm, hkd⟩
        · refine Or.inl ⟨0, h0, ?_⟩
          rw [D.start] at hkd ⊢
          have hxk := hchain 0 k (Nat.zero_le k) hkN
          rw [hc0] at hxk
          have hxm := hchain 0 m (Nat.zero_le m) hm
          rw [hc0] at hxm
          have hcomm := wordDist_comm hS (c m) x
          omega
    | succ i ih =>
        intro hi1
        rcases ih (by omega) with hleft | ⟨k', hk'N, hk'm, hk'd⟩
        · exact Or.inl hleft
        · obtain ⟨k, hkN, hkd⟩ := hb (i + 1) hi1
          rcases Nat.lt_or_ge k m with hkm | hkm
          · exact Or.inr ⟨k, hkN, hkm, hkd⟩
          · refine Or.inl ⟨i + 1, hi1, ?_⟩
            have hstep := D.step x y i (by omega)
            have hck := hchain k' k (by omega) hkN
            have hcm := hchain m k hkm hkN
            have t1 := wordDist_triangle hS (c k') (D.path x y i) (c k)
            have t2 :=
              wordDist_triangle hS (D.path x y i) (D.path x y (i + 1)) (c k)
            have tfin := wordDist_triangle hS (c m) (c k) (D.path x y (i + 1))
            have hcomm1 := wordDist_comm hS (c k') (D.path x y i)
            have hcomm2 := wordDist_comm hS (c k) (D.path x y (i + 1))
            omega
  rcases key (D.len x y) le_rfl with hleft | ⟨k, hkN, hkm, hkd⟩
  · exact hleft
  · refine ⟨D.len x y, le_rfl, ?_⟩
    rw [D.finish] at hkd ⊢
    have hky := hchain k (wordDist S x y) hkN le_rfl
    rw [hcN] at hky
    have hmy := hchain m (wordDist S x y) hm le_rfl
    rw [hcN] at hmy
    have hcomm := wordDist_comm hS y (c k)
    omega

/-! ## Slim triangles -/

/-- **A guessing-geodesics family makes triangles slim**, at `4s + K`. -/
theorem isSlimTriangles_of_guessingData {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {K : ℕ} (D : GuessingData S K) {s : ℕ}
    (hs : ∀ n : ℕ, Bnd D n s) :
    Hyperbolic.IsSlimTriangles S (4 * s + K) := by
  intro x y z p hp
  obtain ⟨c, hc0, hcN, hchain, hcp⟩ := exists_isGeodesicChain_through hS hp
  have hpN : wordDist S x p ≤ wordDist S x y := by
    have h : wordDist S x p + wordDist S p y = wordDist S x y := hp
    omega
  obtain ⟨i, hiL, hid⟩ := exists_path_near_chain hS hs hc0 hcN hchain hpN
  rw [hcp] at hid
  obtain ⟨i', hi'⟩ := D.thin x y z i hiL
  rcases hi' with ⟨hi'le, hi'd⟩ | ⟨hi'le, hi'd⟩
  · obtain ⟨c', hc'0, hc'N, hc'chain⟩ := exists_isGeodesicChain hS x z
    obtain ⟨k, hkN, hkd⟩ :=
      hs (wordDist S x z) x z le_rfl c' hc'0 hc'N hc'chain i' hi'le
    refine Or.inl ⟨c' k, ?_, ?_⟩
    · have hb := hc'chain.isBetween hkN
      rw [hc'0, hc'N] at hb
      exact hb
    · have t1 := wordDist_triangle hS p (D.path x y i) (c' k)
      have t2 :=
        wordDist_triangle hS (D.path x y i) (D.path x z i') (c' k)
      omega
  · obtain ⟨c', hc'0, hc'N, hc'chain⟩ := exists_isGeodesicChain hS z y
    obtain ⟨k, hkN, hkd⟩ :=
      hs (wordDist S z y) z y le_rfl c' hc'0 hc'N hc'chain i' hi'le
    refine Or.inr ⟨c' k, ?_, ?_⟩
    · have hb := hc'chain.isBetween hkN
      rw [hc'0, hc'N] at hb
      exact hb
    · have t1 := wordDist_triangle hS p (D.path x y i) (c' k)
      have t2 :=
        wordDist_triangle hS (D.path x y i) (D.path z y i') (c' k)
      omega

/-! ## The criterion, and Lemma 5.5 -/

/-- **The four-point condition, from a guessing-geodesics family.** -/
theorem exists_isFourPointHyperbolic_of_guessingData {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {K : ℕ} (D : GuessingData S K) :
    ∃ δ : ℕ, Hyperbolic.IsFourPointHyperbolic S δ := by
  obtain ⟨s, hs⟩ := exists_uniform_bnd hS D
  exact ⟨3 * (4 * s + K) + 1,
    Hyperbolic.isFourPointHyperbolic_of_isSlimTriangles hS
      (isSlimTriangles_of_guessingData hS D hs)⟩

/-- **Bowditch's guessing-geodesics criterion**, proved.

`GGT/OsinLemma55GuessingGeodesics.lean` declared this as the one statement that
build assumed; it is now a theorem. -/
theorem guessingGeodesics : GuessingGeodesics.{u} := by
  intro H _ S hS K len path hstart hfinish hstep hshort hthin
  exact exists_isFourPointHyperbolic_of_guessingData hS
    ⟨len, path, hstart, hfinish, hstep, hshort, hthin⟩

/-- **Osin's Lemma 5.5, unconditionally.**

`osinLemma55_of_guessingGeodesics` reduced it to the criterion; the criterion is
now proved, so the reduction may be read as a theorem.  Nothing in the §5
program owes this statement any longer. -/
theorem osinLemma55 : OsinLemma55.{u} :=
  osinLemma55_of_guessingGeodesics guessingGeodesics

end OsinEnlargement
end GGT
end GroupApproximation
