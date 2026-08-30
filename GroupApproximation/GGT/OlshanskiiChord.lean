import GroupApproximation.GGT.DGOWindmillQuasiconvex

/-!
# The dyadic chord lemma: a geodesic stays log-close to a broken line

This is the foundation of the reconstruction of Ol'shanskii's polygon
lemmas (Mat. Sb. **182** (1991), Lemmas 23 and 25), whose proofs appear in
none of the sources this repository can reach: Dahmani--Guirardel--Osin,
Hull, and Osin all state them with a citation to the untranslated original,
and Ol'shanskii's translated book carries only the diagrammatic technology.
The statements are reconstructed here from first principles, against the
repository's own four-point vocabulary.

**The lemma.**  Let `vs 0, vs 1, …, vs k` be points of a hyperbolic space,
joined consecutively by geodesic sides, with `k ≤ 2 ^ c`.  Then every point
of a geodesic chord from `vs 0` to `vs k` lies within `3δ · (c + 1)` of some
side.  The proof is the dyadic descent: a thin triangle at the middle vertex
`vs 2^(c-1)` moves the point onto a chord of half as many sides at a cost of
`3δ`, and after `c` halvings the chord *is* a side, where the same-endpoint
comparison spends the last `3δ`.

Two conventions, both forced by the landed vocabulary rather than chosen:
the sides arrive as explicit geodesic parametrisations (`IsGeodesicSegment`
functions), because the thin-triangle lemma consumes that form; and the
constant is `3δ` per level, not Ol'shanskii's `δ`, because the repository's
hyperbolicity is the four-point condition and its triangles are `3δ`-thin
(`exists_close_on_other_side_of_geodesic_triangle`).  Every consumer of the
reconstruction inherits that dilation, exactly as the windmill campaign's
re-derived budget does.

The space is asked to be geodesic only to *produce* the two half-chords of
the descent; the sides and the chord themselves are data.  On a Cayley
graph the hypothesis is supplied by the quotient model
(`isGeodesicRealisationQuot`), the same route the Morse discharge takes.
-/

namespace GroupApproximation
namespace Olshanskii

open GroupApproximation.HullGeometry
open GroupApproximation.DGOWindmill

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-- The sides of a broken line, as data: for each `i < k` a geodesic
parametrisation from `vs i` to `vs (i + 1)`. -/
def IsSideFamily (vs : ℕ → X) (sides : ℕ → ℝ → X) (k : ℕ) : Prop :=
  ∀ i < k,
    IsGeodesicSegment (sides i) 0 (dist (vs i) (vs (i + 1))) ∧
      sides i 0 = vs i ∧
        sides i (dist (vs i) (vs (i + 1))) = vs (i + 1)

theorem IsSideFamily.shift {vs : ℕ → X} {sides : ℕ → ℝ → X} {k m : ℕ}
    (h : IsSideFamily vs sides k) (hm : m ≤ k) :
    IsSideFamily (fun j => vs (m + j)) (fun j => sides (m + j)) (k - m) := by
  intro j hj
  have hlt : m + j < k := by omega
  have hstep := h (m + j) hlt
  have harg : m + j + 1 = m + (j + 1) := by omega
  rw [harg] at hstep
  exact hstep

/-- **The dyadic chord lemma.**  A geodesic chord across a broken line of at
most `2 ^ c` geodesic sides stays within `3δ · (c + 1)` of the union of the
sides.  Induction on `c`: the base case is the same-endpoint comparison of
two geodesics, and the step is one thin triangle at the vertex `vs 2^c`,
which costs `3δ` and halves the side count. -/
theorem exists_close_side_of_chord {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X) :
    ∀ c k : ℕ, 1 ≤ k → k ≤ 2 ^ c →
      ∀ (vs : ℕ → X) (sides : ℕ → ℝ → X), IsSideFamily vs sides k →
        ∀ g : ℝ → X, IsGeodesicSegment g 0 (dist (vs 0) (vs k)) →
          g 0 = vs 0 → g (dist (vs 0) (vs k)) = vs k →
            ∀ t ∈ Set.Icc (0 : ℝ) (dist (vs 0) (vs k)),
              ∃ i < k, ∃ s ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
                dist (g t) (sides i s) ≤ 3 * δ * ((c : ℝ) + 1) := by
  intro c
  induction c with
  | zero =>
    intro k hk1 hk2 vs sides hsides g hg hg0 hg1 t ht
    have hkeq : k = 1 := by
      have h2 : (2 : ℕ) ^ 0 = 1 := pow_zero 2
      omega
    subst hkeq
    obtain ⟨hside, hside0, hside1⟩ := hsides 0 (by omega)
    have hclose := exists_close_of_geodesic_same_endpoints hδ hδ0
      hg hg0 hg1 hside hside0 hside1 ht
    obtain ⟨s, hs, hdist⟩ := hclose
    refine ⟨0, by omega, s, hs, ?_⟩
    have hcast : 3 * δ * (((0 : ℕ) : ℝ) + 1) = 3 * δ := by norm_num
    rw [hcast]
    exact hdist
  | succ c ih =>
    intro k hk1 hk2 vs sides hsides g hg hg0 hg1 t ht
    by_cases hcase : k ≤ 2 ^ c
    · -- the smaller bound applies and is weakened by one level
      obtain ⟨i, hi, s, hs, hdist⟩ :=
        ih k hk1 hcase vs sides hsides g hg hg0 hg1 t ht
      refine ⟨i, hi, s, hs, le_trans hdist ?_⟩
      have hle : ((c : ℝ) + 1) ≤ ((c : ℝ) + 1 + 1) := by linarith
      have hnn : (0 : ℝ) ≤ 3 * δ := by linarith
      have hmul := mul_le_mul_of_nonneg_left hle hnn
      have hcast : (((c + 1 : ℕ)) : ℝ) + 1 = (c : ℝ) + 1 + 1 := by
        push_cast
        ring
      rw [hcast]
      exact hmul
    · -- split at the vertex `vs (2 ^ c)`
      have hm1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
      have hmk : 2 ^ c < k := by omega
      have hkm : k - 2 ^ c ≤ 2 ^ c := by
        have hpow : (2 : ℕ) ^ (c + 1) = 2 ^ c + 2 ^ c := by
          rw [pow_succ]
          omega
        omega
      have hkm1 : 1 ≤ k - 2 ^ c := by omega
      set m := 2 ^ c
      -- the two half-chords, from the geodesic hypothesis
      obtain ⟨gL, hgL, hgL0, hgL1⟩ := hgeo (vs 0) (vs m)
      obtain ⟨gR, hgR, hgR0, hgR1⟩ := hgeo (vs m) (vs k)
      -- one thin triangle moves `g t` onto a half-chord at cost `3δ`
      have htri := exists_close_on_other_side_of_geodesic_triangle hδ hδ0
        (A := vs 0) (B := vs m) (C := vs k)
        hg hg0 hg1 hgL hgL0 hgL1 hgR hgR0 hgR1 ht
      have hbound : ∀ p : X,
          (∃ i < k, ∃ s ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
            dist p (sides i s) ≤ 3 * δ * ((c : ℝ) + 1)) →
          dist (g t) p ≤ 3 * δ →
          ∃ i < k, ∃ s ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
            dist (g t) (sides i s) ≤ 3 * δ * (((c + 1 : ℕ) : ℝ) + 1) := by
        intro p hp hclose
        obtain ⟨i, hi, s, hs, hdist⟩ := hp
        refine ⟨i, hi, s, hs, ?_⟩
        have htriangle := dist_triangle (g t) p (sides i s)
        have hcast : (((c + 1 : ℕ)) : ℝ) + 1 = ((c : ℝ) + 1) + 1 := by
          push_cast
          ring
        rw [hcast]
        have hsum : dist (g t) p + dist p (sides i s)
            ≤ 3 * δ + 3 * δ * ((c : ℝ) + 1) := by
          exact add_le_add hclose hdist
        have hring : 3 * δ + 3 * δ * ((c : ℝ) + 1)
            = 3 * δ * (((c : ℝ) + 1) + 1) := by ring
        rw [hring] at hsum
        exact le_trans htriangle hsum
      rcases htri with ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩
      · -- left half: sides `0 … m - 1`, `m = 2 ^ c` of them
        have hsidesL : IsSideFamily vs sides m := by
          intro i hi
          exact hsides i (by omega)
        obtain ⟨i, hi, s', hs', hdist⟩ :=
          ih m hm1 (le_refl m) vs sides hsidesL gL hgL hgL0 hgL1 s hs
        exact hbound (gL s) ⟨i, by omega, s', hs', hdist⟩ hclose
      · -- right half: sides `m … k - 1`, at most `2 ^ c` of them, shifted
        have hsidesR := hsides.shift (le_of_lt hmk)
        have hvsk : vs (m + (k - m)) = vs k := by
          have harg : m + (k - m) = k := by omega
          rw [harg]
        -- the shifted chord is `gR`, whose endpoints are `vs m` and `vs k`
        have hgR1' : gR (dist (vs (m + 0)) (vs (m + (k - m))))
            = vs (m + (k - m)) := by
          have h0 : m + 0 = m := by omega
          rw [h0, hvsk]
          exact hgR1
        have hgR' : IsGeodesicSegment gR 0
            (dist (vs (m + 0)) (vs (m + (k - m)))) := by
          have h0 : m + 0 = m := by omega
          rw [h0, hvsk]
          exact hgR
        have hgR0' : gR 0 = vs (m + 0) := by
          have h0 : m + 0 = m := by omega
          rw [h0]
          exact hgR0
        have hs'' : s ∈ Set.Icc (0 : ℝ)
            (dist (vs (m + 0)) (vs (m + (k - m)))) := by
          have h0 : m + 0 = m := by omega
          rw [h0, hvsk]
          exact hs
        obtain ⟨i, hi, s', hs', hdist⟩ :=
          ih (k - m) hkm1 hkm (fun j => vs (m + j)) (fun j => sides (m + j))
            hsidesR gR hgR' hgR0' hgR1' s hs''
        have harg : m + i + 1 = m + (i + 1) := by omega
        refine hbound (gR s) ⟨m + i, by omega, s', ?_, ?_⟩ hclose
        · rw [harg]
          exact hs'
        · exact hdist

end Olshanskii
end GroupApproximation
