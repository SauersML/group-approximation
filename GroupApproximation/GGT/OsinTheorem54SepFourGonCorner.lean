import GroupApproximation.GGT.OsinTheorem54SepFourGonSide
import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# The corner the side-to-polygon bridge did not cover

`isComp_fourGon_of_isComp_side` carries a component of the long side `q` to a
component of the quadrilateral under the hypothesis
`k < q.length ∨ 0 < r.length`.  That hypothesis excludes one configuration: the
run reaches the very end of `q` and the short side `r` is empty, so the letter
following the run is the first letter of the reversed side `revWord s` and may
itself be an `H_λ`-letter.  The run then continues, and the component of the
quadrilateral is strictly longer than the component of the side.

The configuration is not a loss.  When the run continues into `revWord s` the
component of `q` and part of the side `s` are *one* run, so they are joined by
a product of `H_λ`-letters --- and that product is the connector, written down
with no appeal to any bound.  So the corner is discharged by a direct argument
rather than by the isolated-component machinery:

* `isComp_fourGon_of_isComp_side_of_end` --- the bridge again, with the end
  condition isolated as a hypothesis instead of derived from
  `k < q.length ∨ 0 < r.length`.  It does not need `r` to be spelled by base
  letters.
* `end_notIsCompOf_of_lt_or` --- that hypothesis does follow from
  `k < q.length ∨ 0 < r.length` with `r` base-spelled, which is why the landed
  form is a special case.
* `exists_connector_fourGon_run` --- the corner: if the run continues past `q`,
  the connector to `vertex 1 s (|s| - 1)` is the product of the run's letters.
* `exists_named_connector_of_deep` --- the packaging, with **no hypothesis on
  `k` and `r` at all**: a deep component of `q` has a named connector to
  another component of `q` or to a vertex of `s`.

The price of covering the corner is that the second branch no longer asserts
that the vertex of `s` it names *starts* a component of the quadrilateral: in
the corner it does not, being interior to the run that began in `q`.  Where
that clause is wanted, `exists_other_component_of_deep` still supplies it under
the `k < q.length ∨ 0 < r.length` hypothesis.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The bridge, with the end condition as a hypothesis -/

/-- **A component of the side is a component of the quadrilateral**, given
directly that the run does not continue past the end of the side. -/
theorem isComp_fourGon_of_isComp_side_of_end (p q r s : List (RelLetter G Λ))
    (lam : Λ) (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x) {i k : ℕ}
    (hcomp : IsComp lam q i k)
    (hend : ∀ hn : p.length + k < (p ++ q ++ r ++ revWord s).length,
      ¬ ((p ++ q ++ r ++ revWord s)[p.length + k]'hn).IsCompOf lam) :
    IsComp lam (p ++ q ++ r ++ revWord s) (p.length + i) (p.length + k) := by
  obtain ⟨hik, hkq, hrange, hpre, -⟩ := hcomp
  refine ⟨by omega, ?_, ?_, ?_, hend⟩
  · rw [length_fourGon]
    omega
  · intro j hj1 hj2 hj
    have hj' : j - p.length < q.length := by omega
    rw [getElem_fourGon_q p q r s hj' (by omega) hj]
    exact hrange (j - p.length) (by omega) (by omega) hj'
  · intro j hji hj hc
    by_cases hi0 : 0 < i
    · have hj' : i - 1 < q.length := by omega
      rw [getElem_fourGon_q p q r s hj' (by omega) hj] at hc
      exact hpre (i - 1) (by omega) hj' hc
    · have hjp : j < p.length := by omega
      obtain ⟨x, hx⟩ := hp _ (getElem_mem_fourGon_p p q r s hjp hj)
      rw [hx] at hc
      exact hc

/-- **The end condition holds in the covered cases**, so the landed bridge is
the special case of the one above. -/
theorem end_notIsCompOf_of_lt_or (p q r s : List (RelLetter G Λ)) (lam : Λ)
    (hr : ∀ a ∈ r, ∃ x : G, a = RelLetter.base x) {i k : ℕ}
    (hcomp : IsComp lam q i k) (hk : k < q.length ∨ 0 < r.length) :
    ∀ hn : p.length + k < (p ++ q ++ r ++ revWord s).length,
      ¬ ((p ++ q ++ r ++ revWord s)[p.length + k]'hn).IsCompOf lam := by
  obtain ⟨-, hkq, -, -, hpost⟩ := hcomp
  intro hkl hc
  by_cases hklt : k < q.length
  · rw [getElem_fourGon_q p q r s hklt rfl hkl] at hc
    exact hpost hklt hc
  · have hrpos : 0 < r.length := by
      rcases hk with h | h
      · omega
      · exact h
    obtain ⟨x, hx⟩ :=
      hr _ (getElem_mem_fourGon_r p q r s (by omega) (by omega) hkl)
    rw [hx] at hc
    exact hc

/-! ## The corner: the run continues into the reversed side -/

/-- **When the run continues past the end of `q`, the connector is the run
itself.**

The component of `q` and an initial stretch of the reversed side `s` are one
run of `H_λ`-letters, so the product of that run joins them, and it lies in
`H_λ` because every letter of it does.  Nothing is bounded and nothing is
cited: this is `span_mem_fam` applied across the corner, then read in the
coordinates of the two long sides. -/
theorem exists_connector_fourGon_run (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ))
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (hlet : ∀ a ∈ (p ++ q ++ r ++ revWord s), D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam q i k) (hkq : k = q.length) (hr0 : r.length = 0)
    (hn : p.length + k < (p ++ q ++ r ++ revWord s).length)
    (hc : ((p ++ q ++ r ++ revWord s)[p.length + k]'hn).IsCompOf lam) :
    ∃ h : G, h ∈ D.fam lam ∧
      RelLetter.listVal p * vertex (1 : G) q i * h
        = vertex (1 : G) s (s.length - 1) := by
  obtain ⟨hik, hkl, hrange, -, -⟩ := hcomp
  have hW : (p ++ q ++ r ++ revWord s).length
      = p.length + q.length + r.length + s.length := length_fourGon p q r s
  have hs : 0 < s.length := by
    rw [hW] at hn
    omega
  have hiq : i ≤ q.length := by omega
  have hbound : p.length + q.length + r.length + 1
      ≤ (p ++ q ++ r ++ revWord s).length := by
    rw [hW]
    omega
  have hrun : ∀ j : ℕ, p.length + i ≤ j →
      j < p.length + q.length + r.length + 1 →
      ∀ hj : j < (p ++ q ++ r ++ revWord s).length,
        ((p ++ q ++ r ++ revWord s)[j]'hj).IsCompOf lam := by
    intro j hj1 hj2 hj
    by_cases hjq : j < p.length + q.length
    · have hj' : j - p.length < q.length := by omega
      rw [getElem_fourGon_q p q r s hj' (by omega) hj]
      exact hrange (j - p.length) (by omega) (by omega) hj'
    · have hje : j = p.length + k := by omega
      subst hje
      exact hc
  have hspan := span_mem_fam D lam 1 hlet (p.length + q.length + r.length + 1)
    hbound (p.length + i) (by omega) hrun
  have hidx : p.length + q.length + r.length + 1
      = p.length + q.length + r.length + (s.length - (s.length - 1)) := by
    omega
  rw [vertex_fourGon_side p q r s 1 hiq, hidx,
    vertex_fourGon_opposite_closed p q r s hclose (s.length - 1),
    one_mul] at hspan
  exact ⟨(RelLetter.listVal p * vertex (1 : G) q i)⁻¹ *
    vertex (1 : G) s (s.length - 1), hspan, by group⟩

/-! ## The packaging, with no hypothesis on the corner -/

/-- **A deep component of one long side has a named connector**, with no
hypothesis on where the run ends.

Either the run stops inside `q`, and the component of `q` is a component of the
quadrilateral, so Osin's Lemma 4.2 applies and the component is not isolated;
or the run continues past `q`, which forces `k = |q|` and `r` empty and hands
the connector over directly.  The two cases are decided by the one condition
that matters, whether the polygon letter at the end of the run is an
`H_λ`-letter, and neither needs the caller to know which holds.

`IsolatedComponentBound` is the leading binder, as in
`exists_other_component_of_deep`; the corner branch does not use it.

**Warning.**  The connector this produces joins two component STARTS, and
start-to-start connectors are **not bounded by any polygon statement** ---
fp-geometry's witness `[comp lam h, base x, base x⁻¹, comp lam h⁻¹]` is a
`(1,0)`-quasi-geodesic 4-gon whose two components are connected with
start-to-start element `h`, ranging over all of `H_lam` against a finite
`relBall`.  Only the innermost END-to-START element is bounded (their
Lemma 4.21).  A consumer needing a bounded connector must match on
`(vertex 1 s j)⁻¹ * (listVal p * vertex 1 q k)`, with `k` the component END. -/
theorem exists_named_connector_of_deep (D : RelGenSet G Λ)
    (hbound : IsolatedComponentBound (IsQuasiGeodesicPolygon D) D) (lam : Λ)
    {mu b : ℝ} (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho : ℕ) (p q r s : List (RelLetter G Λ)),
      RelLetter.listVal s
          = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r →
      (∀ a ∈ (p ++ q ++ r ++ revWord s), D.IsLetter a) →
      (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
      (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
      IsQuasiGeodesicPolygon D mu b n 1 (p ++ q ++ r ++ revWord s) →
      ∀ i k : ℕ, IsComp lam q i k → C * n ≤ rho →
        (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k ∉ D.relBall lam rho →
          (∃ i' : ℕ, i' ≤ q.length ∧ i' ≠ i ∧ ∃ h : G, h ∈ D.fam lam ∧
              vertex (1 : G) q i * h = vertex (1 : G) q i')
            ∨ (∃ j : ℕ, j ≤ s.length ∧ ∃ h : G, h ∈ D.fam lam ∧
              RelLetter.listVal p * vertex (1 : G) q i * h
                = vertex (1 : G) s j) := by
  obtain ⟨C, hCpos, hC⟩ := hbound mu b hmu hb
  refine ⟨C, hCpos, ?_⟩
  intro n rho p q r s hclose hlet hp hr hpoly i k hcomp hrho hdeep
  have hiq : i ≤ q.length := by
    obtain ⟨hik, hkl, -, -, -⟩ := hcomp
    omega
  have hkl : k ≤ q.length := by
    obtain ⟨-, hkl, -, -, -⟩ := hcomp
    exact hkl
  by_cases hend : ∀ hn : p.length + k < (p ++ q ++ r ++ revWord s).length,
      ¬ ((p ++ q ++ r ++ revWord s)[p.length + k]'hn).IsCompOf lam
  · have hbridge :=
      isComp_fourGon_of_isComp_side_of_end p q r s lam hp hcomp hend
    have hnotiso : ¬ IsIsolated D.fam lam 1 (p ++ q ++ r ++ revWord s)
        (p.length + i) := by
      intro hiso
      have hspan := hC n 1 (p ++ q ++ r ++ revWord s) hpoly lam (p.length + i)
        (p.length + k) hbridge hiso
      rw [span_fourGon_side p q r s hiq hkl] at hspan
      exact hdeep (relBall_mono_radius D lam hrho hspan)
    rcases exists_other_component_fourGon D lam p q r s hclose hp hr hiq
        ⟨p.length + k, hbridge⟩ hnotiso with
      ⟨i', hi', hne, -, hconn⟩ | ⟨j, hj, -, hconn⟩
    · exact Or.inl ⟨i', hi', hne, hconn⟩
    · exact Or.inr ⟨j, hj, hconn⟩
  · have hex : ∃ hn : p.length + k < (p ++ q ++ r ++ revWord s).length,
        ((p ++ q ++ r ++ revWord s)[p.length + k]'hn).IsCompOf lam := by
      by_contra hcon
      refine hend ?_
      intro hn hcc
      exact hcon ⟨hn, hcc⟩
    obtain ⟨hn, hc⟩ := hex
    have hkq : k = q.length := by
      by_contra hne
      obtain ⟨-, -, -, -, hpost⟩ := hcomp
      have hklt : k < q.length := by omega
      rw [getElem_fourGon_q p q r s hklt rfl hn] at hc
      exact hpost hklt hc
    have hr0 : r.length = 0 := by
      by_contra hne
      obtain ⟨x, hx⟩ :=
        hr _ (getElem_mem_fourGon_r p q r s (by omega) (by omega) hn)
      rw [hx] at hc
      exact hc
    exact Or.inr ⟨s.length - 1, by omega,
      exists_connector_fourGon_run D lam p q r s hclose hlet hcomp hkq hr0
        hn hc⟩

end OsinComponents
end GGT
end GroupApproximation
