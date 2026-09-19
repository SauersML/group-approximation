import GroupApproximation.GGT.OsinTheorem54SepFourGon
import GroupApproximation.GGT.OsinTheorem54SepPolygon

/-!
# A component of a side is a component of the quadrilateral

`GGT/OsinTheorem54SepFourGon.lean` speaks of components of the polygon word
`p ++ q ++ r ++ revWord s`.  A caller has a component of the *side* `q` --- a
pair `(i,k)` with `IsComp lam q i k` --- and needs it to be a component of the
polygon, at `(|p| + i, |p| + k)`.

That is not automatic.  `IsComp` is a *maximal* run: it asserts that the letter
before the run and the letter at its end are not `H_λ`-letters, and in the
polygon those two letters may come from the neighbouring sides rather than from
`q`.  Both conditions are supplied by the short sides being spelled by base
letters:

* at the front, the letter before index `|p|` is the last letter of `p`, a base
  letter (and when `i > 0` it is still a letter of `q`, where maximality is
  already known);
* at the back, the letter at index `|p| + k` is the first letter of `r` when
  `k = |q|` --- again a base letter --- and a letter of `q` when `k < |q|`.

The one case that is *not* covered is `k = |q|` with `r` empty: the run then
continues into the reversed side `revWord s`, and the polygon component is
strictly longer than the side component.  So the hypothesis is
`k < q.length ∨ 0 < r.length`, which is exactly what excludes it, and it is a
real restriction rather than bookkeeping.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Reading a letter of the quadrilateral off its side -/

/-- **A letter of the quadrilateral in the `q`-block is a letter of `q`.** -/
theorem getElem_fourGon_q (p q r s : List (RelLetter G Λ)) {n j : ℕ}
    (hj : j < q.length) (hnj : n = p.length + j)
    (hn : n < (p ++ q ++ r ++ revWord s).length) :
    (p ++ q ++ r ++ revWord s)[n]'hn = q[j]'hj := by
  subst hnj
  have h1 : p.length + j < (p ++ q ++ r).length := by
    rw [List.length_append, List.length_append]
    omega
  have h2 : p.length + j < (p ++ q).length := by
    rw [List.length_append]
    omega
  have h3 : p.length ≤ p.length + j := Nat.le_add_right _ _
  rw [List.getElem_append_left h1, List.getElem_append_left h2,
    List.getElem_append_right h3]
  exact getElem_congr_idx (by omega)

/-- **A letter of the quadrilateral in the `p`-block is a letter of `p`.** -/
theorem getElem_mem_fourGon_p (p q r s : List (RelLetter G Λ)) {n : ℕ}
    (hnp : n < p.length) (hn : n < (p ++ q ++ r ++ revWord s).length) :
    (p ++ q ++ r ++ revWord s)[n]'hn ∈ p := by
  have h1 : n < (p ++ q ++ r).length := by
    rw [List.length_append, List.length_append]
    omega
  have h2 : n < (p ++ q).length := by
    rw [List.length_append]
    omega
  rw [List.getElem_append_left h1, List.getElem_append_left h2,
    List.getElem_append_left hnp]
  exact List.getElem_mem _

/-- **A letter of the quadrilateral in the `r`-block is a letter of `r`.** -/
theorem getElem_mem_fourGon_r (p q r s : List (RelLetter G Λ)) {n : ℕ}
    (h1 : p.length + q.length ≤ n) (h2 : n < p.length + q.length + r.length)
    (hn : n < (p ++ q ++ r ++ revWord s).length) :
    (p ++ q ++ r ++ revWord s)[n]'hn ∈ r := by
  have h3 : n < (p ++ q ++ r).length := by
    rw [List.length_append, List.length_append]
    omega
  have h4 : (p ++ q).length ≤ n := by
    rw [List.length_append]
    omega
  rw [List.getElem_append_left h3, List.getElem_append_right h4]
  exact List.getElem_mem _

/-! ## A component of the side is a component of the quadrilateral -/

/-- **A component of the long side `q` is a component of the quadrilateral**,
at the shifted indices, provided the two short sides are spelled by base
letters and the run does not reach the end of `q` with `r` empty. -/
theorem isComp_fourGon_of_isComp_side (p q r s : List (RelLetter G Λ))
    (lam : Λ) (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x)
    (hr : ∀ a ∈ r, ∃ x : G, a = RelLetter.base x) {i k : ℕ}
    (hcomp : IsComp lam q i k) (hk : k < q.length ∨ 0 < r.length) :
    IsComp lam (p ++ q ++ r ++ revWord s) (p.length + i) (p.length + k) := by
  obtain ⟨hik, hkq, hrange, hpre, hpost⟩ := hcomp
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
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
  · intro hkl hc
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

/-- **The isolated-component form, entered from a component of the side.**

This is the statement a caller holding `IsComp lam u₀ i k` can use directly:
the component of `u₀` is a component of the quadrilateral, and if it is not
isolated there it is connected to another component of the quadrilateral, with
the connector named in both branches and no bound claimed on it.

What is *not* here is the step from a component being **deep** --- its span
outside `D.relBall lam ρ` --- to its being non-isolated.  That implication is
Dahmani--Guirardel--Osin's Proposition 4.13 and is where the quasi-geodesic
constants and the hyperbolicity of `Γ(G, X ⊔ ℋ)` are actually spent; it is not
proved anywhere in this development, and it is not assumed here either.  The
hypothesis carried is the conclusion of that step, `¬ IsIsolated`, so that
whatever proves 4.13 plugs in without changing anything below it. -/
theorem exists_other_component_of_isComp_side (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ))
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x)
    (hr : ∀ a ∈ r, ∃ x : G, a = RelLetter.base x) {i k : ℕ}
    (hcomp : IsComp lam q i k) (hk : k < q.length ∨ 0 < r.length)
    (hnot : ¬ IsIsolated D.fam lam 1 (p ++ q ++ r ++ revWord s)
      (p.length + i)) :
    (∃ i' : ℕ, i' ≤ q.length ∧ i' ≠ i ∧
        IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') ∧
        ∃ h : G, h ∈ D.fam lam ∧
          vertex (1 : G) q i * h = vertex (1 : G) q i')
      ∨ (∃ j : ℕ, j ≤ s.length ∧
        IsCompStart lam (p ++ q ++ r ++ revWord s)
          (p.length + q.length + r.length + (s.length - j)) ∧
        ∃ h : G, h ∈ D.fam lam ∧
          RelLetter.listVal p * vertex (1 : G) q i * h
            = vertex (1 : G) s j) := by
  have hbridge := isComp_fourGon_of_isComp_side p q r s lam hp hr hcomp hk
  obtain ⟨hik, hkq, -, -, -⟩ := hcomp
  exact exists_other_component_fourGon D lam p q r s hclose hp hr (by omega)
    ⟨p.length + k, hbridge⟩ hnot

/-! ## Entering from a deep component, over Osin's Lemma 4.2 -/

/-- **The span of a component of the side is the span of the corresponding
component of the quadrilateral.**  The short side `p` translates both endpoints
and cancels. -/
theorem span_fourGon_side (p q r s : List (RelLetter G Λ)) {i k : ℕ}
    (hi : i ≤ q.length) (hk : k ≤ q.length) :
    (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + i))⁻¹ *
        vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + k)
      = (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k := by
  rw [vertex_fourGon_side p q r s 1 hi, vertex_fourGon_side p q r s 1 hk]
  group

/- **A deep component of one long side is connected to another component of
the quadrilateral, with the connector named**, over Osin's Lemma 4.2.

This is the statement in the form a caller wants it: the hypothesis on the
component is that it is *deep* --- its span escapes `D.relBall lam rho` for a
threshold `rho` depending only on `mu`, `b` and the number of sides --- and the
conclusion names an element of `H_lam` joining it to another component.

Osin's Lemma 4.2 is carried as a leading binder, in the SIX-SIDE form: the bound
asserted only for `n ≤ 6`.  That is the form
`DGOIsolatedComponentCut.connector_mem_relBall` consumes, and it is the form
fp-geometry proves; the unrestricted `IsolatedComponentBound` of
`GGT/OsinComponents.lean` implies it by ignoring the restriction, so a caller
holding that hypothesis loses nothing, while a caller holding only what is
actually available can still use this.  The restriction reappears as `n ≤ 6` on
the conclusion, which costs no consumer anything: the polygon here is a
quadrilateral.

What is proved is everything between the bound and the named connector: that the
component of the side is a component of the quadrilateral, that its span is
unchanged by the passage, that the two short sides carry no components, and
that the connector can be written down.

The direction used is the contrapositive: Lemma 4.2 bounds the span of an
*isolated* component, so a component whose span escapes the bound is not
isolated. -/
/-- **A deep component of one long side is connected to another component of
the quadrilateral**, over the bound AT one pair of constants.

The body lives here.  `exists_other_component_of_deep_six` and
`exists_other_component_of_deep_one` are this theorem fed from the two spellings
of the bound that the tree carries --- over all `(μ,b)`, or over `b` alone at
`μ = 1` --- and nothing else distinguishes them. -/
theorem exists_other_component_of_deep_of_bound (D : RelGenSet G Λ) (lam : Λ)
    (mu b : ℝ)
    (hbnd : ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n)) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho : ℕ), n ≤ 6 →
      ∀ p q r s : List (RelLetter G Λ),
      RelLetter.listVal s
          = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r →
      (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
      (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
      IsQuasiGeodesicPolygon D mu b n 1 (p ++ q ++ r ++ revWord s) →
      ∀ i k : ℕ, IsComp lam q i k → (k < q.length ∨ 0 < r.length) →
        C * n ≤ rho →
        (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k ∉ D.relBall lam rho →
          (∃ i' : ℕ, i' ≤ q.length ∧ i' ≠ i ∧
              IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') ∧
              ∃ h : G, h ∈ D.fam lam ∧
                vertex (1 : G) q i * h = vertex (1 : G) q i')
            ∨ (∃ j : ℕ, j ≤ s.length ∧
              IsCompStart lam (p ++ q ++ r ++ revWord s)
                (p.length + q.length + r.length + (s.length - j)) ∧
              ∃ h : G, h ∈ D.fam lam ∧
                RelLetter.listVal p * vertex (1 : G) q i * h
                  = vertex (1 : G) s j) := by
  obtain ⟨C, hCpos, hC⟩ := hbnd
  refine ⟨C, hCpos, ?_⟩
  intro n rho hn p q r s hclose hp hr hpoly i k hcomp hk hrho hdeep
  have hbridge := isComp_fourGon_of_isComp_side p q r s lam hp hr hcomp hk
  have hiq : i ≤ q.length := by
    obtain ⟨hik, hkl, -, -, -⟩ := hcomp
    omega
  have hkl : k ≤ q.length := by
    obtain ⟨-, hkl, -, -, -⟩ := hcomp
    exact hkl
  refine exists_other_component_of_isComp_side D lam p q r s hclose hp hr
    hcomp hk ?_
  intro hiso
  have hspan := hC n hn 1 (p ++ q ++ r ++ revWord s) hpoly lam (p.length + i)
    (p.length + k) hbridge hiso
  rw [span_fourGon_side p q r s hiq hkl] at hspan
  exact hdeep (relBall_mono_radius D lam hrho hspan)

/-- **The same, over the bound at every pair of constants.** -/
theorem exists_other_component_of_deep_six (D : RelGenSet G Λ)
    (hbound : ∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (lam : Λ) {mu b : ℝ} (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho : ℕ), n ≤ 6 →
      ∀ p q r s : List (RelLetter G Λ),
      RelLetter.listVal s
          = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r →
      (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
      (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
      IsQuasiGeodesicPolygon D mu b n 1 (p ++ q ++ r ++ revWord s) →
      ∀ i k : ℕ, IsComp lam q i k → (k < q.length ∨ 0 < r.length) →
        C * n ≤ rho →
        (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k ∉ D.relBall lam rho →
          (∃ i' : ℕ, i' ≤ q.length ∧ i' ≠ i ∧
              IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') ∧
              ∃ h : G, h ∈ D.fam lam ∧
                vertex (1 : G) q i * h = vertex (1 : G) q i')
            ∨ (∃ j : ℕ, j ≤ s.length ∧
              IsCompStart lam (p ++ q ++ r ++ revWord s)
                (p.length + q.length + r.length + (s.length - j)) ∧
              ∃ h : G, h ∈ D.fam lam ∧
                RelLetter.listVal p * vertex (1 : G) q i * h
                  = vertex (1 : G) s j) :=
  exists_other_component_of_deep_of_bound D lam mu b (hbound mu b hmu hb)

/-- **The same, over the bound at `μ = 1`** --- the spelling
`OsinTheorem54SepSixBound.sixBound_one_of_fourPointHyperbolic` proves outright,
and the only one anything in this development instantiates. -/
theorem exists_other_component_of_deep_one (D : RelGenSet G Λ)
    (hbound : ∀ b : ℝ, 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D 1 b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (lam : Λ) (b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho : ℕ), n ≤ 6 →
      ∀ p q r s : List (RelLetter G Λ),
      RelLetter.listVal s
          = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r →
      (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
      (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
      IsQuasiGeodesicPolygon D 1 b n 1 (p ++ q ++ r ++ revWord s) →
      ∀ i k : ℕ, IsComp lam q i k → (k < q.length ∨ 0 < r.length) →
        C * n ≤ rho →
        (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k ∉ D.relBall lam rho →
          (∃ i' : ℕ, i' ≤ q.length ∧ i' ≠ i ∧
              IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') ∧
              ∃ h : G, h ∈ D.fam lam ∧
                vertex (1 : G) q i * h = vertex (1 : G) q i')
            ∨ (∃ j : ℕ, j ≤ s.length ∧
              IsCompStart lam (p ++ q ++ r ++ revWord s)
                (p.length + q.length + r.length + (s.length - j)) ∧
              ∃ h : G, h ∈ D.fam lam ∧
                RelLetter.listVal p * vertex (1 : G) q i * h
                  = vertex (1 : G) s j) :=
  exists_other_component_of_deep_of_bound D lam 1 b (hbound b hb)

end OsinComponents
end GGT
end GroupApproximation
