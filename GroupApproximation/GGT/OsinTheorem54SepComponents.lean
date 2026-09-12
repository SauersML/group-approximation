import GroupApproximation.GGT.OsinTheorem54SepReversal

/-!
# Components, their spans, and the cosets they name

Osin's Lemma 4.9 --- the triangle inequality with defect two that
`GGT.OsinEnlargement.SepData.sep_triangle` records --- is proved by comparing the
components of one side of a geodesic triangle with those of the other two: a
component that is not *isolated* in the triangle is connected to a component of
another side, and therefore contributes the same separating coset.  This module
supplies the two facts that step rests on, both of which
`GGT/OsinComponents.lean` leaves unstated.

* `vertex_succ` --- the vertex map is the running product: reading one more
  letter multiplies by its value.  This is what identifies the index arithmetic
  of `IsComp` with the group arithmetic of `relBall`.
* `span_mem_fam` --- **the span of a component lies in the family.**  Every
  letter of the run is a letter of `H_λ`, and the spans multiply, so
  `(a₋)⁻¹ a₊ ∈ H_λ`.  Without this the essentiality condition of
  `EssentiallyPenetrates` --- that the span is outside a `d̂_λ`-ball --- is not
  even about an element of `H_λ`.
* `mk_eq_mk_of_connected`, `connected_of_mk_eq_mk` --- **`Connected` is coset
  equality.**  `OsinComponents.Connected` says two initial vertices differ by an
  element of `H_λ`; `sepSet` records the coset of an initial vertex.  The two are
  the same statement, and `QuotientGroup.eq` is the whole proof.
* `mk_vertex_eq_of_isComp` --- so a component's two endpoints name the same
  coset.  This is the half of `SepData.sep_comm` that
  `GGT/OsinTheorem54SepReversal.lean` calls immediate: reversing a path turns a
  component's initial vertex into its terminal one, and the coset does not
  notice.

What Lemma 4.9 still needs on top of these is the polygon theory:
`OsinComponents.IsolatedComponentBound` carries `IsQuasiGeodesicPolygon` as an
abstract predicate, and instantiating it at a geodesic triangle, so that
non-isolated components can be counted against the other two sides, is not done
anywhere in the repository.  That, and not the bookkeeping here, is the
obstruction.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The vertex map is the running product -/

/-- **Reading one more letter multiplies by its value.** -/
theorem vertex_succ :
    ∀ (w : List (RelLetter G Λ)) (v : G) (j : ℕ) (hj : j < w.length),
      vertex v w (j + 1) = vertex v w j * (w[j]'hj).val := by
  intro w
  induction w with
  | nil =>
      intro _ j hj
      simp at hj
  | cons a t ih =>
      intro v j hj
      cases j with
      | zero =>
          simp only [vertex_cons_succ, vertex_zero, List.getElem_cons_zero]
      | succ j' =>
          have hj' : j' < t.length := by
            simp only [List.length_cons] at hj
            omega
          rw [vertex_cons_succ, vertex_cons_succ, ih (v * a.val) j' hj',
            List.getElem_cons_succ]

/-! ## The span of a component -/

/-- **The span of a run of `lam`-letters lies in `H lam`.**

Stated as an induction on the far endpoint: if every letter between `i` and `k`
is a `lam`-letter of the family, the vertices `a₋ = vertex v w i` and
`a₊ = vertex v w k` satisfy `a₋⁻¹ a₊ ∈ H lam`.

`EssentiallyPenetrates` asks for that span to lie outside a `d̂_lam`-ball, and a
`d̂_lam`-ball is a subset of `H lam`; so without this lemma the essentiality
condition is not a condition on `H lam` at all. -/
theorem span_mem_fam (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) :
    ∀ k : ℕ, k ≤ w.length → ∀ i : ℕ, i ≤ k →
      (∀ j : ℕ, i ≤ j → j < k → ∀ hj : j < w.length,
        (w[j]'hj).IsCompOf lam) →
          (vertex v w i)⁻¹ * vertex v w k ∈ D.fam lam := by
  intro k
  induction k with
  | zero =>
      intro _ i hi _
      have hi0 : i = 0 := by omega
      subst hi0
      rw [inv_mul_cancel]
      exact one_mem _
  | succ k ih =>
      intro hk i hi hrange
      rcases Nat.eq_or_lt_of_le hi with heq | hlt
      · subst heq
        rw [inv_mul_cancel]
        exact one_mem _
      · have hik : i ≤ k := by omega
        have hkw : k < w.length := by omega
        have hprev : (vertex v w i)⁻¹ * vertex v w k ∈ D.fam lam :=
          ih (by omega) i hik
            (fun j hj1 hj2 hj3 => hrange j hj1 (by omega) hj3)
        have hcompk : (w[k]'hkw).IsCompOf lam := hrange k hik (by omega) hkw
        have hvalk : (w[k]'hkw).val ∈ D.fam lam :=
          val_mem_fam_of_isCompOf D (hlet _ (List.getElem_mem hkw)) hcompk
        rw [vertex_succ w v k hkw, ← mul_assoc]
        exact mul_mem hprev hvalk

/-- The span of a component, in the form `IsComp` delivers it. -/
theorem span_mem_fam_of_isComp (D : RelGenSet G Λ) {lam : Λ} (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam w i k) :
    (vertex v w i)⁻¹ * vertex v w k ∈ D.fam lam := by
  obtain ⟨hik, hkw, hrange, -, -⟩ := hcomp
  exact span_mem_fam D lam v hlet k hkw i (le_of_lt hik) hrange

/-! ## `Connected` is coset equality -/

/-- **Two connected components name the same coset.**  `Connected` says the two
initial vertices differ by an element of `H lam`, and that is exactly what
`QuotientGroup.eq` reads off. -/
theorem mk_eq_mk_of_connected {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {w : List (RelLetter G Λ)} {i j : ℕ}
    (h : Connected D.fam lam v w i j) :
    (QuotientGroup.mk (vertex v w i) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex v w j) :=
  QuotientGroup.eq.mpr h

/-- The converse: components naming the same coset are connected. -/
theorem connected_of_mk_eq_mk {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {w : List (RelLetter G Λ)} {i j : ℕ}
    (h : (QuotientGroup.mk (vertex v w i) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex v w j)) :
    Connected D.fam lam v w i j :=
  QuotientGroup.eq.mp h

/-- **A component's two endpoints name the same coset.**

This is what makes the coset half of `SepData.sep_comm` immediate: reversing a
path turns a component's initial vertex into its terminal one, and `sepSet`
records only the coset, which does not distinguish them. -/
theorem mk_vertex_eq_of_isComp (D : RelGenSet G Λ) {lam : Λ} (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam w i k) :
    (QuotientGroup.mk (vertex v w i) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex v w k) :=
  QuotientGroup.eq.mpr (span_mem_fam_of_isComp D v hlet hcomp)

end OsinComponents
end GGT
end GroupApproximation
