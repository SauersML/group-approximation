import GroupApproximation.GGT.DGOIsolatedComponentBridge

/-!
# The closing edge of an admissible loop is isolated

This is the step Osin's Lemma 5.8 ends on.  A path `t` from `1` to `h ∈ H_λ`
that avoids `Γ_{H_λ}` is closed up by the single edge `f` labelled `h⁻¹`, and in
the resulting loop `f` is an ISOLATED component: no other component of the loop
lies in the same coset of `H_λ`.

Both clauses are the avoidance hypothesis, read twice.

* `f` is a component AT ALL --- that is, the letter before it is not a
  `λ`-letter --- because if it were, the vertex before it would be
  `h · (that letter's value)⁻¹`, a product of two elements of `H_λ`, hence in
  `H_λ`; and a `λ`-letter read at a vertex of `H_λ` is exactly what avoidance
  forbids.  Osin does not remark on this and it is the one clause that is not
  immediate.
* `f` is isolated because a component of `t` connected to `f` would have its
  vertex in `H_λ` --- `f` sits at `h ∈ H_λ`, so connectedness says the two
  vertices differ by an element of `H_λ` --- which avoidance forbids again.

Nothing here is about `Z`, or about geodesics, or about the enlargement: it is a
fact about any admissible path from `1` to a point of `H_λ`, and it is stated
that way so the surgery of Lemma 5.8 has only to produce such a path.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The closing edge of an admissible loop is an isolated component.** -/
theorem isIsolated_closing_of_avoidsFrom (D : RelGenSet G Λ) (lam : Λ) {h : G}
    (hh : h ∈ D.fam lam) {t : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ t, D.IsLetter a) (hval : RelLetter.listVal t = h)
    (hav : AvoidsFrom D.fam lam t 1) :
    IsIsolated D.fam lam 1 (t ++ [RelLetter.comp lam h⁻¹]) t.length := by
  have hpos := (avoidsFrom_iff_forall D.fam lam t 1).mp hav
  have hone : ([RelLetter.comp lam h⁻¹] : List (RelLetter G Λ)).length = 1 := rfl
  have hlen : (t ++ [RelLetter.comp lam h⁻¹]).length = t.length + 1 := by
    rw [List.length_append, hone]
  have hsing : ∀ (k : ℕ)
      (hk : k < ([RelLetter.comp lam h⁻¹] : List (RelLetter G Λ)).length),
      ([RelLetter.comp lam h⁻¹] : List (RelLetter G Λ))[k]'hk
        = RelLetter.comp lam h⁻¹ := by
    intro k hk
    rw [hone] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  have hvert : ∀ j : ℕ, j ≤ t.length →
      vertex 1 (t ++ [RelLetter.comp lam h⁻¹]) j = vertex 1 t j :=
    fun j hj => vertex_append_of_le t [RelLetter.comp lam h⁻¹] 1 j hj
  have hvt : vertex 1 t t.length = h := by
    rw [vertex_length, one_mul, hval]
  have hlt : ∀ (j : ℕ) (hj : j < t.length)
      (hj' : j < (t ++ [RelLetter.comp lam h⁻¹]).length),
      (t ++ [RelLetter.comp lam h⁻¹])[j]'hj' = t[j]'hj :=
    fun j hj _ => List.getElem_append_left hj
  have hlast : ∀ hj : t.length < (t ++ [RelLetter.comp lam h⁻¹]).length,
      (t ++ [RelLetter.comp lam h⁻¹])[t.length]'hj = RelLetter.comp lam h⁻¹ := by
    intro hj
    rw [List.getElem_append_right (le_refl t.length)]
    exact hsing _ _
  -- the closing edge is a component
  have hstart : IsComp lam (t ++ [RelLetter.comp lam h⁻¹]) t.length
      (t.length + 1) := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro j hj1 hj2 hjw
      have hjeq : j = t.length := by omega
      subst hjeq
      rw [hlast hjw]
      rfl
    · intro j hj hjw
      have hjt : j < t.length := by omega
      rw [hlt j hjt hjw]
      intro hc
      have hxfam : (t[j]'hjt).val ∈ D.fam lam :=
        val_mem_fam_of_isCompOf D (hlet _ (List.getElem_mem hjt)) hc
      have hsucc : vertex 1 t (j + 1) = vertex 1 t j * (t[j]'hjt).val :=
        vertex_succ t 1 j hjt
      have h1 : vertex 1 t (j + 1) = h := by
        rw [← hj, hvt]
      have hjv : vertex 1 t j ∈ D.fam lam := by
        have h2 : vertex 1 t j = h * ((t[j]'hjt).val)⁻¹ := by
          rw [← h1, hsucc]
          group
        rw [h2]
        exact mul_mem hh (inv_mem hxfam)
      exact hpos j hjt hc hjv
    · intro hk
      exfalso
      rw [hlen] at hk
      omega
  refine ⟨⟨t.length + 1, hstart⟩, ?_⟩
  intro j hjne hjstart hconn
  obtain ⟨k, hk⟩ := hjstart
  have hjk : j < k := hk.1
  have hkw : k ≤ (t ++ [RelLetter.comp lam h⁻¹]).length := hk.2.1
  rw [hlen] at hkw
  have hjt : j < t.length := by omega
  have hjw : j < (t ++ [RelLetter.comp lam h⁻¹]).length := by
    rw [hlen]
    omega
  have hjcomp : (t[j]'hjt).IsCompOf lam := by
    have hgot := hk.2.2.1 j (le_refl j) hjk hjw
    rwa [hlt j hjt hjw] at hgot
  have hconn' : (vertex 1 (t ++ [RelLetter.comp lam h⁻¹]) t.length)⁻¹ *
      vertex 1 (t ++ [RelLetter.comp lam h⁻¹]) j ∈ D.fam lam := hconn
  rw [hvert t.length le_rfl, hvert j (le_of_lt hjt), hvt] at hconn'
  have hjv : vertex 1 t j ∈ D.fam lam := by
    have hmul := mul_mem hh hconn'
    rwa [mul_inv_cancel_left] at hmul
  exact hpos j hjt hjcomp hjv

end OsinComponents
end GGT
end GroupApproximation
