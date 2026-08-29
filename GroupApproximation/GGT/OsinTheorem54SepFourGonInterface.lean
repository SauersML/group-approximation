import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning

/-!
# What the quadrilateral hands a consumer, and what it refuses

Two interface facts, both asked for by a consumer of the four-gon machinery.

## The closing clause fails, with the matching intact

`fourGon_closing_clause_fails` exhibits the configuration: short sides
`p = [base x]` and `r = [base x']` with `x' ≠ x⁻¹`, long sides `q` arbitrary and
`s = [base x] ++ q ++ [base x']`.  The quadrilateral closes; every vertex of `q`
matches the corresponding vertex of `s` with connector `1`, so the two long
sides fellow-travel as tightly as anything ever will; and
`listVal r ≠ (listVal p)⁻¹`.

Since `q` is arbitrary, it may be as long, as deep and as quasi-geodesic as one
likes, and `s` is then quasi-geodesic too, being two letters longer.  So no
hypothesis about deep components, isolated-component bounds or quasi-geodesic
sides can yield the closing clause: the configuration satisfies all of them and
refutes it.  Together with `listVal_inv_iff_conj`, which shows the clause *is*
the conjugacy, that closes the question.

## The same-side exclusion need only be assumed near the diagonal

`hnoself_of_near` converts the exclusion hypothesis of
`exists_two_block_connector_of_deep_quasi` from all pairs of component starts
to pairs at index-distance at most `N`, for any `N` with
`mu * (1 + b) ≤ N`.  The reason is that connected components are one letter
apart in the alphabet metric, and a `(mu,b)`-quasi-geodesic side turns that into
an index bound: `|t - t'| ≤ mu * (1 + b)`.  Two components of `q` further apart
than that are *never* connected, so nothing has to be assumed about them.

At `mu = 1`, `b = 0` this is `N = 1` --- adjacent component starts only.  At
`(1, b)` it is `N = 1 + b`.  The price is that `q` must carry its own
quasi-geodesic hypothesis; `exists_two_block_connector_of_deep_quasi` needs it
only for `s`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The closing clause fails -/

/-- **The quadrilateral does not close up**, however good the matching.

The three conjuncts are: the four-gon relation holds; every vertex of `q`
matches the corresponding vertex of `s` with connector `1`; and the closing
clause fails. -/
theorem fourGon_closing_clause_fails (x x' : G) (q : List (RelLetter G Λ))
    (hne : x' ≠ x⁻¹) :
    RelLetter.listVal ([RelLetter.base (Λ := Λ) x] ++ q ++ [RelLetter.base (Λ := Λ) x'])
        = RelLetter.listVal [RelLetter.base (Λ := Λ) x] * RelLetter.listVal q
            * RelLetter.listVal [RelLetter.base (Λ := Λ) x']
      ∧ (∀ i : ℕ, i ≤ q.length →
          RelLetter.listVal [RelLetter.base (Λ := Λ) x] * vertex (1 : G) q i * 1
            = vertex (1 : G) ([RelLetter.base (Λ := Λ) x] ++ q ++ [RelLetter.base (Λ := Λ) x'])
                (i + 1))
      ∧ RelLetter.listVal [RelLetter.base (Λ := Λ) x']
          ≠ (RelLetter.listVal [RelLetter.base (Λ := Λ) x])⁻¹ := by
  have hval : RelLetter.listVal [RelLetter.base (Λ := Λ) x] = x := by
    simp [listVal_singleton, RelLetter.val]
  have hval' : RelLetter.listVal [RelLetter.base (Λ := Λ) x'] = x' := by
    simp [listVal_singleton, RelLetter.val]
  have hb : ((RelLetter.base x : RelLetter G Λ)).val = x := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [listVal_append, listVal_append]
  · intro i hi
    have h1 : i + 1 ≤ ([RelLetter.base x] ++ q).length := by
      show i + 1 ≤ (RelLetter.base x :: q).length
      rw [List.length_cons]
      omega
    rw [vertex_append_of_le _ _ _ _ h1]
    show RelLetter.listVal [RelLetter.base x] * vertex (1 : G) q i * 1
      = vertex (1 : G) (RelLetter.base x :: q) (i + 1)
    rw [vertex_cons_succ, hb, one_mul, hval, mul_one,
      vertex_eq_mul_vertex_one q x i]
  · rw [hval, hval']
    exact hne

/-! ## The same-side exclusion, restricted near the diagonal -/

/-- **Two components of a quasi-geodesic side further apart than `mu * (1 + b)`
are never connected**, so the exclusion hypothesis need only be assumed near the
diagonal.

Connected components are one letter apart in the alphabet metric
(`wordDist_le_one_of_mem_fam`), and the quasi-geodesic clause turns that into an
index bound.  At `mu = 1`, `b = 0` the bound is `1`: adjacent component starts
only. -/
theorem hnoself_of_near (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ)) {mu b : ℝ} (hmu : 1 ≤ mu) (N : ℕ)
    (hN : mu * (1 + b) ≤ (N : ℝ))
    (hqqg : ∀ t t' : ℕ, t ≤ t' → t' ≤ q.length →
      ((t' - t : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) q t)
              (vertex (1 : G) q t') : ℕ) : ℝ))
    (hnear : ∀ t t' : ℕ, t ≤ q.length → t' ≤ q.length → t ≠ t' →
      t' ≤ t + N → t ≤ t' + N →
      IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + t) →
      IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + t') →
      (vertex (1 : G) q t)⁻¹ * vertex (1 : G) q t' ∉ D.fam lam) :
    ∀ t t' : ℕ, t ≤ q.length → t' ≤ q.length → t ≠ t' →
      IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + t) →
      IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + t') →
      (vertex (1 : G) q t)⁻¹ * vertex (1 : G) q t' ∉ D.fam lam := by
  have hmupos : (0 : ℝ) < mu := by linarith
  have hmune : mu ≠ 0 := ne_of_gt hmupos
  have step : ∀ d : ℕ, ((d : ℕ) : ℝ) / mu - b ≤ 1 → d ≤ N := by
    intro d hd
    have h1 : ((d : ℕ) : ℝ) / mu ≤ 1 + b := by linarith
    have h2 : ((d : ℕ) : ℝ) ≤ mu * (1 + b) := by
      calc ((d : ℕ) : ℝ) = mu * (((d : ℕ) : ℝ) / mu) := by field_simp
        _ ≤ mu * (1 + b) := mul_le_mul_of_nonneg_left h1 (le_of_lt hmupos)
    exact_mod_cast le_trans h2 hN
  intro t t' ht ht' hne hst hst' hmem
  have hone : wordDist D.alphabet.carrier (vertex (1 : G) q t)
      (vertex (1 : G) q t') ≤ 1 := wordDist_le_one_of_mem_fam D hmem
  rcases le_total t t' with hle | hle
  · have hq := hqqg t t' hle ht'
    have hcast : ((wordDist D.alphabet.carrier (vertex (1 : G) q t)
        (vertex (1 : G) q t') : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hone
    have hd : t' - t ≤ N := step _ (le_trans hq hcast)
    exact hnear t t' ht ht' hne (by omega) (by omega) hst hst' hmem
  · have hq := hqqg t' t hle ht
    have hone' : wordDist D.alphabet.carrier (vertex (1 : G) q t')
        (vertex (1 : G) q t) ≤ 1 := by
      rwa [wordDist_comm D.alphabet.symmetricGenerating] at hone
    have hcast : ((wordDist D.alphabet.carrier (vertex (1 : G) q t')
        (vertex (1 : G) q t) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hone'
    have hd : t - t' ≤ N := step _ (le_trans hq hcast)
    exact hnear t t' ht ht' hne (by omega) (by omega) hst hst' hmem

end OsinComponents
end GGT
end GroupApproximation
