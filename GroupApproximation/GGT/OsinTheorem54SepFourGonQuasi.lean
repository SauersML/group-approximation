import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning

/-!
# The quadrilateral at quasi-geodesic sides, and what it does not close

Two things, both asked for by a consumer of the four-gon machinery.

## The gap between two matches

`index_le_of_connector` pins a single match to within `eps + 1` of the
diagonal, but only for geodesic sides: for `(mu,b)`-quasi-geodesic sides the
pinning of one index is *multiplicative* in `mu`, because a quasi-geodesic only
gives `|vertex 1 q i| ∈ [i/mu - b, i]`, a range whose width grows linearly in
`i`.  The *gap* between two matches behaves better, for a reason worth stating:
the short side cancels.  Both connectors are taken through the same prefix, so
`u'⁻¹v' = h₁⁻¹ (u⁻¹v) h₂` and `eps` does not appear in the estimate at all ---
only the two connectors, each of length one.

So the honest gap bound is two-sided and multiplicative,

  `j₂ - j₁ ≤ mu * ((i₂ - i₁) + 2 + b)`  and  `i₂ - i₁ ≤ mu * ((j₂ - j₁) + 2 + b)`,

and at `mu = 1` it collapses to the additive form with constant `2 + b`.  There
is no additive bound at `mu > 1`, with any constant.

Note which side needs what: only `s` needs the quasi-geodesic hypothesis, since
`q` enters through the upper bound `wordDist_vertex_le`, which every word
satisfies.

## The closing clause, which the quadrilateral does not give

A consumer asked whether the machinery forces `listVal r = (listVal p)⁻¹` ---
that the four-gon closes up, the connector at the far end being the inverse of
the one at the near end.  It does not, and `listVal_inv_iff_conj` below says why
in one line: given the four-gon relation, that clause is *equivalent* to
`listVal s = listVal p * listVal q * (listVal p)⁻¹`.  It is the conjugacy
itself, not a consequence of anything.

It is also false in general, with deep matching and quasi-geodesic sides
intact.  Take `p = [base x]`, `r = [base x']` with `x' ≠ x⁻¹`, and
`s = [base x] ++ q ++ [base x']`.  The quadrilateral closes; the sides are
quasi-geodesic whenever `q` is, `s` being longer by two letters; every
component of `q` matches the corresponding component of `s` with connector
`h = 1` at index shifted by one; and `listVal r = x' ≠ x⁻¹`.  No polygon
hypothesis distinguishes `p` from `r`, so no polygon argument can produce the
clause.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The closing clause is the conjugacy -/

/-- **The closing clause is not a consequence of the quadrilateral; it is the
conjugacy.**

Given that the four-gon closes, `listVal r = (listVal p)⁻¹` holds exactly when
the two long sides are conjugate by `listVal p`.  So a consumer asking the
polygon machinery for the closing clause is asking it for the conjugacy, and
must get that from somewhere else. -/
theorem listVal_inv_iff_conj (p q r s : List (RelLetter G Λ))
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r) :
    RelLetter.listVal r = (RelLetter.listVal p)⁻¹
      ↔ RelLetter.listVal s
        = RelLetter.listVal p * RelLetter.listVal q * (RelLetter.listVal p)⁻¹ := by
  constructor
  · intro h
    rw [hclose, h]
  · intro h
    have h1 : RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r
        = RelLetter.listVal p * RelLetter.listVal q * (RelLetter.listVal p)⁻¹ := by
      rw [← hclose, h]
    exact mul_left_cancel h1

/-! ## Arithmetic of the quasi-geodesic constant -/

/-- From `x / mu - b ≤ y` and `1 ≤ mu`, the multiplicative form. -/
theorem le_mul_of_div_sub_le {x y mu b : ℝ} (hmu : 1 ≤ mu)
    (h : x / mu - b ≤ y) : x ≤ mu * (y + b) := by
  have hmupos : (0 : ℝ) < mu := by linarith
  have hne : mu ≠ 0 := ne_of_gt hmupos
  have h1 : x / mu ≤ y + b := by linarith
  calc x = mu * (x / mu) := by field_simp
    _ ≤ mu * (y + b) := mul_le_mul_of_nonneg_left h1 (le_of_lt hmupos)

/-! ## The two-block theorem at quasi-geodesic sides -/

/-- **Two deep components of `q` match `s` with a two-sided gap bound**, for
sides that are only `(mu,b)`-quasi-geodesic.

Only `s` carries the quasi-geodesic hypothesis: `q` enters through
`wordDist_vertex_le`, the upper bound every word satisfies.  The same-side
branch is excluded by hypothesis rather than proved, since for
`mu(1 + b) ≥ 2` a quasi-geodesic side can genuinely connect two of its own
components; that hypothesis is stated over component starts, and must be, since
unrestricted it is false for any word carrying a run of length two.

The conclusion carries the gap bound in both directions, and each connector
with its word-norm bound --- which is `1`, every element of `H_λ` being a single
letter of `X ⊔ ℋ`.

`IsolatedComponentBound` is the leading binder, as everywhere in this chain. -/
theorem exists_two_block_connector_of_deep_quasi (D : RelGenSet G Λ)
    (hbound : IsolatedComponentBound (IsQuasiGeodesicPolygon D) D) (lam : Λ)
    {mu b : ℝ} (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho : ℕ) (p q r s : List (RelLetter G Λ)),
      RelLetter.listVal s
          = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r →
      (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
      (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
      (∀ a ∈ q, D.IsLetter a) →
      IsQuasiGeodesicPolygon D mu b n 1 (p ++ q ++ r ++ revWord s) →
      (∀ t t' : ℕ, t ≤ t' → t' ≤ s.length →
        ((t' - t : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) s t)
                (vertex (1 : G) s t') : ℕ) : ℝ)) →
      (∀ t t' : ℕ, t ≤ q.length → t' ≤ q.length → t ≠ t' →
        IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + t) →
        IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + t') →
        (vertex (1 : G) q t)⁻¹ * vertex (1 : G) q t' ∉ D.fam lam) →
      ∀ i₁ k₁ i₂ k₂ : ℕ, IsComp lam q i₁ k₁ → IsComp lam q i₂ k₂ →
        k₁ < q.length → k₂ < q.length → i₁ ≤ i₂ → C * n ≤ rho →
        (vertex (1 : G) q i₁)⁻¹ * vertex (1 : G) q k₁ ∉ D.relBall lam rho →
        (vertex (1 : G) q i₂)⁻¹ * vertex (1 : G) q k₂ ∉ D.relBall lam rho →
          ∃ j₁ j₂ : ℕ, j₁ ≤ s.length ∧ j₂ ≤ s.length ∧
            ((j₂ - j₁ : ℕ) : ℝ) ≤ mu * (((i₂ - i₁ : ℕ) : ℝ) + 2 + b) ∧
            ((j₁ - j₂ : ℕ) : ℝ) ≤ mu * (((i₂ - i₁ : ℕ) : ℝ) + 2 + b) ∧
            (∃ h₁ : G, h₁ ∈ D.fam lam ∧
              wordNorm D.alphabet.carrier h₁ ≤ 1 ∧
              RelLetter.listVal p * vertex (1 : G) q i₁ * h₁
                = vertex (1 : G) s j₁) ∧
            (∃ h₂ : G, h₂ ∈ D.fam lam ∧
              wordNorm D.alphabet.carrier h₂ ≤ 1 ∧
              RelLetter.listVal p * vertex (1 : G) q i₂ * h₂
                = vertex (1 : G) s j₂) := by
  obtain ⟨C, hCpos, hC⟩ := exists_other_component_of_deep D hbound lam hmu hb
  refine ⟨C, hCpos, ?_⟩
  intro n rho p q r s hclose hp hr hqlet hpoly hsqg hnoself i₁ k₁ i₂ k₂ hc₁ hc₂
    hk₁ hk₂ hi12 hrho hd₁ hd₂
  have key : ∀ i k : ℕ, IsComp lam q i k → k < q.length →
      (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k ∉ D.relBall lam rho →
      ∃ j : ℕ, j ≤ s.length ∧ ∃ h : G, h ∈ D.fam lam ∧
        RelLetter.listVal p * vertex (1 : G) q i * h = vertex (1 : G) s j := by
    intro i k hcomp hk hdeep
    have hiq : i ≤ q.length := by
      obtain ⟨hlt, hle, -, -, -⟩ := hcomp
      omega
    have hbridge := isComp_fourGon_of_isComp_side p q r s lam hp hr hcomp
      (Or.inl hk)
    rcases hC n rho p q r s hclose hp hr hpoly i k hcomp (Or.inl hk) hrho hdeep
      with ⟨i', hi', hne, hstart', hconn⟩ | ⟨j, hj, -, hconn⟩
    · obtain ⟨hval, hhmem, heq⟩ := hconn
      refine absurd ?_ (hnoself i i' hiq hi' (Ne.symm hne)
        ⟨p.length + k, hbridge⟩ hstart')
      rw [← heq]
      simpa using hhmem
    · exact ⟨j, hj, hconn⟩
  obtain ⟨j₁, hj₁, h₁, hh₁, he₁⟩ := key i₁ k₁ hc₁ hk₁ hd₁
  obtain ⟨j₂, hj₂, h₂, hh₂, he₂⟩ := key i₂ k₂ hc₂ hk₂ hd₂
  have hi₂q : i₂ ≤ q.length := by
    obtain ⟨hlt, hle, -, -, -⟩ := hc₂
    omega
  have hqd : wordDist D.alphabet.carrier (vertex (1 : G) q i₁)
      (vertex (1 : G) q i₂) ≤ i₂ - i₁ := wordDist_vertex_le D hqlet hi12 hi₂q
  have hpair : wordDist D.alphabet.carrier (vertex (1 : G) s j₁)
        (vertex (1 : G) s j₂)
      ≤ wordDist D.alphabet.carrier (vertex (1 : G) q i₁)
          (vertex (1 : G) q i₂) + 2 :=
    wordDist_connector_pair D hh₁ hh₂ he₁ he₂
  have hpair' : wordDist D.alphabet.carrier (vertex (1 : G) s j₂)
        (vertex (1 : G) s j₁)
      ≤ wordDist D.alphabet.carrier (vertex (1 : G) q i₁)
          (vertex (1 : G) q i₂) + 2 := by
    rw [wordDist_comm D.alphabet.symmetricGenerating]
    exact hpair
  have hmain : ∀ t t' : ℕ, t ≤ t' → t' ≤ s.length →
      wordDist D.alphabet.carrier (vertex (1 : G) s t) (vertex (1 : G) s t')
        ≤ (i₂ - i₁) + 2 →
      ((t' - t : ℕ) : ℝ) ≤ mu * (((i₂ - i₁ : ℕ) : ℝ) + 2 + b) := by
    intro t t' htt ht' hdd
    refine le_mul_of_div_sub_le hmu (le_trans (hsqg t t' htt ht') ?_)
    exact_mod_cast hdd
  have hdd₁ : wordDist D.alphabet.carrier (vertex (1 : G) s j₁)
      (vertex (1 : G) s j₂) ≤ (i₂ - i₁) + 2 := by omega
  have hdd₂ : wordDist D.alphabet.carrier (vertex (1 : G) s j₂)
      (vertex (1 : G) s j₁) ≤ (i₂ - i₁) + 2 := by omega
  have hnn : (0 : ℝ) ≤ ((i₂ - i₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨j₁, j₂, hj₁, hj₂, ?_, ?_,
    ⟨h₁, hh₁, wordNorm_connector_le_one D hh₁, he₁⟩,
    ⟨h₂, hh₂, wordNorm_connector_le_one D hh₂, he₂⟩⟩
  · rcases le_total j₁ j₂ with hle | hle
    · exact hmain j₁ j₂ hle hj₂ hdd₁
    · have h0 : (j₂ - j₁ : ℕ) = 0 := by omega
      rw [h0, Nat.cast_zero]
      nlinarith
  · rcases le_total j₂ j₁ with hle | hle
    · exact hmain j₂ j₁ hle hj₁ hdd₂
    · have h0 : (j₁ - j₂ : ℕ) = 0 := by omega
      rw [h0, Nat.cast_zero]
      nlinarith

end OsinComponents
end GGT
end GroupApproximation
