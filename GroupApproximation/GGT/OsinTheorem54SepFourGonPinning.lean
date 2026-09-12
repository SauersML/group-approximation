import GroupApproximation.GGT.OsinTheorem54SepFourGonGeneral
import GroupApproximation.GGT.OsinTheorem54SepFourGonCorner

/-!
# The match between two long sides is pinned near the diagonal

In a general geodesic polygon the components of one side match the components
of another in an order that only Osin's `⪯` --- the half of Lemma 4.8 this
repository does not carry --- controls.  In the quadrilateral of a
relator-separation argument the two long sides share both endpoints up to the
short base paths, and that pins the match: a component of `q` at index `i`
matches `s` at an index `j` with

  `|i - j| ≤ eps + 1`,

where `eps` bounds the `X`-length of the short side `p`.  The `+1` is the
connector itself, which is one letter of the alphabet because it lies in
`H_λ`.

Two consequences, and the second is the one a caller wants:

* the match is quantitatively near the diagonal, so a caller who knows the
  block structure of its sides can read off which block a match lands in;
* if two components of `q` are more than `2(eps + 1)` apart then their matches
  on `s` are **ordered the same way** --- `exists_two_block_connector_of_deep`.
  That is what detects orientation, and it is why one match never suffices: a
  single match is consistent with an inversion.

The order comes out without `⪯` because both sides are read from the same
basepoint `1`.  For a polygon whose long sides do not share endpoints this
argument says nothing, and there the order really is Lemma 4.8's content.

Conditional on Osin's Lemma 4.2 in the six-side form exactly where
`exists_other_component_of_deep_six` is, and on nothing else; the pinning
estimate itself is unconditional.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## A vertex of a geodesic word is at distance its index -/

/-- **On a geodesic word read from `1`, the vertex at index `i` has word length
exactly `i`.**  At most, because the prefix spells it in `i` letters; at least,
because the word is geodesic. -/
theorem wordNorm_vertex_eq (D : RelGenSet G Λ) {g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D 1 g w) {i : ℕ}
    (hi : i ≤ w.length) :
    wordNorm D.alphabet.carrier (vertex (1 : G) w i) = i := by
  refine le_antisymm ?_ ?_
  · have hpre : vertex (1 : G) w i = RelLetter.listVal (w.take i) := by
      rw [vertex_eq_mul_listVal_take, one_mul]
    rw [hpre]
    have h := wordNorm_listVal_le D (w.take i)
      (fun a ha => hw.1 a (List.take_subset i w ha))
    rw [List.length_take] at h
    omega
  · have h := sub_le_wordDist_vertex D hw 0 i (Nat.zero_le i) hi
    rw [vertex_zero, wordDist_one_left] at h
    omega

/-! ## The pinning estimate -/

/-- **The match is pinned near the diagonal.**

If the connector equation `listVal p * vertex 1 q i * h = vertex 1 s j` holds
with `h ∈ H_λ`, and both long sides are geodesic from `1`, then `i` and `j`
differ by at most `eps + 1`, where `eps` bounds the word length of the short
side.  Both directions are the triangle inequality for `wordNorm`, the reverse
one after inverting the equation.

Unconditional: no bound, no polygon hypothesis, no leaf. -/
theorem index_le_of_connector (D : RelGenSet G Λ) {lam : Λ}
    {p q s : List (RelLetter G Λ)} {eps i j : ℕ}
    (hq : IsGeodesicWord D 1 (RelLetter.listVal q) q)
    (hs : IsGeodesicWord D 1 (RelLetter.listVal s) s)
    (hi : i ≤ q.length) (hj : j ≤ s.length)
    (hple : wordNorm D.alphabet.carrier (RelLetter.listVal p) ≤ eps)
    {h : G} (hh : h ∈ D.fam lam)
    (heq : RelLetter.listVal p * vertex (1 : G) q i * h = vertex (1 : G) s j) :
    j ≤ i + eps + 1 ∧ i ≤ j + eps + 1 := by
  have hsym := D.alphabet.symmetricGenerating
  have hqi : wordNorm D.alphabet.carrier (vertex (1 : G) q i) = i :=
    wordNorm_vertex_eq D hq hi
  have hsj : wordNorm D.alphabet.carrier (vertex (1 : G) s j) = j :=
    wordNorm_vertex_eq D hs hj
  have hh1 : wordNorm D.alphabet.carrier h ≤ 1 := by
    have hstep := wordDist_le_one_of_mem_fam D (lam := lam) (x := (1 : G))
      (y := h) (by rw [inv_one, one_mul]; exact hh)
    rwa [wordDist_one_left] at hstep
  constructor
  · have h1 : wordNorm D.alphabet.carrier (vertex (1 : G) s j)
        ≤ wordNorm D.alphabet.carrier (RelLetter.listVal p * vertex (1 : G) q i)
          + wordNorm D.alphabet.carrier h := by
      rw [← heq]
      exact wordNorm_mul_le hsym _ _
    have h2 : wordNorm D.alphabet.carrier
        (RelLetter.listVal p * vertex (1 : G) q i)
        ≤ wordNorm D.alphabet.carrier (RelLetter.listVal p)
          + wordNorm D.alphabet.carrier (vertex (1 : G) q i) :=
      wordNorm_mul_le hsym _ _
    rw [hsj] at h1
    rw [hqi] at h2
    omega
  · have hback : vertex (1 : G) q i
        = (RelLetter.listVal p)⁻¹ * vertex (1 : G) s j * h⁻¹ := by
      rw [← heq]
      group
    have h1 : wordNorm D.alphabet.carrier (vertex (1 : G) q i)
        ≤ wordNorm D.alphabet.carrier
            ((RelLetter.listVal p)⁻¹ * vertex (1 : G) s j)
          + wordNorm D.alphabet.carrier h⁻¹ := by
      rw [hback]
      exact wordNorm_mul_le hsym _ _
    have h2 : wordNorm D.alphabet.carrier
        ((RelLetter.listVal p)⁻¹ * vertex (1 : G) s j)
        ≤ wordNorm D.alphabet.carrier ((RelLetter.listVal p)⁻¹)
          + wordNorm D.alphabet.carrier (vertex (1 : G) s j) :=
      wordNorm_mul_le hsym _ _
    rw [wordNorm_inv hsym] at h1
    rw [wordNorm_inv hsym, hsj] at h2
    rw [hqi] at h1
    omega

/-! ## The same-side branch closes for a geodesic side -/

/-- **A component of a geodesic side `q` is not connected to a neighbouring
component of the quadrilateral lying in the `q`-block.**

Connected vertices on a geodesic side are one letter apart, hence at most one
index apart; and both ways of being one index apart contradict maximality.  At
`i + 1` the letter before the second run is `q[i]`, which *is* a component
letter, so the second run cannot start there.  At `i - 1` the letter at the
second run's start is `q[i-1]`, which is *not* a component letter, because `i`
starts a component. -/
theorem not_connected_qBlock_of_isComp (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ))
    (hq : IsGeodesicWord D 1 (RelLetter.listVal q) q) {i k i' : ℕ}
    (hcomp : IsComp lam q i k) (hi' : i' ≤ q.length) (hne : i' ≠ i)
    (hstart' : IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i'))
    {h : G} (hh : h ∈ D.fam lam)
    (heq : vertex (1 : G) q i * h = vertex (1 : G) q i') : False := by
  obtain ⟨hik, hkq, hrange, hpre, -⟩ := hcomp
  have hiq : i < q.length := by omega
  have hmem : (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q i' ∈ D.fam lam := by
    rw [← heq]
    simpa using hh
  have hone : wordDist D.alphabet.carrier (vertex (1 : G) q i)
      (vertex (1 : G) q i') ≤ 1 := wordDist_le_one_of_mem_fam D hmem
  have hadj : i' = i + 1 ∨ i' + 1 = i := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hd := sub_le_wordDist_vertex D hq i' i (le_of_lt hlt) (by omega)
      rw [wordDist_comm D.alphabet.symmetricGenerating] at hone
      omega
    · have hd := sub_le_wordDist_vertex D hq i i' (le_of_lt hgt) hi'
      omega
  rcases hadj with hup | hdown
  · obtain ⟨m, -, -, -, hpre', -⟩ := hstart'
    have hjw : p.length + i < (p ++ q ++ r ++ revWord s).length := by
      rw [length_fourGon]
      omega
    refine hpre' (p.length + i) (by omega) hjw ?_
    rw [getElem_fourGon_q p q r s hiq rfl hjw]
    exact hrange i le_rfl hik hiq
  · obtain ⟨m, him, -, hrange', -, -⟩ := hstart'
    have hi'q : i' < q.length := by omega
    have hjw : p.length + i' < (p ++ q ++ r ++ revWord s).length := by
      rw [length_fourGon]
      omega
    have hc := hrange' (p.length + i') le_rfl him hjw
    rw [getElem_fourGon_q p q r s hi'q rfl hjw] at hc
    exact hpre i' (by omega) hi'q hc

/-! ## Two blocks, and the order between their matches -/

/-- **Two well-separated deep components of `q` match `s` in the same order.**

Each deep component is not isolated in the quadrilateral, so it is connected to
another component of it; the two short sides carry no components, and the
`q`-block is excluded by `not_connected_qBlock_of_isComp`, so each match lands
on `s` with a named connector.  The pinning estimate puts each `j` within
`eps + 1` of its `i`, and a separation of more than `2(eps + 1)` between the two
`i`'s then forces `j₁ < j₂`.

That order is what detects orientation: one match alone is consistent with an
inversion, which is why the two-block form is the one a caller needs.

Osin's Lemma 4.2 in the six-side form is the leading binder, exactly as in
`exists_other_component_of_deep_six`; nothing else is assumed.

**Warning.**  The connector this produces joins two component STARTS, and
start-to-start connectors are **not bounded by any polygon statement** ---
fp-geometry's witness `[comp lam h, base x, base x⁻¹, comp lam h⁻¹]` is a
`(1,0)`-quasi-geodesic 4-gon whose two components are connected with
start-to-start element `h`, ranging over all of `H_lam` against a finite
`relBall`.  Only the innermost END-to-START element is bounded (their
Lemma 4.21).  A consumer needing a bounded connector must match on
`(vertex 1 s j)⁻¹ * (listVal p * vertex 1 q k)`, with `k` the component END. -/
theorem exists_two_block_connector_of_deep (D : RelGenSet G Λ)
    (hbound : ∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (lam : Λ) {mu b : ℝ} (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n rho eps : ℕ), n ≤ 6 →
      ∀ p q r s : List (RelLetter G Λ),
      RelLetter.listVal s
          = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r →
      wordNorm D.alphabet.carrier (RelLetter.listVal p) ≤ eps →
      IsGeodesicWord D 1 (RelLetter.listVal q) q →
      IsGeodesicWord D 1 (RelLetter.listVal s) s →
      (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
      (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
      IsQuasiGeodesicPolygon D mu b n 1 (p ++ q ++ r ++ revWord s) →
      ∀ i₁ k₁ i₂ k₂ : ℕ, IsComp lam q i₁ k₁ → IsComp lam q i₂ k₂ →
        k₁ < q.length → k₂ < q.length →
        i₁ + 2 * (eps + 1) < i₂ → C * n ≤ rho →
        (vertex (1 : G) q i₁)⁻¹ * vertex (1 : G) q k₁ ∉ D.relBall lam rho →
        (vertex (1 : G) q i₂)⁻¹ * vertex (1 : G) q k₂ ∉ D.relBall lam rho →
          ∃ j₁ j₂ : ℕ, j₁ < j₂ ∧ j₂ ≤ s.length ∧
            (∃ h₁ : G, h₁ ∈ D.fam lam ∧
              RelLetter.listVal p * vertex (1 : G) q i₁ * h₁
                = vertex (1 : G) s j₁) ∧
            (∃ h₂ : G, h₂ ∈ D.fam lam ∧
              RelLetter.listVal p * vertex (1 : G) q i₂ * h₂
                = vertex (1 : G) s j₂) := by
  obtain ⟨C, hCpos, hC⟩ := exists_other_component_of_deep_six D hbound lam hmu hb
  refine ⟨C, hCpos, ?_⟩
  intro n rho eps hn p q r s hclose hple hq hs hp hr hpoly i₁ k₁ i₂ k₂ hc₁ hc₂
    hk₁ hk₂ hsep hrho hd₁ hd₂
  have key : ∀ i k : ℕ, IsComp lam q i k → k < q.length →
      (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k ∉ D.relBall lam rho →
      ∃ j : ℕ, j ≤ s.length ∧ ∃ h : G, h ∈ D.fam lam ∧
        RelLetter.listVal p * vertex (1 : G) q i * h = vertex (1 : G) s j := by
    intro i k hcomp hk hdeep
    rcases hC n rho hn p q r s hclose hp hr hpoly i k hcomp (Or.inl hk) hrho
      hdeep with ⟨i', hi', hne, hstart', hconn⟩ | ⟨j, hj, -, hconn⟩
    · obtain ⟨hh, hhmem, heq⟩ := hconn
      exact (not_connected_qBlock_of_isComp D lam p q r s hq hcomp hi' hne
        hstart' hhmem heq).elim
    · exact ⟨j, hj, hconn⟩
  obtain ⟨j₁, hj₁, h₁, hh₁, he₁⟩ := key i₁ k₁ hc₁ hk₁ hd₁
  obtain ⟨j₂, hj₂, h₂, hh₂, he₂⟩ := key i₂ k₂ hc₂ hk₂ hd₂
  have hi₁ : i₁ ≤ q.length := by
    obtain ⟨hlt, hle, -, -, -⟩ := hc₁
    omega
  have hi₂ : i₂ ≤ q.length := by
    obtain ⟨hlt, hle, -, -, -⟩ := hc₂
    omega
  obtain ⟨hA, -⟩ := index_le_of_connector D hq hs hi₁ hj₁ hple hh₁ he₁
  obtain ⟨-, hB⟩ := index_le_of_connector D hq hs hi₂ hj₂ hple hh₂ he₂
  exact ⟨j₁, j₂, by omega, hj₂, ⟨h₁, hh₁, he₁⟩, ⟨h₂, hh₂, he₂⟩⟩

/-! ## The gap between two matches, for sides that are only quasi-geodesic -/

/-- **Splitting a prefix.**  `Init`'s `List` API has no `take_take` at this
revision, so the identity `take j = take i ++ (drop i).take (j - i)` is proved
here by induction rather than assembled. -/
theorem listVal_take_split : ∀ (w : List (RelLetter G Λ)) (i j : ℕ), i ≤ j →
    RelLetter.listVal (w.take i)
        * RelLetter.listVal ((w.drop i).take (j - i))
      = RelLetter.listVal (w.take j) := by
  intro w
  induction w with
  | nil =>
      intro i j _
      simp [RelLetter.listVal_nil]
  | cons a t ih =>
      intro i j hij
      cases i with
      | zero => simp [RelLetter.listVal_nil]
      | succ i' =>
          cases j with
          | zero => exact absurd hij (by omega)
          | succ j' =>
              have hij' : i' ≤ j' := by omega
              simp only [List.take_succ_cons, List.drop_succ_cons,
                Nat.succ_sub_succ]
              rw [listVal_cons, listVal_cons, mul_assoc, ih i' j' hij']

/-- **A segment of a word bounds the distance between its endpoints.**

The upper half that a quasi-geodesic hypothesis does not give: whatever the
word, the vertices at `i` and `j` are at most `j - i` letters apart, because the
segment between them spells the difference. -/
theorem wordDist_vertex_le (D : RelGenSet G Λ) {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, D.IsLetter a) {i j : ℕ} (hij : i ≤ j) (_hj : j ≤ w.length) :
    wordDist D.alphabet.carrier (vertex (1 : G) w i) (vertex (1 : G) w j)
      ≤ j - i := by
  have hval : (vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j
      = RelLetter.listVal ((w.drop i).take (j - i)) := by
    rw [vertex_eq_mul_listVal_take w 1 i, vertex_eq_mul_listVal_take w 1 j,
      one_mul, one_mul, ← listVal_take_split w i j hij]
    group
  show wordNorm D.alphabet.carrier
    ((vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j) ≤ j - i
  rw [hval]
  have hle := wordNorm_listVal_le D ((w.drop i).take (j - i))
    (fun a ha => hlet a (List.drop_subset i w (List.take_subset (j - i) _ ha)))
  rw [List.length_take, List.length_drop] at hle
  omega

/-- **The short side cancels between two matches.**

If two vertices `u`, `v` match `u'`, `v'` through the *same* prefix `lp` and
connectors in `H_λ`, then the distance between the matched pair differs from
the distance between the original pair by at most `2` --- one for each
connector.  The prefix drops out entirely: `u'⁻¹v' = h₁⁻¹ (u⁻¹v) h₂`.

So the estimate controlling the *gap* between two matches does not involve
`eps` at all, only the two connectors.  This is stronger than the pinning
estimate `index_le_of_connector` gives when applied twice, and it is what the
quasi-geodesic case needs, since there the pinning of a single index is
multiplicative in `mu` while the gap estimate is not. -/
theorem wordDist_connector_pair (D : RelGenSet G Λ) {lam : Λ}
    {lp u v u' v' h₁ h₂ : G} (hh₁ : h₁ ∈ D.fam lam) (hh₂ : h₂ ∈ D.fam lam)
    (he₁ : lp * u * h₁ = u') (he₂ : lp * v * h₂ = v') :
    wordDist D.alphabet.carrier u' v'
      ≤ wordDist D.alphabet.carrier u v + 2 := by
  have hsym := D.alphabet.symmetricGenerating
  have hn₁ : wordNorm D.alphabet.carrier h₁ ≤ 1 := by
    have hstep := wordDist_le_one_of_mem_fam D (lam := lam) (x := (1 : G))
      (y := h₁) (by rw [inv_one, one_mul]; exact hh₁)
    rwa [wordDist_one_left] at hstep
  have hn₂ : wordNorm D.alphabet.carrier h₂ ≤ 1 := by
    have hstep := wordDist_le_one_of_mem_fam D (lam := lam) (x := (1 : G))
      (y := h₂) (by rw [inv_one, one_mul]; exact hh₂)
    rwa [wordDist_one_left] at hstep
  have hkey : u'⁻¹ * v' = h₁⁻¹ * (u⁻¹ * v) * h₂ := by
    rw [← he₁, ← he₂]
    group
  show wordNorm D.alphabet.carrier (u'⁻¹ * v')
    ≤ wordNorm D.alphabet.carrier (u⁻¹ * v) + 2
  rw [hkey]
  have hA : wordNorm D.alphabet.carrier (h₁⁻¹ * (u⁻¹ * v) * h₂)
      ≤ wordNorm D.alphabet.carrier (h₁⁻¹ * (u⁻¹ * v))
        + wordNorm D.alphabet.carrier h₂ := wordNorm_mul_le hsym _ _
  have hB : wordNorm D.alphabet.carrier (h₁⁻¹ * (u⁻¹ * v))
      ≤ wordNorm D.alphabet.carrier h₁⁻¹
        + wordNorm D.alphabet.carrier (u⁻¹ * v) := wordNorm_mul_le hsym _ _
  rw [wordNorm_inv hsym] at hB
  omega

/-- **Every connector is one letter long.**  An element of `H_λ` is a letter of
`X ⊔ ℋ`, so no bound on a connector beyond `1` is ever needed in the alphabet
metric. -/
theorem wordNorm_connector_le_one (D : RelGenSet G Λ) {lam : Λ} {h : G}
    (hh : h ∈ D.fam lam) : wordNorm D.alphabet.carrier h ≤ 1 := by
  have hstep := wordDist_le_one_of_mem_fam D (lam := lam) (x := (1 : G)) (y := h)
    (by rw [inv_one, one_mul]; exact hh)
  rwa [wordDist_one_left] at hstep

end OsinComponents
end GGT
end GroupApproximation
