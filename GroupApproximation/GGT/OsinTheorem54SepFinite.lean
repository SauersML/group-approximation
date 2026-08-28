import GroupApproximation.GGT.OsinTheorem54SepSplit

/-!
# Local finiteness survives a finite enlargement of the base inside the family

This completes the transport `GGT/OsinTheorem54SepSymmetric.lean` needs.  With
`X ⊆ X' ⊆ X ∪ N`, `N ⊆ H` finite, and `d̂` locally finite for `X`, it is locally
finite for `X'`.

The argument is one recursion.  Given an `X'`-avoiding path to `h` of length at
most `n + 1`, either it reads no new letter inside `H` --- and then
`GGT/OsinTheorem54SepTransport.lean` converts it outright --- or it does, and we
cut at the **first** such letter:

* the prefix reads no new letter inside `H`, by minimality, and ends at a vertex
  of `H`, so it converts and puts that vertex in `D.relBall`;
* the letter itself contributes a factor in the finite set `N`;
* the rest, translated back to `1`, is an `X'`-avoiding path of length at most
  `n`, so the recursion applies to it.

`exists_peel` is that trichotomy and `relBall_finite_of_base_subset` the
induction on `n`, whose base case is `relBall_zero`: the radius-zero ball is
`{1}`.

With `alphabet_eq_of_symmetrizedBase`, which says symmetrising the base leaves
`Γ(G, X ⊔ ℋ)` alone, this is everything
`OsinTheorem54SepSymmetric.exists_symmetric_base` needs: hyperbolicity is
literally the same statement for the two relative generating sets, and local
finiteness is the theorem below.  So the symmetrisation, and with it the repair
of `SepData.sep_comm` that `GGT/OsinTheorem54SepCommRefuted.lean` forces, costs
no citation.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Reading a prefix -/

omit [Group G] in
/-- Indexing a prefix agrees with indexing the word. -/
theorem getElem_take_eq :
    ∀ (w : List (RelLetter G Λ)) (j m : ℕ) (hm : m < (w.take j).length)
      (hm' : m < w.length), (w.take j)[m]'hm = w[m]'hm' := by
  intro w
  induction w with
  | nil =>
      intro j m hm _
      simp at hm
  | cons a t ih =>
      intro j m hm hm'
      cases j with
      | zero => simp at hm
      | succ j' =>
          cases m with
          | zero => simp
          | succ m' =>
              have hm2 : m' < (t.take j').length := by
                simp only [List.take_succ_cons, List.length_cons] at hm
                omega
              have hm3 : m' < t.length := by
                simp only [List.length_cons] at hm'
                omega
              simp only [List.take_succ_cons, List.getElem_cons_succ]
              exact ih j' m' hm2 hm3

/-- The vertices of a prefix are the vertices of the word. -/
theorem vertex_take_eq (v : G) (w : List (RelLetter G Λ)) (j m : ℕ)
    (hm : m ≤ j) : vertex v (w.take j) m = vertex v w m := by
  have hmm : (w.take j).take m = w.take m := by
    rw [List.take_take]
    congr 1
    omega
  rw [vertex_eq_mul_listVal_take, vertex_eq_mul_listVal_take, hmm]

/-! ## Cutting at the first new letter inside the family -/

/-- **The peel.**  An `X'`-avoiding path of length at most `n + 1` either
converts wholesale, or splits as `p · x · q` with `p ∈ D.relBall () (n+1)`,
`x ∈ N`, and `q ∈ D'.relBall () n`. -/
theorem exists_peel (D D' : RelGenSet G Unit) (hfam : D'.fam = D.fam)
    {N : Set G} (hN : N ⊆ ((D.fam () : Subgroup G) : Set G))
    (hbase : D'.base ⊆ D.base ∪ N) {n : ℕ} {h : G}
    (hh : h ∈ D'.relBall () (n + 1)) :
    h ∈ D.relBall () (n + 1) ∨
      ∃ p x q : G, p ∈ D.relBall () (n + 1) ∧ x ∈ N ∧
        q ∈ D'.relBall () n ∧ h = p * x * q := by
  classical
  obtain ⟨hfamh, w, hlet, hval, hav, hlen⟩ := hh
  have hfamh' : h ∈ D.fam () := by rw [← hfam]; exact hfamh
  by_cases hgood : ∀ (j : ℕ) (hj : j < w.length) (x : G),
      (w[j]'hj) = RelLetter.base x → x ∈ N → x ∉ D.base →
        vertex (1 : G) w j ∉ D.fam ()
  · exact Or.inl (mem_relBall_of_noNewLetterInFam D D' hfam hN hbase hfamh'
      hlet hval hav hlen hgood)
  · have hex : ∃ j : ℕ, ∃ hj : j < w.length, ∃ x : G,
        (w[j]'hj) = RelLetter.base x ∧ x ∈ N ∧ x ∉ D.base ∧
          vertex (1 : G) w j ∈ D.fam () := by
      by_contra hcon
      refine hgood ?_
      intro j hj x hx hxN hxb hv
      exact hcon ⟨j, hj, x, hx, hxN, hxb, hv⟩
    obtain ⟨hj₀len, x, hx, hxN, hxb, hvH⟩ := Nat.find_spec hex
    -- the prefix reads no new letter inside `H`, so it converts
    have hpre : vertex (1 : G) w (Nat.find hex) ∈ D.relBall () (n + 1) := by
      refine mem_relBall_of_noNewLetterInFam D D' hfam hN hbase hvH
        (fun a ha => hlet a (List.take_subset (Nat.find hex) w ha)) ?_
        (avoidsFrom_take D'.fam () 1 w (Nat.find hex) hav) ?_ ?_
      · rw [vertex_eq_mul_listVal_take w 1 (Nat.find hex), one_mul]
      · rw [List.length_take]
        omega
      · intro m hm y hy hyN hyb hv
        have hmj : m < Nat.find hex := by
          rw [List.length_take] at hm
          omega
        have hmw : m < w.length := by omega
        refine Nat.find_min hex hmj ⟨hmw, y, ?_, hyN, hyb, ?_⟩
        · rw [← getElem_take_eq w (Nat.find hex) m hm hmw]
          exact hy
        · rwa [vertex_take_eq 1 w (Nat.find hex) m (le_of_lt hmj)] at hv
    -- the cut letter, and the vertex after it
    have hxval : (w[Nat.find hex]'hj₀len).val = x := by
      simp [hx, RelLetter.val]
    have hsucc : vertex (1 : G) w (Nat.find hex + 1)
        = vertex (1 : G) w (Nat.find hex) * x := by
      rw [vertex_succ w 1 (Nat.find hex) hj₀len, hxval]
    have hxfam : x ∈ D.fam () := hN hxN
    have hvH1 : vertex (1 : G) w (Nat.find hex + 1) ∈ D'.fam () := by
      rw [hfam, hsucc]
      exact mul_mem hvH hxfam
    have hendq : (vertex (1 : G) w (Nat.find hex + 1))⁻¹ * RelLetter.listVal w
        ∈ D'.fam () := by
      rw [hfam, hval, hsucc]
      exact mul_mem (inv_mem (mul_mem hvH hxfam)) hfamh'
    have hle : w.length - (Nat.find hex + 1) ≤ n := by omega
    have hq : (vertex (1 : G) w (Nat.find hex + 1))⁻¹ * RelLetter.listVal w
        ∈ D'.relBall () n :=
      relBall_mono_radius D' () hle
        (mem_relBall_vertex_inv_mul D' () hlet hav (Nat.find hex + 1) hvH1 hendq)
    refine Or.inr ⟨vertex (1 : G) w (Nat.find hex), x,
      (vertex (1 : G) w (Nat.find hex + 1))⁻¹ * RelLetter.listVal w,
      hpre, hxN, hq, ?_⟩
    rw [hsucc, ← hval]
    group

/-! ## The transport -/

/-- **Local finiteness transports across a finite enlargement of the base inside
the family.** -/
theorem relBall_finite_of_base_subset (D D' : RelGenSet G Unit)
    (hfam : D'.fam = D.fam) {N : Set G}
    (hN : N ⊆ ((D.fam () : Subgroup G) : Set G)) (hNfin : N.Finite)
    (hbase : D'.base ⊆ D.base ∪ N)
    (hDfin : ∀ m : ℕ, (D.relBall () m).Finite) :
    ∀ n : ℕ, (D'.relBall () n).Finite := by
  intro n
  induction n with
  | zero =>
      rw [RelGenSet.relBall_zero]
      exact Set.finite_singleton 1
  | succ n ih =>
      refine Set.Finite.subset
        ((hDfin (n + 1)).union
          (((hDfin (n + 1)).prod (hNfin.prod ih)).image
            (fun t : G × G × G => t.1 * t.2.1 * t.2.2))) ?_
      intro g hg
      rcases exists_peel D D' hfam hN hbase hg with
        hd | ⟨p, x, q, hp, hx, hq, heq⟩
      · exact Or.inl hd
      · exact Or.inr ⟨(p, x, q), ⟨hp, hx, hq⟩, heq.symm⟩

end OsinComponents
end GGT
end GroupApproximation
