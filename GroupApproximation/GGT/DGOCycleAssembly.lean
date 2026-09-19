import GroupApproximation.GGT.DGOCycleSplice

/-!
# Splicing a connector across a polygon keeps the component isolated

This is the assembly step of Dahmani--Guirardel--Osin's Lemma 4.16, separated
from the choice of the two indices.  Given the polygon `w` with an isolated
`H lam`-component as its first letter, two indices `m ≤ j`, and a connector `r`
from `vertex v w m` to `vertex v w j` **no vertex of which lies in the coset**,
the word

    q = w.take m ++ (r ++ w.drop j)

is a closed admissible path carrying the same span as an isolated component at
`0`, of length `m + |r| + (|w| - j)`.  All four of their Case 4 cycles are
instances --- they differ only in how `m`, `j` and `r` are produced --- and the
two-connector case is this applied twice.

## Where each hypothesis is spent

Closedness of `w` gives `listVal (w.drop j) = (vertex v w j)⁻¹ * v`, which is
what lets the suffix return to the basepoint.  Isolation of the original
component rules out `lam`-letters at coset vertices in the prefix and the
suffix, through `notMem_coset_of_isIsolated_zero`.  The connector hypothesis
rules them out along `r`; in the construction it is supplied by
`notMem_coset_vertex_of_offset`, and this is the only place the corner offset
is used.

`2 ≤ m` is not assumed: the connector hypothesis at `p = 0` already says
`vertex v w m` is outside the coset, while `vertex v w 0` and `vertex v w 1` are
both in it.  That is also what makes `IsComp lam q 0 1` free --- the letter at
index `1` of `q` is `w[1]`, which the original component's maximality already
says is not a `lam`-letter.

## Supplying the connector

`exists_connector` produces the `r` that `cycle_of_connector` consumes, from
`OsinGeodesicWord.existsGeodesicWord`, and adds the only thing that lemma does
not give: that no vertex of the connector lies in the coset.  It takes the
offset hypothesis as a disjunction over the two endpoints, because a vertex at
parameter `p` of a geodesic word of length `L` is `p` from the start and `L - p`
from the finish --- so the count runs from whichever end is far from `v`.  That
disjunction is what lets the cases which offset along the side *preceding* the
component reuse the same assembly instead of reversing the word.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The splice of a connector into a polygon.** -/
theorem cycle_of_connector (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hcl : RelLetter.listVal w = 1)
    (hcomp : IsComp lam w 0 1) (hiso : IsIsolated D.fam lam v w 0)
    {m j : ℕ} (hmj : m ≤ j) (hjw : j ≤ w.length)
    {r : List (RelLetter G Λ)} (hrlet : ∀ a ∈ r, D.IsLetter a)
    (hrval : RelLetter.listVal r = (vertex v w m)⁻¹ * vertex v w j)
    (hrcos : ∀ p : ℕ, p ≤ r.length →
      v⁻¹ * vertex (vertex v w m) r p ∉ D.fam lam) :
    ∃ q : List (RelLetter G Λ),
      (∀ a ∈ q, D.IsLetter a) ∧ RelLetter.listVal q = 1 ∧
      q.length = m + r.length + (w.length - j) ∧
      IsComp lam q 0 1 ∧ IsIsolated D.fam lam v q 0 ∧
      (vertex v q 0)⁻¹ * vertex v q 1 = (vertex v w 0)⁻¹ * vertex v w 1 := by
  have hmw : m ≤ w.length := le_trans hmj hjw
  have h1w : 1 ≤ w.length := hcomp.2.1
  -- the connector starts outside the coset, so it starts past the component
  have hm0 : m ≠ 0 := by
    intro h
    refine hrcos 0 (Nat.zero_le _) ?_
    subst h
    simp only [vertex_zero, inv_mul_cancel]
    exact one_mem _
  have hm1 : m ≠ 1 := by
    intro h
    refine hrcos 0 (Nat.zero_le _) ?_
    subst h
    have hspan := span_mem_fam_of_isComp D v hlet hcomp
    rw [vertex_zero] at hspan
    simpa only [vertex_zero] using hspan
  have hm2 : 2 ≤ m := by omega
  obtain ⟨hv1, hv2, hv3⟩ := vertex_splice v w r hmw hrval
  have hqlen : (w.take m ++ (r ++ w.drop j)).length
      = m + r.length + (w.length - j) := by
    rw [List.length_append, List.length_append, List.length_take,
      List.length_drop]
    omega
  -- the first letter is the component, the second is not
  have hw0 : (w[0]'(by omega)).IsCompOf lam :=
    hcomp.2.2.1 0 le_rfl (by omega) (by omega)
  have hw1 : ∀ h1 : 1 < w.length, ¬ (w[1]'h1).IsCompOf lam := hcomp.2.2.2.2
  have hqcomp : IsComp lam (w.take m ++ (r ++ w.drop j)) 0 1 := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro i _ hi1 hiq
      have hi0 : i = 0 := by omega
      subst hi0
      rw [getElem_splice_left (i := 0) w r hmw (by omega) hiq]
      exact hw0
    · intro i hcon
      exact absurd hcon (by omega)
    · intro hk hcon
      rw [getElem_splice_left (i := 1) w r hmw (by omega) hk] at hcon
      exact hw1 (by omega) hcon
  -- the suffix returns to the basepoint
  have hAB : RelLetter.listVal (w.take j) * RelLetter.listVal (w.drop j) = 1 := by
    rw [← listVal_append, List.take_append_drop]
    exact hcl
  have htj : RelLetter.listVal (w.take j) = v⁻¹ * vertex v w j := by
    rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
  have htm : RelLetter.listVal (w.take m) = v⁻¹ * vertex v w m := by
    rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
  have hdj : RelLetter.listVal (w.drop j) = (vertex v w j)⁻¹ * v := by
    rw [htj] at hAB
    calc RelLetter.listVal (w.drop j)
        = (v⁻¹ * vertex v w j)⁻¹ *
            ((v⁻¹ * vertex v w j) * RelLetter.listVal (w.drop j)) := by group
      _ = (v⁻¹ * vertex v w j)⁻¹ := by rw [hAB, mul_one]
      _ = (vertex v w j)⁻¹ * v := by group
  refine ⟨w.take m ++ (r ++ w.drop j), ?_, ?_, hqlen, hqcomp, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hlet a (List.take_subset m w h)
    · rcases List.mem_append.mp h with h' | h'
      · exact hrlet a h'
      · exact hlet a (List.drop_subset j w h')
  · rw [listVal_append, listVal_append, htm, hrval, hdj]
    group
  · refine isIsolated_zero_of_notMem D lam v hqcomp ?_
    intro i hine hiq hci
    rcases Nat.lt_or_ge i m with hlt | hge
    · rw [getElem_splice_left (i := i) w r hmw hlt hiq] at hci
      rw [hv1 i (le_of_lt hlt)]
      exact notMem_coset_of_isIsolated_zero D lam v hlet hcomp hiso (p := i)
        (by omega) hci (by omega)
    · rcases Nat.lt_or_ge i (m + r.length) with hlt2 | hge2
      · have hidx : m + (i - m) = i := by omega
        have hveq : vertex v (w.take m ++ (r ++ w.drop j)) i
            = vertex (vertex v w m) r (i - m) := by
          have h := hv2 (i - m) (by omega)
          rwa [hidx] at h
        rw [hveq]
        exact hrcos (i - m) (by omega)
      · have hidx : m + r.length + (i - m - r.length) = i := by omega
        have hveq : vertex v (w.take m ++ (r ++ w.drop j)) i
            = vertex v w (j + (i - m - r.length)) := by
          have h := hv3 (i - m - r.length)
          rwa [hidx] at h
        rw [getElem_splice_right (i := i) w r hge2 hmw hiq] at hci
        rw [hveq]
        exact notMem_coset_of_isIsolated_zero D lam v hlet hcomp hiso
          (p := j + (i - m - r.length)) (by omega) hci (by omega)
  · rw [hv1 0 (by omega), hv1 1 (by omega)]

/-! ## The connector -/

/-- **The connector between two vertices, with its coset-freeness, in either
orientation.**

`OsinGeodesicWord.existsGeodesicWord` supplies an admissible word of length
exactly the distance; what has to be added is that none of its vertices lies in
the coset of the basepoint.  That is the corner offset, and it works from either
end: a vertex at parameter `p` of a geodesic word of length `L` is `p` letters
from the start and `L - p` from the finish, so `θ + 2 ≤ d(v, ·)` at *either*
endpoint clears the whole connector.  Both orientations occur in Lemma 4.16 ---
the cases that offset along the side following the component read the connector
forwards, the cases that offset along the side preceding it read it backwards,
and only this lemma has to know the difference. -/
theorem exists_connector (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} {m j θ : ℕ}
    (hd : wordDist D.alphabet.carrier (vertex v w m) (vertex v w j) ≤ θ)
    (hoff : θ + 2 ≤ wordDist D.alphabet.carrier v (vertex v w m) ∨
      θ + 2 ≤ wordDist D.alphabet.carrier v (vertex v w j)) :
    ∃ r : List (RelLetter G Λ), (∀ a ∈ r, D.IsLetter a) ∧
      RelLetter.listVal r = (vertex v w m)⁻¹ * vertex v w j ∧
      r.length ≤ θ ∧
      ∀ p : ℕ, p ≤ r.length →
        v⁻¹ * vertex (vertex v w m) r p ∉ D.fam lam := by
  obtain ⟨r, hrlet, hrprod, hrlen⟩ :=
    existsGeodesicWord D (vertex v w m) (vertex v w j)
  have hrval : RelLetter.listVal r = (vertex v w m)⁻¹ * vertex v w j := by
    rw [← hrprod, inv_mul_cancel_left]
  have hrle : r.length ≤ θ := by
    rw [hrlen]
    exact hd
  refine ⟨r, hrlet, hrval, hrle, ?_⟩
  intro p hp
  rcases hoff with hstart | hend
  · exact notMem_coset_vertex_of_offset D hrlet hrle hstart hp
  · refine notMem_coset_of_offset D hend ?_
    have hsplit : RelLetter.listVal (r.take p) * RelLetter.listVal (r.drop p)
        = RelLetter.listVal r := by
      rw [← listVal_append, List.take_append_drop]
    have hvp : vertex (vertex v w m) r p
        = vertex v w m * RelLetter.listVal (r.take p) :=
      vertex_eq_mul_listVal_take r (vertex v w m) p
    have hj : vertex v w j = vertex v w m * (RelLetter.listVal (r.take p)
        * RelLetter.listVal (r.drop p)) := by
      rw [hsplit, hrval]
      group
    have hkey : (vertex (vertex v w m) r p)⁻¹ * vertex v w j
        = RelLetter.listVal (r.drop p) := by
      rw [hvp, hj]
      group
    have hnorm : wordDist D.alphabet.carrier (vertex (vertex v w m) r p)
        (vertex v w j) ≤ θ := by
      show wordNorm D.alphabet.carrier
        ((vertex (vertex v w m) r p)⁻¹ * vertex v w j) ≤ θ
      rw [hkey]
      have hle := wordNorm_listVal_le D (r.drop p)
        (fun a ha => hrlet a (List.drop_subset p r ha))
      rw [List.length_drop] at hle
      omega
    rw [wordDist_comm D.alphabet.symmetricGenerating]
    exact hnorm

end OsinComponents
end GGT
end GroupApproximation
