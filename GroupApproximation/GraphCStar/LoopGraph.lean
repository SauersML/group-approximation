import GroupApproximation.GraphCStar.Graph
import GroupApproximation.KirchbergLoops.GraphRows

/-!
# The graphs `E(u)` of STW Problem L

For `u : Fin n → ℕ` the graph `E(u)` of the STW Problem L artifact
(`research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md`, §2) has vertices `Fin n`, a loop
`d i` at each vertex `i`, and edges `a i ⟨j, k⟩ : i → j` for `k : Fin (u j)`. Its vertex matrix
is `M(u)_{ij} = δ_{ij} + u_j`.

* `loopGraph u`: the graph `E(u)`, with edge type `Fin n ⊕ Fin n × ArrowIndex u`.
* `sum_filter_src`: the edges leaving `v` are the loop at `v` and the edges `a v e`.
* `CKFamily.ofLoopFamily`, `CKFamily.toLoopFamily`: Cuntz–Krieger `E(u)`-families in the sense of
  this directory are the families `KirchbergLoops.CuntzKriegerFamily` of `KirchbergLoops/GraphRows`.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation
namespace GraphCStar

open Finset KirchbergLoops

variable {n : ℕ} (u : Fin n → ℕ)

/-- The graph `E(u)`: a loop `Sum.inl i` at each vertex and edges `Sum.inr (i, ⟨j, k⟩) : i → j`
for `k : Fin (u j)`. -/
def loopGraph : Graph (Fin n) (Fin n ⊕ Fin n × ArrowIndex u) where
  src := Sum.elim id Prod.fst
  rng := Sum.elim id fun ie ↦ ie.2.1

@[simp] theorem loopGraph_src_inl (i : Fin n) : (loopGraph u).src (.inl i) = i := rfl

@[simp] theorem loopGraph_rng_inl (i : Fin n) : (loopGraph u).rng (.inl i) = i := rfl

@[simp] theorem loopGraph_src_inr (i : Fin n) (e : ArrowIndex u) :
    (loopGraph u).src (.inr (i, e)) = i := rfl

@[simp] theorem loopGraph_rng_inr (i : Fin n) (e : ArrowIndex u) :
    (loopGraph u).rng (.inr (i, e)) = e.1 := rfl

theorem sum_filter_src {M : Type*} [AddCommMonoid M] (f : Fin n ⊕ Fin n × ArrowIndex u → M)
    (v : Fin n) :
    ∑ e ∈ univ.filter (fun e ↦ (loopGraph u).src e = v), f e =
      f (.inl v) + ∑ a, f (.inr (v, a)) := by
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  congr 1
  · rw [Finset.sum_eq_single v]
    · exact if_pos rfl
    · intro b _ hb
      exact if_neg hb
    · intro h
      exact absurd (Finset.mem_univ v) h
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
    · exact Finset.sum_congr rfl fun _ _ ↦ if_pos rfl
    · intro b _ hb
      exact Finset.sum_eq_zero fun _ _ ↦ if_neg hb
    · intro h
      exact absurd (Finset.mem_univ v) h

namespace CKFamily

variable {u} {R : Type*} [Ring R] [StarRing R]

/-- A `KirchbergLoops.CuntzKriegerFamily` is a Cuntz–Krieger `E(u)`-family. -/
def ofLoopFamily (F : KirchbergLoops.CuntzKriegerFamily R n u) : CKFamily (loopGraph u) R where
  p := F.p
  s := Sum.elim F.d fun ie ↦ F.a ie.1 ie.2
  star_p := F.star_p
  p_mul_p_self v := by rw [F.p_mul_p, if_pos rfl]
  p_mul_p_of_ne v v' h := by rw [F.p_mul_p, if_neg h]
  s_mul_p_rng := by
    rintro (i | ⟨i, a⟩)
    · have h := KirchbergLoops.mul_rowProj_of_row (F.sum_row_mul_star_row i)
        (F.star_row_mul_row i) (.inl i)
      rw [F.row_inl, if_pos rfl, F.rowProj_inl] at h
      exact h
    · have h := KirchbergLoops.mul_rowProj_of_row (F.sum_row_mul_star_row i)
        (F.star_row_mul_row i) (.inr a)
      rw [F.row_inr, F.rowProj_inr] at h
      exact h
  star_s_mul_s_self := by
    rintro (i | ⟨i, a⟩)
    · exact (F.star_d_mul_d i i).trans (if_pos rfl)
    · exact (F.star_a_mul_a i a i a).trans (if_pos ⟨rfl, rfl⟩)
  star_s_mul_s_of_ne := by
    rintro (i | ⟨i, a⟩) (i' | ⟨i', a'⟩) h
    · exact (F.star_d_mul_d i i').trans (if_neg fun hi ↦ h (congrArg Sum.inl hi))
    · exact F.star_d_mul_a i i' a'
    · exact F.star_a_mul_d i a i'
    · exact (F.star_a_mul_a i a i' a').trans (if_neg fun hia ↦ by
        rcases hia with ⟨rfl, rfl⟩
        exact h rfl)
  sum_s_mul_star_s v _ := by
    rw [sum_filter_src]
    exact F.sum_source v
  sum_p := F.sum_p

@[simp] theorem ofLoopFamily_p (F : KirchbergLoops.CuntzKriegerFamily R n u) (v : Fin n) :
    (ofLoopFamily F).p v = F.p v := rfl

@[simp] theorem ofLoopFamily_s_inl (F : KirchbergLoops.CuntzKriegerFamily R n u) (i : Fin n) :
    (ofLoopFamily F).s (.inl i) = F.d i := rfl

@[simp] theorem ofLoopFamily_s_inr (F : KirchbergLoops.CuntzKriegerFamily R n u) (i : Fin n)
    (e : ArrowIndex u) : (ofLoopFamily F).s (.inr (i, e)) = F.a i e := rfl

/-- A Cuntz–Krieger `E(u)`-family is a `KirchbergLoops.CuntzKriegerFamily`. -/
def toLoopFamily (F : CKFamily (loopGraph u) R) : KirchbergLoops.CuntzKriegerFamily R n u where
  p := F.p
  d i := F.s (.inl i)
  a i e := F.s (.inr (i, e))
  star_d_mul_d i i' := by
    by_cases h : i = i'
    · subst h
      rw [if_pos rfl]
      exact F.star_s_mul_s_self _
    · rw [if_neg h]
      exact F.star_s_mul_s_of_ne _ _ fun h' ↦ h (Sum.inl_injective h')
  star_d_mul_a i i' e := F.star_s_mul_s_of_ne _ _ Sum.inl_ne_inr
  star_a_mul_a i e i' e' := by
    by_cases h : i = i' ∧ e = e'
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos ⟨rfl, rfl⟩]
      exact F.star_s_mul_s_self _
    · rw [if_neg h]
      exact F.star_s_mul_s_of_ne _ _ fun h' ↦ h (by simpa using h')
  sum_source i := by
    have h := F.sum_s_mul_star_s i ⟨.inl i, rfl⟩
    rw [sum_filter_src] at h
    exact h
  sum_p := F.sum_p

end CKFamily

end GraphCStar
end GroupApproximation
