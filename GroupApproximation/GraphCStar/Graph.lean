import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite directed graphs and Cuntz–Krieger families

A finite directed graph `E = (E⁰, E¹, s, r)` has finitely many vertices and edges, a source map
`s : E¹ → E⁰` and a range map `r : E¹ → E⁰`. An edge `e` goes from `s e` to `r e`.

A Cuntz–Krieger `E`-family in a unital star ring consists of mutually orthogonal projections
`p_v` and elements `s_e` with

* `s_e* s_f = δ_{e,f} p_{r(e)}` and `s_e p_{r(e)} = s_e`;
* `∑_{s(e) = v} s_e s_e* = p_v` whenever `v` emits an edge;
* `∑_v p_v = 1`.

This edge convention is that of Kumjian–Pask–Raeburn, *Cuntz–Krieger algebras of directed graphs*
(Pacific J. Math. 184, 1998) and of Bates–Pask–Raeburn–Szymański, *The C*-algebras of row-finite
graphs* (New York J. Math. 6, 2000). It is also the convention of
`GroupApproximation.KirchbergLoops.CuntzKriegerFamily`. Raeburn's book *Graph algebras* (CBMS 103,
2005) uses the opposite direction.

In a C*-algebra the relations `s_e* s_f = 0` for `e ≠ f` and `s_e p_{r(e)} = s_e` follow from the
others. They are stated here as fields, as in the presentation of the Leavitt path algebra, so that
the structure makes sense in any star ring. The last relation says that the family is unital: for
a finite graph the unit of `C*(E)` is `∑_v p_v`.

* `Graph`: a directed graph with source and range maps.
* `CKFamily`: a unital Cuntz–Krieger family.
* `CKFamily.p_src_mul_s`, `CKFamily.p_mul_s_of_ne`: `p_{s(e)} s_e = s_e` and `p_v s_e = 0` otherwise.
* `CKFamily.map`: the image of a family under a unital star-algebra homomorphism.
* `CKFamily.ofJointlyInjective`: elements whose images under a jointly injective family of
  homomorphisms form Cuntz–Krieger families are themselves a Cuntz–Krieger family.

The prose of this module was written by Claude (Anthropic).
-/

universe u

namespace GroupApproximation
namespace GraphCStar

open Finset

/-- A directed graph with vertex type `V` and edge type `E`. The edge `e` goes from `src e` to
`rng e` (Kumjian–Pask–Raeburn 1998, §1). -/
structure Graph (V E : Type u) where
  /-- The source `s(e)` of an edge. -/
  src : E → V
  /-- The range `r(e)` of an edge. -/
  rng : E → V

variable {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V]

/-- A unital Cuntz–Krieger `G`-family in a star ring (Kumjian–Pask–Raeburn 1998, §1;
Bates–Pask–Raeburn–Szymański 2000, §1), with the orthogonality of the edge ranges and
`s_e p_{r(e)} = s_e` included as relations. -/
structure CKFamily (G : Graph V E) (R : Type*) [Ring R] [StarRing R] where
  /-- The vertex projections. -/
  p : V → R
  /-- The edge partial isometries. -/
  s : E → R
  star_p : ∀ v, star (p v) = p v
  p_mul_p_self : ∀ v, p v * p v = p v
  p_mul_p_of_ne : ∀ v v', v ≠ v' → p v * p v' = 0
  s_mul_p_rng : ∀ e, s e * p (G.rng e) = s e
  star_s_mul_s_self : ∀ e, star (s e) * s e = p (G.rng e)
  star_s_mul_s_of_ne : ∀ e e', e ≠ e' → star (s e) * s e' = 0
  sum_s_mul_star_s : ∀ v, (∃ e, G.src e = v) →
    ∑ e ∈ univ.filter (fun e => G.src e = v), s e * star (s e) = p v
  sum_p : ∑ v, p v = 1

namespace CKFamily

variable {G : Graph V E} {R : Type*} [Ring R] [StarRing R] (F : CKFamily G R)

theorem p_mul_p (v v' : V) : F.p v * F.p v' = if v = v' then F.p v else 0 := by
  by_cases h : v = v'
  · subst h
    rw [if_pos rfl, F.p_mul_p_self]
  · rw [if_neg h, F.p_mul_p_of_ne v v' h]

theorem p_src_mul_s (e : E) : F.p (G.src e) * F.s e = F.s e := by
  have he : e ∈ univ.filter (fun f => G.src f = G.src e) := by simp
  rw [← F.sum_s_mul_star_s (G.src e) ⟨e, rfl⟩, Finset.sum_mul, Finset.sum_eq_single_of_mem e he]
  · rw [mul_assoc, F.star_s_mul_s_self, F.s_mul_p_rng]
  · intro f _ hf
    rw [mul_assoc, F.star_s_mul_s_of_ne f e hf, mul_zero]

theorem p_mul_s_of_ne {v : V} {e : E} (h : v ≠ G.src e) : F.p v * F.s e = 0 := by
  rw [← F.p_src_mul_s e, ← mul_assoc, F.p_mul_p_of_ne v (G.src e) h, zero_mul]

theorem star_s_mul_p_src (e : E) : star (F.s e) * F.p (G.src e) = star (F.s e) := by
  have h := congrArg star (F.p_src_mul_s e)
  rwa [star_mul, F.star_p] at h

theorem p_rng_mul_star_s (e : E) : F.p (G.rng e) * star (F.s e) = star (F.s e) := by
  have h := congrArg star (F.s_mul_p_rng e)
  rwa [star_mul, F.star_p] at h

theorem star_s_mul_s [DecidableEq E] (e e' : E) :
    star (F.s e) * F.s e' = if e = e' then F.p (G.rng e) else 0 := by
  by_cases h : e = e'
  · subst h
    rw [if_pos rfl, F.star_s_mul_s_self]
  · rw [if_neg h, F.star_s_mul_s_of_ne e e' h]

section Map

variable {S : Type*} [CommSemiring S] [Algebra S R] {B : Type*} [Ring B] [StarRing B] [Algebra S B]

/-- The image of a Cuntz–Krieger family under a unital star-algebra homomorphism. -/
def map (φ : R →⋆ₐ[S] B) : CKFamily G B where
  p v := φ (F.p v)
  s e := φ (F.s e)
  star_p v := by rw [← map_star φ, F.star_p]
  p_mul_p_self v := by rw [← map_mul φ, F.p_mul_p_self]
  p_mul_p_of_ne v v' h := by rw [← map_mul φ, F.p_mul_p_of_ne v v' h, map_zero]
  s_mul_p_rng e := by rw [← map_mul φ, F.s_mul_p_rng]
  star_s_mul_s_self e := by rw [← map_star φ, ← map_mul φ, F.star_s_mul_s_self]
  star_s_mul_s_of_ne e e' h := by
    rw [← map_star φ, ← map_mul φ, F.star_s_mul_s_of_ne e e' h, map_zero]
  sum_s_mul_star_s v hv := by
    rw [← F.sum_s_mul_star_s v hv, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul, map_star]
  sum_p := by
    have h := congrArg φ F.sum_p
    rwa [map_sum, map_one] at h

@[simp] theorem map_p (φ : R →⋆ₐ[S] B) (v : V) : (F.map φ).p v = φ (F.p v) := rfl

@[simp] theorem map_s (φ : R →⋆ₐ[S] B) (e : E) : (F.map φ).s e = φ (F.s e) := rfl

end Map

section JointlyInjective

variable {S : Type*} [CommSemiring S] [Algebra S R] {ι : Type*} {B : ι → Type*}
  [∀ i, Ring (B i)] [∀ i, StarRing (B i)] [∀ i, Algebra S (B i)]

/-- Elements `p v`, `s e` of `R` form a Cuntz–Krieger family when their images under a jointly
injective family of unital star-algebra homomorphisms do. -/
def ofJointlyInjective (φ : ∀ i, R →⋆ₐ[S] B i) (hφ : ∀ x y, (∀ i, φ i x = φ i y) → x = y)
    (Fi : ∀ i, CKFamily G (B i)) (p : V → R) (s : E → R) (hp : ∀ i v, φ i (p v) = (Fi i).p v)
    (hs : ∀ i e, φ i (s e) = (Fi i).s e) : CKFamily G R where
  p := p
  s := s
  star_p v := hφ _ _ fun i => by rw [map_star, hp, (Fi i).star_p]
  p_mul_p_self v := hφ _ _ fun i => by rw [map_mul, hp, (Fi i).p_mul_p_self]
  p_mul_p_of_ne v v' h := hφ _ _ fun i => by
    rw [map_mul, hp, hp, (Fi i).p_mul_p_of_ne v v' h, map_zero]
  s_mul_p_rng e := hφ _ _ fun i => by rw [map_mul, hs, hp, (Fi i).s_mul_p_rng]
  star_s_mul_s_self e := hφ _ _ fun i => by
    rw [map_mul, map_star, hs, hp, (Fi i).star_s_mul_s_self]
  star_s_mul_s_of_ne e e' h := hφ _ _ fun i => by
    rw [map_mul, map_star, hs, hs, (Fi i).star_s_mul_s_of_ne e e' h, map_zero]
  sum_s_mul_star_s v hv := hφ _ _ fun i => by
    rw [map_sum, hp, ← (Fi i).sum_s_mul_star_s v hv]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul, map_star, hs]
  sum_p := hφ _ _ fun i => by
    rw [map_sum, map_one, ← (Fi i).sum_p]
    exact Finset.sum_congr rfl fun v _ => hp i v

end JointlyInjective

end CKFamily

end GraphCStar
end GroupApproximation
