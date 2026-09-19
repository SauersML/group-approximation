---
rg: 2
id: polynomial-rank-is-at-most-hochschild-dimension
kind: claim
title: An algebra of Hochschild dimension d contains no polynomial ring in more than d commuting variables
distinct_from:
  quasi-free-algebras-have-no-trdeg-two-subfields: that forbids subfields of transcendence degree two, whose lower bound on global dimension needs a subfield; this forbids polynomial subrings k[x_1..x_n] with n > hd, needs no flatness and no subfield, and implies that claim at d = 1 because a trdeg-two subfield contains k[x,y].
  leavitt-algebras-have-no-trdeg-two-subfields: that is the Leavitt case for subfields, where the homological method was recorded as needing flatness over the commutative subring; this removes that need by a diagonal Koszul complex after base change.
---

**ESTABLISHED.** Let `k` be a field and `A` a `k`-algebra with Hochschild dimension
`hd_k(A) = pd_(A^e) A = d < ∞`. If `a_1, ..., a_n ∈ A` commute pairwise and are
algebraically independent over `k`, then `n <= d`.

Equivalently, the polynomial rank of `A` (the largest `n` with `k[x_1..x_n]`
embedded as a subalgebra) is at most `hd_k(A)`.

**Special cases.**
- `d = 1` (quasi-free algebras in the sense of Cuntz--Quillen): no two commuting
  algebraically independent elements. This covers free algebras (Bergman's
  centralizer theorem gives the same conclusion there) and `L_k(1,2)`.
- A non-unital embedding of `k[x_1..x_n]` also counts: adjoining `1_A` keeps the
  images algebraically independent.

**Proof.** Route `polynomial-rank-hochschild-bound-via-diagonal-koszul`, self-contained.
- The lower bound: `l.gl.dim(A ⊗_k k(y_1..y_n)) >= n`, from a diagonal Koszul complex
  on `u_i = a_i - y_i`.
- The upper bound: `l.gl.dim(A ⊗_k K) <= hd_k(A)` for every field `K ⊇ k`
  (Cartan--Eilenberg IX.7).

**Consumers.**
- `leavitt-algebras-contain-no-two-variable-polynomial-ring`, route
  `leavitt-polynomial-rank-one-via-hochschild-dimension`.
- `cantor-crossed-hosts-of-finite-cd-have-bounded-polynomial-rank`.
