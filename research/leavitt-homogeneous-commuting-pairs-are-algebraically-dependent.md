---
rg: 2
id: leavitt-homogeneous-commuting-pairs-are-algebraically-dependent
kind: claim
title: Over every field, two commuting homogeneous elements of the Leavitt algebra L_k(1,n) satisfy a nonzero polynomial relation; so no polynomial ring k[x,y] in L_k(1,n) has homogeneous generators
distinct_from:
  algebraic-core-gradings-bound-homogeneous-laurent-rank: that treats homogeneous units, where x^b y^(-a) has degree 0 and is algebraic; this treats arbitrary homogeneous elements, which have no inverses, by a structure theorem for finite-dimensional modules over the Segre product of the free algebra with k[x,y].
  leavitt-commuting-units-are-algebraically-dependent: that is the open Laurent (unit) question over F_2 for all units; this is proved for all homogeneous elements, units or not, over every field, and says nothing about inhomogeneous pairs.
  laurent-tensors-reduce-leavitt-rank-to-function-fields: that reduces Z^4 host embeddings to two commuting independent elements of L over F_2(x,y); this kills every homogeneous choice of those two elements, over F_2(x,y) and every other field.
  finite-field-polynomial-growth-hosts-bound-commuting-rank: that counts dimensions on polynomial-growth spaces over a finite field and fails on the exponential tree column of L(1,2); this works on that column, over any field, but only for homogeneous elements.
  leavitt-isometry-centralizers-are-monogenic: that computes the whole centralizer of one monomial isometry s_w; this allows both elements to be arbitrary homogeneous sums, of any degrees, and proves only dependence.
artifacts:
  - experiments/leavitt-polynomial-rank-2026-09-17/search_deg1.py
  - experiments/leavitt-polynomial-rank-2026-09-17/nonneg.py
---

**ESTABLISHED (unreviewed)** by `leavitt-homogeneous-pairs-dependence-proof`.

Let `k` be any field, `n >= 2`, and `L = L_k(1,n)` with generators `s_c, s_c^*`
(`c < n`) and the standard `Z`-grading `deg s_c = 1`, `deg s_c^* = -1`.

**Theorem H.** Let `x, y ∈ L` be homogeneous and `xy = yx`. Then some nonzero
`f ∈ k[X, Y]` has `f(x, y) = 0`.

**Sharp form (same positive degree).** If `deg x = deg y = d >= 1` and `x, y` are
written with window `r` (every monomial `s_α s_β^*` refined to `|β| = r`), then
the relation can be taken homogeneous of degree `<= n^r`.

**Corollaries.**
1. *No homogeneous polynomial ring.* `L` contains no `k[X, Y]`, unital or not,
   with homogeneous generators. The same holds after any automorphism of `L`, so
   for every `Z`-grading in the `Aut(L)`-orbit of the standard one.
2. *Leading forms collapse.* For any commutative subalgebra `A ⊆ L`, the span
   `gr(A)` of the top-degree components of elements of `A` is a graded
   commutative subalgebra of `L`, and each of its finitely generated subalgebras
   has Krull dimension `<= 1`. So in any copy of `k[X, Y]` in `L`, the leading
   forms of any two elements are algebraically dependent. The `Z`-degree must
   restrict to a filtration of `k[X, Y]` whose associated graded ring has local
   Krull dimension `<= 1`. Examples are the filtration of a non-divisorial
   discrete valuation, or one whose leading forms multiply to zero. This is a
   constraint on candidates, not an obstruction.
3. *Graded case of Ara–Cortiñas Q5.7.* Let `a, b ∈ L` be transcendental over `k`
   (for example `a = b = s_0`). No injective homomorphism `φ : L ⊗ L -> L` sends
   both `a ⊗ 1` and `1 ⊗ b` to homogeneous elements. In particular no injective
   `φ` is graded for the total grading of `L ⊗ L`. When `L ⊗ L` is simple (the
   central simple case recorded on `leavitt-commuting-units-are-algebraically-dependent`),
   this covers every nonzero `φ`.

**Evidence.** `search_deg1.py` (window size `N = n^r` with `n = 2`, over `F_2`):
- `N = 2`: an exhaustive sweep over `A`, with up to 8 random commuting `B` for
  each, gave 476 pairs, all with relation degree `<= 2`;
- sampled for `N = 3` (17768 pairs) and `N = 4` (1028 pairs): the Hilbert function
  of `k[x, y]` never exceeds `N`, and `N` is attained, for example
  `(2, 3, 4, 4, 4, 4)` at `N = 4`.

So the degree bound `n^r` is sharp in these ranges.

**Why it matters.**
- *Which routes it kills.* The `Z^4` fork
  (`f2-z4-embeds-in-z2-sft-boundary-product-hosts`, under
  `decidable-algebras-embed-in-z2-sft-boundary-product-hosts`) reduces through
  `laurent-tensors-reduce-leavitt-rank-to-function-fields` to `Q_2(F_2(x,y))`:
  two commuting algebraically independent elements of `L` over `F_2(x,y)`. Theorem H
  kills every homogeneous candidate over every field, units or not.
- *What is left.* A YES construction must use inhomogeneous elements whose
  leading forms collapse, as in Corollary 2.
- *Relation to bus-only nodes.* Two nodes are posted on the live bus but not yet
  present in this worktree: `leavitt-algebras-contain-no-two-variable-polynomial-ring`
  (the field-uniform target) and `leavitt-nonnegative-part-is-matrix-union-over-free-algebra`
  (pairs in `L_(>=0)` need trdeg-2 subfields of `M_r(D)`, `r >= 2`). Theorem H is
  the unconditional homogeneous case of the former. It covers every homogeneous
  pair in `L_(>=0)` without the skew-field question `r >= 2`, and it also covers
  pairs of opposite degree, which cannot be moved into `L_(>=0)`.
- *Where it sits against the firewall.* Theorem H does not decide Q5.7. Its
  graded case (Corollary 3) is proved here without K-theory.

**Precise invariant.** A homogeneous pair of the same degree `d >= 1` is a
finite-dimensional module `V = k^(n^r)` over the Segre product
`S = k<e_w : |w| = d> ∘ k[X, Y]`, with `x ↦ (A_w)`, `y ↦ (B_w)`. Commutation is
`A_w B_v = B_w A_v` for all letters `w, v`. The proof shows that every such module
has a homogeneous annihilating form of degree `<= dim V`. It uses two invariant
subspaces, `∩ ker A_w` and `Σ Im A_w`. On the nondegenerate part it proves
`B_w = A_w G = G A_w` for one matrix `G`, and then the minimal polynomial of `G`
is the relation.

## Attempts

1. **Construct `k[x, y]` with homogeneous degree-1 generators (this lane, 2026-09-17).**
   - *Aim:* refute the `NO` mechanism of the `Z^4` fork.
   - *Search:* exhaustive and sampled `F_2` searches over window matrices, in
     `search_deg1.py`.
   - *Result:* every pair tested was dependent.
   - *Where it dies:* Theorem H above, which rules out every homogeneous pair
     over every field.
   - *Next step:* the inhomogeneous search in `L_{>=0}` is set up in `nonneg.py`
     but has not been run.
