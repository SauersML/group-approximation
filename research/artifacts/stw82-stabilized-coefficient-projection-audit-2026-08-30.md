# Audit: stabilized coefficient multiplier projections

Date: 2026-08-30

Claim: `stw82-stabilized-coefficient-projections`.

## General theorem

1. `p=e tensor 1` normalizes `B tensor K`, so the displayed adjunction is a
   C-star algebra and contains the stabilized coefficient algebra as an
   ideal.

2. At a finite-rank stage, `p` is the sum of the internal projection
   `e tensor P_n` and the tail `e tensor (1-P_n)`.  The tail annihilates the
   entire stage on both sides, regardless of whether `e` is central in `B`.

3. The stage is therefore exactly `(B tensor M_r) direct_sum C`, not an
   extension requiring an extra colour.  The identity relating consecutive
   tails proves the stages are nested.

4. Matrix corners exhaust `B tensor K` and every stage already contains
   `p`, so their union is dense in the adjoined algebra.  Matrix, direct-sum,
   inductive-limit, ideal, and stabilization permanence give equality of
   nuclear dimensions.

## Nonquasidiagonal witness

5. The two-symbol Toeplitz algebra is the inverse image of the diagonal
   subalgebra `C(T) direct_sum C(T)` under `M_2(T)->M_2(C(T))`.  Its compact
   matrix ideal is essential.

6. The two coefficient support ideals have the stated Peirce matrices,
   proper essential support, and overlap `M_2(K)`.  Stabilization preserves
   all these properties, making both complementary multiplier projections
   nonfull and both supports noncomplemented.

7. The lower-right multiplier corner of the overlap extension is the
   stabilized Toeplitz extension.  Its nonzero index survives in the full
   overlap because the corner induces a Morita isomorphism on `K_0`.
   Therefore the overlap extension is not quasidiagonal and cannot satisfy
   the previous projectional-cut hypothesis.

8. Gardner--Tikuisis computes the essential commutative-by-compacts
   coefficient algebra as nuclear dimension one; the general tail theorem
   transfers that value exactly to the multiplier adjunction.

## Scope

The theorem requires stabilized coefficient form `A=B tensor K` and
`p=e tensor 1` for a projection in a unital coefficient algebra.  It does
not claim that an arbitrary multiplier projection is unitarily equivalent
to this form.  Within this class it imposes no quasidiagonality or support
regularity.

Outcome: **PASS**.
