# Independent review of the factorial-torsion manuscript

Date: 5 September 2026. Reviewer: the Berend/LVIII parallel lane.

I read the entire file
`stw59-factorial-torsion-simple-ah-manuscript-2026-09-05.md`, including
the structural and finite-stage detection arguments. This is an
internal mathematical review, not external verification or a claim
of a second named open-problem resolution. I found no mathematical
correction needed for the stated theorem or its finite-order corollary.

## Finite obstruction and powers

1. The restriction kernel in Lemma 1 is exactly the indicated tensor
   product: `K^1(Y)=0`, and all relevant K-groups are free. External
   multiplication of the normalized odd Bott classes gives `z` with
   coefficient one. Since `z^2=0`, the logarithmic Chern identity
   is linear here, including for virtual classes. Every displayed
   coefficient is
   `n! binom(|b|+n,n) multinomial(|b|;b) product a_j^b_j`,
   an integer multiple of `n!`. Torsion-free integral cohomology
   justifies the integral divisibility assertion. Multiplication
   by `c(V)` preserves it.
2. An isomorphism of the two complements really does extend to a
   unitary automorphism of the same bundle `V`. The inverse in the
   mapping-torus convention is consistent: the terminal section
   is `g e`, which identifies with the initial section `e`.
   Formula (8) is nonzero at the seam, and its interior zero set
   is exactly the one stated. The derivative in the sphere and
   interval variables is invertible at every zero; its orientation
   sign differs from the local degree sign by one fixed global
   sign. The product zero count is consequently `+/- k`, with no
   missing factorial. No stable gauge automorphism is assumed to
   lift to an unstable one: Lemma 1 applies to the actual mapping
   torus of every possible complement isomorphism.
3. The power/degree identification is justified by the boundary
   homomorphism of `U(n)->U(n+1)->S^(2n+1)`:
   `partial(k)=k partial(1)=[u_n^k]`.
   Pulling back the frame bundle along a degree-`k` sphere map has
   this characteristic class. One need not assume that the chosen
   smooth degree map preserves hemispheres. Thus its associated
   vector bundle is the clutch bundle of `u_n^k`.
4. A null-homotopy in the endomorphism section algebra extends the
   clutching automorphism over the hemisphere times `Y`; the
   background bundle `1^n+H` extends there by pullback from `Y`.
   Therefore Lemma 2 really obstructs the unitary null-homotopy.
   Conversely the source relation `[u_n]^(n!)=1` gives the upper
   bound on the component order. Equation (11) follows in both
   directions. The additional trivial line required for the
   `U(n+1)` contraction is present in the second copy of `E`, so
   the asserted `M_2` contraction is valid.

## Full tower and exact order

5. The rank identity is exact:
   `rank(H_i)=sum_(j<i)n 2^j=n(2^i-1)` and
   `rank(E_i)=n 2^i=r_i`. The same identity gives
   `dim(X_i)=2n+2 sum_(j<i)r_j=2r_i`.
   The chosen fiber identification makes the evaluation summand
   in (13) an endomorphism of the stated line-twisted bundle;
   the coordinate summand gives a unital injective homomorphism.
6. The repeated dense sequence in the infinite product gives dense
   tails after every earlier coordinate projection. A nonzero
   positive stage element retains its nonzero coordinate block
   until a later evaluation hits its nonzero open set. That
   evaluation block is nonzero at every point of the next base,
   hence is full there. The explicit quotient/cutdown argument
   correctly upgrades this fact to simplicity for arbitrary
   nonzero ideals of the limit.
7. The claims AH, nuclear, separable, unital and infinite-dimensional
   follow from the building blocks and injectivity. Even cells
   give `K^1(X_i)=0`, and Morita equivalence and continuity give
   zero limit `K_1`. Compactness of the product of trace spaces
   gives a compatible family without requiring surjective trace
   restrictions. Its faithful limit trace and faithful matrix
   amplifications prove stable finiteness.
8. At each step the evaluated matrix is a single constant unitary
   in `U(r_i)`. A path contracting that matrix remains a legitimate
   path after tensoring with the line bundle. Thus the stage image
   of the original unitary is homotopic to `u_n+1_(H_i)`; taking
   powers of this same path proves the assertion for every integer
   power, not just the first power.
9. The finite-stage path detection uses only injectivity, finite
   approximation of a norm-continuous path and polar decomposition.
   An element within `1/100` of a unitary has polar unitary within
   `2/100` of it. The chosen adjacent vertices therefore remain
   at distance strictly below two; their principal-logarithm paths
   lie in the common stage. The endpoints can be kept exact.
   Consequently no nonzero residue modulo `n!` can become null
   only at the limit.
10. The source `n!`-power contraction and the one-stabilization
    contraction pass through the inductive system. Together with
    item 9 this proves exact order `n!`, rather than merely a
    surviving nonzero torsion class. If `d` divides `n!`, the power
    `v_n^(n!/d)` has order exactly `d`. This conclusion only
    constructs one algebra for each chosen order, as the manuscript
    explicitly states.

The full manuscript passes this independent internal review. The
review does not assert that the entire component group is cyclic,
that one algebra realizes all finite orders, or that the examples
are pure.

## Cairn validation

The actual CLI commands `check --changed` and `preview` passed on MSI
for the relevant dependency closure: 25 claims and 23 routes. The
factorial-torsion claim derives `ESTABLISHED`; the LIX root derives
`REFUTED`, while LXI remains open. A first run found an earlier LXI
artifact missing from the temporary check directory; uploading that
existing artifact repaired the environment, and both checks then passed.
No proof or prerequisite was removed to obtain the clean result.

Logs are `factorial-check.log` and `factorial-preview.log` in
`/projects/standard/hsiehph/sauer354/stw79-cairn-check-20260904/cu-all-base-scope-20260905`.
These checks validate the source graph and its declared derivations;
the mathematical review above is separate.
