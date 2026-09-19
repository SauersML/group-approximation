# Problem LXXII: chain-ideal cover collapse audit (2026-08-30)

## Result

If a weakly purely infinite C-star algebra `A` is the closed sum of ideals
whose internal closed ideal lattices are linearly ordered, then `A` is
purely infinite.  The family can be arbitrary and its members need not be
comparable with one another.

## Permanence audit

There are exactly three permanence moves.

1. Weak pure infiniteness passes from `A` to each cover ideal.  The existing
   chain-ideal theorem therefore makes every cover ideal purely infinite.
2. If `I` and `J` are purely infinite ideals, then `I+J` is purely infinite:
   `I+J` is closed and

   ```text
   0 -> I -> I+J -> J/(I intersect J) -> 0
   ```

   has purely infinite ideal and quotient.  Quotient permanence and
   extension permanence apply in precisely those directions.  Induction
   handles every finite sum.
3. The finite sums form a directed system under injective inclusions.  Its
   C-star inductive limit is their closed union, namely `A`.  Directed
   inductive-limit permanence of plain Kirchberg--Rordam pure infiniteness
   gives the conclusion.

The extension and inductive-limit inputs are the permanence theorems for
plain nonsimple pure infiniteness in E. Kirchberg and M. Rordam,
*Non-simple purely infinite C-star algebras*, American Journal of
Mathematics 122 (2000), 637--666, DOI `10.1353/ajm.2000.0021`.  Strong pure
infiniteness is not substituted.  The proof never asserts that an infinite
sum of closed ideals is closed, nor that an intersection of purely infinite
ideals is purely infinite.

## Strict scope: a rational-cut graph

The new hypothesis is not contained in any of the previous finite-lattice,
global-chain, scattered-spectrum, or transfinite-simple-layer classes.
Here is an explicit witness.

Let `E` be the countable directed graph with vertex set `Q`.  For every
`r<q` and every positive integer `n`, include a parallel edge

```text
e_(q,r,n): q -> r.
```

The graph is acyclic, so `B=C*(E)` is a nonzero separable AF algebra and
satisfies graph Condition (K).  Every vertex is an infinite emitter.  By the
standard admissible-pair description of ideals of an arbitrary graph
C-star algebra under Condition (K), every ideal comes from a saturated
hereditary vertex set.  Saturation imposes no extra condition because there
are no regular vertices.  There are no breaking vertices: relative to a
hereditary set, a vertex emits either zero or infinitely many edges to its
complement, because each ordered pair carries infinitely many parallel
edges.

Consequently the ideal lattice of `B` is exactly the lattice of downward
closed subsets of `Q`.  Any two such subsets are comparable.  This lattice
has no minimal nonzero member: if `H` is nonempty and `q in H`, choose
`s<q`; then the nonempty lower set `{r:r<=s}` is properly contained in `H`.

Put

```text
C = B tensor_min O_infinity,       A_0 = C direct_sum C.
```

Since `B` is separable and exact and `O_infinity` is simple, the exact
primitive-tensor-product theorem identifies `Prim(C)` with `Prim(B)` and
therefore preserves this chain ideal lattice.  The algebra `C` is
`O_infinity`-stable, separable, and nuclear, hence strongly purely infinite;
so `A_0` is strongly, in particular weakly, purely infinite.

The two summand ideals cover `A_0` and each has a chain ideal lattice.  On
the other hand:

* the ideal lattice of `A_0` is the product of two infinite chains, hence is
  infinite and not linearly ordered;
* `A_0` has no minimal nonzero ideal, so `Prim(A_0)` has no isolated point
  and is not scattered;
* any nonzero continuous transfinite series with simple successor layers
  must begin with a nonzero simple ideal, which would be a minimal nonzero
  ideal.  Thus `A_0` admits no such series.

This also explains why the theorem is not merely a reindexing of the prior
transfinite argument.  Its gluing geometry is a directed net of finite sums,
not one composition chain.

For the tensor-space step, the in-repository primary-source import is
`blanchard-kirchberg-exact-primitive-tensor-product`.  The graph calculation
uses the admissible-pair ideal theorem; the infinite parallel edges were
included specifically to eliminate breaking-vertex ideals rather than
silently assuming row-finiteness.
