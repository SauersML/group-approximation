# Operator lifting does not supply uniform Ulam input

The earlier `hs-stability-from-ulam-stability-and-lifting` proof used an
invalid quantifier interchange and the wrong dimension convention. Its
open prerequisite and proof have been rewritten to state the stronger
input actually sufficient for the published theorem. This is a repair of
the conditional route, not progress establishing that input.

## 1. The cited theorem's hypothesis

Burger--Ozawa--Thom, *On Ulam stability*, Section 2, defines operator defect
using the supremum over all pairs of group elements. Theorem 1.3 gives
finite-dimensional Ulam stability for `SL_n(Z)`, n at least three.
The [primary PDF](https://people.math.ethz.ch/~burger/pub/2013_Ulam_stability.pdf)
was inspected at pages 111--113. The broader
[Glebsky--Lubotzky--Monod--Rangarajan theorem](https://arxiv.org/abs/2301.00476)
also states uniform stability. Thus the required input has order

```text
lim_j sup_(g,h) ||f_j(gh)-f_j(g)f_j(h)||_op = 0.        (ULQ1)
```

An exact homomorphism into an operator-norm ultraproduct, with chosen
unitary coordinate lifts, only gives

```text
for every fixed g,h,
 lim_omega ||f_j(gh)-f_j(g)f_j(h)||_op = 0.             (ULQ2)
```

Countability allows diagonal subsequences for fixed windows, but does not
move a supremum over the whole infinite group through the limit.

## 2. An elementary counterexample to the interchange

In any infinite finitely generated group G choose distinct elements
`a_j` whose word lengths tend to infinity. Define unital scalar maps

```text
f_j(g) = -1 if g=a_j, and 1 otherwise.
```

For every fixed g, h, eventually none of g, h, gh equals a_j. The
corresponding pair defect is then zero. Thus these maps represent the
trivial homomorphism in the operator-norm ultraproduct, and have zero
error on every fixed finite window eventually.

At each j choose `h_j` outside the finite set `{e,a_j}`. Then
`a_j h_j != a_j`, `f_j(h_j)=1`, and

```text
|f_j(a_j h_j)-f_j(a_j)f_j(h_j)| = |1-(-1)| = 2.
```

The uniform defect is therefore exactly two at every j. This construction
also works in `SL_n(Z)` itself. It does not disprove the existence of
different uniformly controlled lifts: in this example the trivial maps
provide them. It disproves the assertion that the chosen pointwise lifts
already have the uniform error bound used in the former proof.

## 3. Cutting a corner is not flexible dimension addition

Suppose a rank-q_j projection Q_j in dimension d_j has q_j/d_j tending
to one, and an exact representation rho_j on its range approximates
`Q_j U_j(s) Q_j` in normalized HS norm. Extend rho_j by the trivial
representation on the complementary space. This gives an exact
representation in the original dimension d_j. Its retained diagonal
error tends to zero. The omitted blocks of any unitary have combined
HS error at most a constant times `sqrt((d_j-q_j)/d_j)`, hence also
tend to zero. Consequently such a universal cutting-and-exactifying
method gives same-dimension stability.

For the infinite residually finite Kazhdan group `SL_n(Z)`, this
conclusion is ruled out by
[Becker--Lubotzky, Group stability and Property (T)](https://arxiv.org/abs/1809.00632).
Flexible stability instead allows larger dimensions `D_j>=d_j` with
`D_j/d_j->1`. A subsequent deletion need not recover an exact representation
in dimension d_j because the original corner need not be reducing.

There was also a typing problem in the old quotient formulation: a
projection Q in the tracial ultraproduct with trace one equals the identity
there, by faithfulness of the trace. A nontrivial trace-null corner must
be specified by a projection in the operator-norm product or its lifts,
not by treating Q in the quotient as if it were already in the source.

## 4. The repaired route

The prerequisite now asks, for some rank N, for nearby maps in genuinely
padded dimensions satisfying `(ULQ1)`. Applying the published modulus and
then the generatorwise triangle inequality proves flexible HS stability.
Conversely, exact flexible corrections provide such maps with uniform
defect zero. Both nodes now quantify over some N, so their stated
equivalence also has matching rank quantifiers.

No pointwise-to-uniform conversion has been proved. The quadratic-rank
cohomology correction remains valid, but works on defining errors and
fixed pairs and therefore does not fill this gap by itself.
