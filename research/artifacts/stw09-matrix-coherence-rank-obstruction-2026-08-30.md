# IX(2): normalized-rank obstruction to full-matrix coherification

## The failed shortcut

A faithful quasidiagonal trace gives independent u.c.p. maps to full matrix
algebras, asymptotically multiplicative in operator norm and converging to
the trace.  The finite-core exactification theorem
`stw10-qd-traces-admit-exact-finite-dimensional-core-models` additionally
puts any prescribed finite-dimensional subalgebra in the multiplicative
domain of every model.

A natural proposed shortcut to IX(2) is then:

1. pass to a subsequence and amplify the full matrix targets;
2. connect consecutive targets by unital matrix embeddings;
3. arrange norm coherence of the amplified maps;
4. take the UHF limit.

This shortcut is false for a reason already visible on a single central
projection.  Unital embeddings between full matrix algebras preserve
normalized rank.  Once two projections are within operator-norm distance
strictly less than `1`, their ranks agree.  Thus an exact core projection's
normalized rank freezes along every norm-coherent tail.

## Exact criterion

For `E=direct_sum_j M_(d_j)` with faithful trace `tau`, exact representations
of `E` in full matrices can be connected asymptotically in norm through
unital full-matrix embeddings, while their normalized traces converge to
`tau`, **if and only if** every central weight `tau(z_j)` is rational.

Necessity is projection-rank freezing.  For sufficiency, choose a common
matrix size `k` such that `m_j=k tau(z_j)/d_j` is integral, represent the
`j`-th summand with multiplicity `m_j`, and repeatedly amplify this one
representation.  The trace and coherence are then exact at every stage.

The complete proof is `stw09-projection-rank-freezing-obstruction-proof`.

## Minimal strict obstruction: an AF algebra itself

Fix an irrational `lambda in (0,1)` and set

```text
A=C^2,
tau_lambda(a,b)=lambda a+(1-lambda)b.
```

This is a faithful trace on a finite-dimensional, hence exact and AF,
algebra.  Choose integers `0<r_n<k_n` with `r_n/k_n -> lambda` and define

```text
psi_n(a,b)=diag(a 1_(r_n), b 1_(k_n-r_n)).
```

Every `psi_n` is an exact unital star homomorphism, and
`tr_(k_n) psi_n -> tau_lambda`.  Hence the induced homomorphism

```text
C^2 -> product_omega (M_(k_n),tr_(k_n))
```

is trace-preserving and injective: its composite trace is the faithful
`tau_lambda`.

Nevertheless, no subsequence of these models, even after arbitrary
amplifications, can be norm-coherified through unital embeddings of full
matrix targets with error tending to zero on `(1,0)`.  Such coherence would
force the rational numbers `r_n/k_n` to be eventually constant, contradicting
their irrational limit.

Thus even a faithful tracial matrix-ultraproduct embedding, built from
coordinatewise exact models of an AF algebra, does not contain the proposed
full-matrix coherence data.  This is an obstruction to a proof strategy, not
a counterexample to IX(2): `C^2` is already AF-embeddable.

## What a viable criterion must permit

The established criterion
`stw09-trace-preserving-af-embedding-iff-trace-coherent-models` correctly
allows finite-dimensional algebras with several summands and arbitrary
compatible traces.  Those degrees of freedom can carry irrational central
weights.  Restricting its stages to full matrices with normalized traces
silently imposes rationality and loses even elementary positive examples.

Accordingly, an IX(2) coherification theorem must do at least one of the
following:

- retain multi-summand finite-dimensional stages with compatible noncanonical
  traces;
- abandon trace preservation by the connecting system and obtain injectivity
  through separate norm detection; or
- introduce genuinely new summands rather than insist that every later model
  be a small norm perturbation of one full-matrix amplification.

Tracial `2`-norm agreement is insufficient: projections of different ranks
can become arbitrarily close in normalized `2`-norm while remaining at
operator-norm distance `1`.

