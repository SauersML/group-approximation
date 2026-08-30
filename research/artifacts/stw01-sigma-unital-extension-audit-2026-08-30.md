# Problem I: arbitrary extension permanence and the sequential boundary

## Outcome

Bounded-quasitrace linearity is closed under every unital extension

```text
0 -> I -> A -> A/I -> 0
```

when both the ideal and quotient have bounded-quasitrace linearity.  Neither
the ideal nor the ambient algebra is assumed sigma-unital, separable, or
exact.

For a bounded ambient quasitrace `tau`, its restriction to `I` is a bounded
trace `theta`.  Every positive-contractive approximate-unit net is
asymptotically idempotent and central in the relevant square seminorms.  A
cofinal ultrafilter on the directed index set turns the entire net into an
exact central projection in a quasitracial quotient.  Its head is linear on
the ideal and its tail factors through the quotient.

## Net quotient removes sigma-unitality

Let `(e_lambda)` be any positive-contractive approximate-unit net for `I`.
The finite extension of `theta` to `M(I)` gives

```text
theta(e_lambda), theta(e_lambda^2) -> ||theta||,
theta_tilde((1-e_lambda)^2) -> 0.
```

It follows that the idempotence defects tend to zero and, for every ambient
element `a`,

```text
||[e_lambda,a]||_(2,theta_tilde)
 <= 2||a|| theta_tilde((1-e_lambda)^2)^(1/2) -> 0.
```

The tails of the directed set have the finite-intersection property, so an
ultrafilter containing all of them exists.  In the square-null quotient of
the corresponding coordinate-ultralimit quasitrace, `[e_lambda]` is one
central projection relative to the constant copy of `A`.  The exact
head/tail splitting proves the extension theorem without extracting a
sequence.

## Spectral-measure construction

For a strictly positive contraction `h in I`, the functions
`f_n(t)=min(1,nt)` give an increasing approximate unit `f_n(h)`.  On
`C*(1,h)`, a bounded `2`-quasitrace is a finite positive measure.  Pointwise
convergence and dominated convergence therefore give

```text
tau((f_n(h)-f_n(h)^2)^2) -> 0.
```

This works for every bounded quasitrace with the same sequence.  If the
ambient algebra is separable, successive-tail convexification gives an
increasing norm-quasicentral sequence still consisting of functions of
`h`; the same spectral proof survives the convexification.

## The shorter idempotence argument under ideal linearity

For the permanence theorem, `theta=tau|I` is already a trace.  Both
`e_lambda` and `e_lambda^2` are approximate-unit nets, so

```text
theta(e_lambda), theta(e_lambda^2) -> ||theta||.
```

Since `(e_lambda-e_lambda^2)^2 <= e_lambda-e_lambda^2`, this proves the idempotence limit
without spectral measures.  The spectral argument remains useful because
it proves the construction for an arbitrary fixed bounded quasitrace before
any ideal-linearity assumption is made.

## Why ambient commutators still vanish

The trace `theta` extends canonically to a finite trace on `M(I)`.  With
`r_lambda=1-e_lambda`,

```text
theta_tilde(r_lambda^2)
 = ||theta||-2theta(e_lambda)+theta(e_lambda^2) -> 0.
```

The action of `A` on `I` is a contractive star homomorphism into `M(I)`, and

```text
||[e_lambda,a]||_(2,theta_tilde)
 <= 2||a|| theta_tilde(r_lambda^2)^(1/2).
```

This is precisely the commutator convergence needed by the net-quotient
splitting theorem.  No norm-quasicentrality or countability enters.

## Sharp sequential obstruction

Separability of `I` alone does not produce a sequential norm-quasicentral
approximate unit relative to arbitrary `A`.  For

```text
K(H) direct_sum 0  triangleleft  B(H) direct_sum C,
```

one diagonalizes against any proposed compact approximate-unit sequence:
choose vectors on which a selected subsequence is respectively almost the
identity and almost zero, then join the latter to the former by one partial
isometry.  Its commutators stay asymptotically of norm one.  The scalar trace
on the second summand is nonzero and sees every idempotence defect in the
ideal as zero, so adding a fixed quasitrace does not remove the obstruction.

The exact sequential boundary is therefore:

- a sigma-unital ideal supplies a universal sequence of idempotence cuts;
- a separable ambient algebra permits those cuts to be norm-quasicentral;
- a separable ideal in an arbitrary ambient algebra need not admit any
  sequential relative quasicentral approximate unit;
- trace-linearity on an arbitrary ideal replaces norm-quasicentrality by the
  weaker square-seminorm centrality of an approximate-unit net, which is
  sufficient for extension permanence.

## Scope

Boundedness is used twice: to obtain a finite spectral measure in the
sequential construction and to extend the ideal trace as a finite trace on
`M(I)`.  Sigma-unitality is relevant only to the optional universal sequence,
not to extension permanence.  The result does not settle unrestricted
Problem I, because it assumes quasitrace linearity on both subquotients.
