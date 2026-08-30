# Problem I: sigma-unital extension permanence and the sequential boundary

## Outcome

Bounded-quasitrace linearity is closed under an extension

```text
0 -> I -> A -> A/I -> 0
```

when `A` is unital and `I` is sigma-unital.  Both the ideal and quotient are
assumed to have bounded-quasitrace linearity.  The ambient algebra need not
be separable or exact.

For a bounded ambient quasitrace `tau`, its restriction to `I` is a bounded
trace `theta`.  An increasing functional-calculus approximate unit becomes
asymptotically idempotent in the `tau` square seminorm.  Although that
sequence need not be norm-quasicentral, its commutators with every ambient
element tend to zero in the `theta` square seminorm.  The existing
quasitracial sequence-tail splitting theorem then applies.

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

For the permanence theorem, `theta=tau|I` is already a trace.  Both `e_n`
and `e_n^2` are approximate units, so

```text
theta(e_n), theta(e_n^2) -> ||theta||.
```

Since `(e_n-e_n^2)^2 <= e_n-e_n^2`, this proves the idempotence limit
without spectral measures.  The spectral argument remains useful because
it proves the construction for an arbitrary fixed bounded quasitrace before
any ideal-linearity assumption is made.

## Why ambient commutators still vanish

The trace `theta` extends canonically to a finite trace on `M(I)`.  With
`r_n=1-e_n`,

```text
theta_tilde(r_n^2)
 = ||theta||-2theta(e_n)+theta(e_n^2) -> 0.
```

The action of `A` on `I` is a contractive star homomorphism into `M(I)`, and

```text
||[e_n,a]||_(2,theta_tilde)
 <= 2||a|| theta_tilde(r_n^2)^(1/2).
```

This is precisely the commutator hypothesis needed by the sequence-quotient
splitting theorem.  No norm-quasicentrality or separability of `A` enters.

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

The exact boundary is therefore:

- a sigma-unital ideal always supplies the required idempotence cuts;
- a separable ambient algebra permits those cuts to be norm-quasicentral;
- a separable ideal in an arbitrary ambient algebra need not admit any
  sequential relative quasicentral approximate unit;
- trace-linearity on the ideal replaces norm-quasicentrality by the weaker
  square-seminorm centrality needed for extension permanence.

## Scope

Boundedness is used twice: to obtain a finite spectral measure and to extend
the ideal trace as a finite trace on `M(I)`.  Sigma-unitality supplies a
sequence rather than a net.  The result does not settle unrestricted
Problem I, because it assumes quasitrace linearity on both subquotients.
