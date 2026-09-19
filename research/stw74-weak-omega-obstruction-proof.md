---
rg: 2
id: stw74-weak-omega-obstruction-proof
kind: route
title: Stabilize the trace-free projectionless corner and read off a comparison witness
target: stw74-weak-omega-comparison-closes-hinge
requires:
  - stw74-counterexamples-are-unstably-projectionless
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

Assume that `A` is not purely infinite, and choose the nonzero full
projectionless hereditary subalgebra `D` from the required claim.  Brown
stabilization identifies

```text
D tensor K  ~=  A tensor K,                                  (1)
```

so the left side contains a nonzero properly infinite projection.  Hence
`D` is not stable: otherwise an isomorphism `D ~= D tensor K` would put a
nonzero projection in `D`.

We next check the two inputs to property (S).  Simplicity and
projectionlessness show that `D` has no nonzero unital quotient.  If `tau`
were a nonzero bounded lower-semicontinuous 2-quasitrace on `D`, its kernel
would be an ideal, so `tau` and every matrix extension would be faithful.
Choose an infinite projection `q in M_k(D)` and a proper subprojection
`r<q` equivalent to `q`.  Quasitracial additivity on orthogonal positive
elements gives

```text
tau_k(q)=tau_k(r)+tau_k(q-r)>tau_k(r)=tau_k(q),                (2)
```

a contradiction.  Thus `D` has neither a unital quotient nor a bounded
2-quasitrace.

The property-(S) stability mechanism of Ortega--Perera--Rordam now applies.
Since `D` is a full hereditary subalgebra of `A`, `A tensor K` contains a
full projection, and `Cu(A)` has weak omega-comparison, it makes `D` stable.
This contradicts (1) and projectionlessness.  Therefore `A` is purely
infinite.

For the explicit obstruction, take the contrapositive of the same stability
argument.  Nonstability gives `a in D_+` and `epsilon>0` such that no
positive `b` orthogonal to `(a-epsilon/2)_+` satisfies

```text
(a-epsilon)_+ <=_Cu b.                                      (3)
```

Property (S), applied recursively starting at `(a-epsilon/2)_+`, produces
pairwise orthogonal full positives `b_0,b_1,...` in `D`, all orthogonal to
that cutdown, with

```text
(a-epsilon/2)_+ <_s b_0 <_s b_1 <_s ... .                    (4)
```

Set `x=[(a-epsilon/2)_+]`, `x'=[(a-epsilon)_+]`, and
`y_j=[b_j]`.  Then
`x'<<x`, every `y_j` is full, and (4) gives `x<_s y_j`.  If
`x'<=y_0+...+y_n`, the orthogonal sum `b_0+...+b_n` would contradict
(3).  These elements therefore witness failure of weak omega-comparison.

The imported boundary is precisely the property-(S) characterization and
stability construction documented in the artifact.  The absence of
quasitraces, the nonstability contradiction, and extraction of the displayed
witness are internal.
