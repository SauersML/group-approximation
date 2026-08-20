# Left-right finiteness is the correct building-block hypothesis

Date: 2026-08-19.

Provenance: session development from the manuscript's constant-coordinate counterexample and the existing Kazhdan transport proof architecture.

This note repairs the false attempt to extend Kazhdan transport to every
faithfully traced coordinate algebra and gives a genuine infinite-dimensional
class of building blocks for which the full non-MF obstruction survives.

## 1. The failed generality

For a finite von Neumann factor `M` in standard form,

```text
M or JMJ = M or M' = B(L^2(M)),
```

which is not a finite C-star algebra when `M` is infinite-dimensional.  Thus
the old sentence that `M tensorbar M^op` surjects normally onto `M or JMJ`
and therefore makes the latter finite cannot be used: the represented
left-right algebra need not be a finite quotient.  The manuscript's constant
coordinate example `A_n=C*_r(E)` is an explicit group-theoretic failure of
the resulting transport theorem.

The true bookkeeping facts for a faithfully traced unital C-star algebra are
still useful: it is finite, nonzero corners inherit faithful normalized
traces, and projections in a norm corona can be rounded to coordinate
projection lifts.

## 2. Correct hypothesis

For `(A,tau)`, define

```text
D_tau(A)=C*(L_a,R_b:a,b in A) <= B(L^2(A,tau)).
```

Assume `D_tau(A)` itself is finite.  For a sequence of such coordinates the
norm ultraproduct `prod_omega D_(tau_n)(A_n)` is finite by coordinate polar
correction: an ultraproduct isometry can be represented by coordinate
isometries, and those are unitaries in finite coordinates.

Now every adjoint action is an element of this finite norm ultraproduct:

```text
Ad U_n(g)=L_(U_n(g)) R_(U_n(g)^*).
```

Operator-norm multiplicativity of `U_n` makes these adjoint actions
operator-norm multiplicative.  The Kazhdan spectral projection `P` therefore
belongs to the finite ultraproduct.  The one-sided subgroup relation gives
`P<=VPV^*`, and unitary conjugacy gives `P~VPV^*`; finiteness forces equality.
This is exactly the matrix transport proof with the load-bearing property
named directly.

## 3. Corners preserve the hypothesis

Let `q` be a nonzero projection and `e=L_qR_q`.  After renormalizing the trace,
`L^2(qAq,tau_q)` identifies with `eL^2(A,tau)` up to a scalar rescaling.  For
`a,b in qAq`, the corresponding left/right operators are restrictions of
`eL_a e` and `eR_b e`.  Hence

```text
D_(tau_q)(qAq) <= e D_tau(A) e.
```

A corner of a finite C-star algebra is finite, as is a unital C-star
subalgebra.  Thus the negative spectral corner and finite-normal isotypic
corner used by the obstruction stay in the same class.

This yields the central-sign and finite-normal contradictions exactly as in
the matrix case, with each corner normalized by its own faithful trace.

## 4. Examples

* finite-dimensional C-star algebras: the left-right algebra is
  finite-dimensional;
* commutative C-star algebras with faithful trace: left and right
  multiplication coincide, so the left-right algebra is commutative;
* AF algebras with faithful trace, hence UHF algebras: the left/right
  representation is an image of `A tensor A^op`; this tensor product is AF,
  and the image is an AF quotient, hence finite.

So the obstruction genuinely survives beyond matrix blocks.  What fails for
arbitrary faithfully traced coordinates is not trace faithfulness or corner
lifting but finiteness of the *left-right representation algebra*.

## Trust boundary

This is an informal proof, not a Lean theorem.  It reuses only standard
C-star facts plus the already formalized matrix proof architecture.  The
constant-coordinate counterexample in the manuscript is the regression test:
any proposed coordinate class containing that example without an additional
hypothesis is too large.
