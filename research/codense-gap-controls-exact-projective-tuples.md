---
rg: 2
id: codense-gap-controls-exact-projective-tuples
kind: claim
title: A finite-dimensional co-dense conjugation gap controls every exact projective tuple
distinct_from:
  exact-projective-codensity-has-a-uniform-trace-square-gap: that derives projective transfer for honest representations by cancelling source phases using perfectness; this needs no perfectness and treats honest projective representations by applying the ordinary conjugation gap twice.
  sl2-exact-projective-transfer-via-doubled-squeeze: that is the arithmetic rank-one specialization for honest representations; this is the abstract doubled-squeeze lemma and permits arbitrary scalar presentation relators.
  projective-commutant-transfer-for-arithmetic-pair: that concerns arbitrary approximate representations; this requires the adjoint tuple to be an exact representation.
---

Let `C=<S> <= A` be finitely generated and fix `h in A`.  Suppose there is
`kappa>0` such that every finite-dimensional unitary representation
`pi:A->U(D)` has

```text
pi(C)'=pi(A)'                                           (CDG1)
```

and, writing `Q_pi` for the Hilbert--Schmidt orthogonal projection onto
`pi(C)'`,

```text
||X-Q_pi(X)||_2^2
 <= kappa^(-2) sum_(c in S)||pi(c)Xpi(c)^*-X||_2^2     (CDG2)
```

for every `X in M_D`.  Then every finite-dimensional projective unitary
representation `bar(rho):A->PU(d)`, every choice of unitary lifts
`rho(g)`, and every `U in U(d)` satisfy

```text
1-|tr_d([U,rho(h)])|^2
 <= (4/kappa^2) sum_(c in S)
       (1-|tr_d([U,rho(c)])|^2).                       (CDG3)
```

The estimate is independent of `d` and of the multiplier class of
`bar(rho)`.

## Proof

The projective representation has the honest adjoint lift

```text
pi(g)=Ad(rho(g)) in U(M_d).                             (CDG4)
```

Apply `(CDG2)` to the vector `X=Ad(U)` in
`End(M_d)=M_(d^2)`, and put `Y=Q_pi(X)`.  By `(CDG1)`, `Y` commutes with
`pi(h)`, so

```text
||Xpi(h)-pi(h)X||_2 <= 2||X-Y||_2.                     (CDG5)
```

For any unitaries `V,W in U(d)`, unitary invariance of normalized
Hilbert--Schmidt norm and the trace formula for an inner automorphism give

```text
||Ad(V)Ad(W)-Ad(W)Ad(V)||_2^2
 =||Ad([V,W])-I||_2^2
 =2-2|tr_d([V,W])|^2.                                 (CDG6)
```

Square `(CDG5)`, use `(CDG2)`, and substitute `(CDG6)` at `h` and every
`c in S`.  Cancelling the common factor `2` proves `(CDG3)`.

This is an ordinary relative Poincare estimate on the second adjoint
space.  In particular it neither selects a vector on which close
superoperators must agree nor requires an exactification back into the
inner-automorphism locus.
