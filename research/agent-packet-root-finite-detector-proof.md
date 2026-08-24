---
rg: 2
id: agent-packet-root-finite-detector-proof
kind: route
title: Restrict the regular representation of the root-killed quotient to the packet
target: agent-packet-root-finite-detectors-are-normal-quotient-selectors
requires: []
---

Let `L=<<z>>_K`.  The image of `H` in `Q=K/L` is `H/N`, where
`N=H intersect L`.  If the image `bar q` in `C[H/N]` is nonzero, then left
multiplication by `bar q` is a nonzero projection in the regular
representation of `H/N`.  Since

```text
lambda_Q restricted to H/N
  congruent [Q:H/N] lambda_(H/N),                     (FDP1)
```

`lambda_Q(bar q)` has positive normalized trace.  Pulling `lambda_Q` back
to `K` gives `z=1`, proving `(FDS4)` and the necessity of `(FDS3)`.

For sufficiency decompose any finite-dimensional `K`-representation into
irreducibles.  If an irreducible `sigma` kills `z`, it factors through `Q`
and kills `q` by `(FDS3)`.  On every other irreducible the denominator
`||sigma(z)-1||_2^2` is positive.  There are finitely many irreducibles, so
their ratios have a finite maximum `C`.  Both normalized trace of `q` and
squared normalized HS displacement are dimension-weighted averages under
direct sums, proving `(FDS2)` with the same `C`.

Finite groups are dimension-uniformly HS-correctable: average an approximate
action over the fixed group, take the nearby invariant representation, and
round the finite spectral projections.  Since `q` is a fixed group-algebra
polynomial, its trace changes by at most a fixed multiple of the correction
error.  This supplies the robust presentation version.

Frobenius reciprocity gives the equivalent induction statement.  For every
irreducible `eta` of `H/N`, `Ind_(H/N)^Q eta` is nonzero and some irreducible
summand restricts with a copy of `eta`.  Therefore finite induction cannot
remove a packet type which survives `(FDS3)`.

Finally, for an arbitrary `Gamma`, every finite-dimensional representation
of `Gamma/<<z>>` pulls back with zero root displacement.  Hence `(FDS2)`
forces all of them to kill `q`, proving `(FDS5)` and the claimed non-RFD
escape condition.

For completeness, suppose `N=<<z>>` has property `(T)` with squared Kazhdan
constant `kappa` for `s_1,...,s_r`, and each `s_j` is a product of at most
`ell` conjugates of `z` and `z^-1`.  In a representation `rho`, let `P_N` project
onto the `N`-fixed subspace.  Normality makes `P_N` commute with `rho(Gamma)`.
If `q=0` in `C^*(Gamma/N)`, then `rho(q)P_N=0`, so every vector in
`Ran rho(q)` is orthogonal to the `N`-fixed subspace.  The Kazhdan inequality
and an orthonormal basis of `Ran rho(q)` give

```text
Tr rho(q)
 <= kappa^-1 sum_j ||(rho(s_j)-1)rho(q)||_F^2
 <= kappa^-1 sum_j ||rho(s_j)-1||_F^2
 <= r ell^2 kappa^-1 ||rho(z)-1||_F^2.
```

Division by the matrix dimension proves `(FDS6)`.  Conversely, if `q`
survives the full root-killed quotient, a unitary representation of that
quotient detects it while `z=1`; hence no inequality over all unitary
representations is possible.  Ordinary Kazhdan spectral gap can therefore
robustify only the algebraic quotient case.  A non-RFD escape must use a gap
special to finite-dimensional representations.
