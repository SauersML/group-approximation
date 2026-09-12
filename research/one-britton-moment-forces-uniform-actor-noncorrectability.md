---
rg: 2
id: one-britton-moment-forces-uniform-actor-noncorrectability
kind: claim
title: The one-Britton canonical moment forces a uniform distance from every exact arithmetic actor
distinct_from:
  one-britton-commutator-excludes-exact-arithmetic-actor-sector: that treats actor distance zero and gives a convenient infeasibility threshold; this keeps the actor distance as a parameter and proves the explicit quantitative lower bound.
  homogeneous-quotient-ce-forces-sl3-outlier-at-large-primes: that uses the homogeneous-quotient cell structure and large-prime depth theorem to force flexible outliers; this uses only the HNN centrality relators and the single canonical moment of [t,h], and controls same-dimension exact actor distance on S union {h}.
  sl3-hnn-finite-window-central-dual-gap: that must bound every stable-letter-central matrix-range separator once arbitrary actor outliers are allowed; this proves the precise finite noncorrectability inequality which any such outlier automatically satisfies.
---

Fix a prime `p`, put

```text
Lambda=SL_3(Z), Gamma=SL_3(Z[1/p]), h=diag(p,1,1/p),
```

and let `S` be a finite symmetric Kazhdan generating set of `Lambda`, with
Kazhdan constant `kappa>0` in normalized Hilbert--Schmidt norm.  Let

```text
X_s in U(d) (s in S),       H,T in U(d).
```

Define the lattice-centrality and canonical Britton-moment errors

```text
delta_C=max_(s in S)||[T,X_s]-I||_2,
delta_B=|tr_d([T,H])|,                                      (BNC1)
```

and the same-dimension exact arithmetic actor distance

```text
zeta=inf_(rho:Gamma->U(d))
     max( ||H-rho(h)||_2, max_(s in S)||X_s-rho(s)||_2 ).     (BNC2)
```

Then

```text
zeta >=
 [ sqrt(2(1-delta_B))-(2 sqrt(|S|)/kappa)delta_C ]_+
 / (2+4 sqrt(|S|)/kappa).                                   (BNC3)
```

In particular, along any finite HNN presentation assignments for which the
centrality relators tend to zero and the single nontrivial word `[t,h]` has
canonical trace tending to zero,

```text
liminf zeta >= sqrt(2)/(2+4 sqrt(|S|)/kappa)>0.               (BNC4)
```

Thus one fixed mixed Britton moment already forces a uniform actor outlier;
no growing canonical window is needed for this noncorrectability statement.

## Proof

Fix an exact `rho:Gamma->U(d)` and put

```text
zeta_rho=max( ||H-rho(h)||_2,
              max_(s in S)||X_s-rho(s)||_2 ).
```

The unitary commutator word is `2`-Lipschitz in either actor coordinate, so

```text
max_(s in S)||[T,rho(s)]-I||_2 <= delta_C+2 zeta_rho.          (BNC5)
```

Let `Q` be the Hilbert--Schmidt projection onto `rho(Lambda)'`.  Property
`(T)` gives

```text
||T-Q(T)||_2
 <= sqrt(|S|)(delta_C+2 zeta_rho)/kappa.                       (BNC6)
```

Finite-dimensional arithmetic co-density gives
`rho(Lambda)'=rho(Gamma)'`, so `Q(T)` commutes with `rho(h)`.  The same
commutator Lipschitz estimate at `h` yields

```text
||[T,H]-I||_2
 <= (2 sqrt(|S|)/kappa)(delta_C+2 zeta_rho)+2 zeta_rho.        (BNC7)
```

For `W=[T,H]`, the exact trace identity and `(BNC1)` imply

```text
1-(1/2)||W-I||_2^2=Re tr_d(W)<=|tr_d(W)|=delta_B,
```

hence `||W-I||_2>=sqrt(2(1-delta_B))`.  Combine this with `(BNC7)`, solve
for `zeta_rho`, and take the infimum over `rho` to obtain `(BNC3)`.

## Scope

The distance in `(BNC2)` is same-dimensional and uses only the finite actor
packet `S union {h}`.  Passing to flexible compressions requires the separate
Kazhdan/Stinespring matrix-range exactification step; it is not silently
claimed here.  Conversely no arithmetic presentation defect appears in the
estimate beyond its contribution to the displayed matrices and centrality
relations: once an exact comparison representation is proposed, `(BNC3)` is
dimension-free.
