---
rg: 2
id: flexible-bs-cycle-surgery-absorbs-exact-coboundaries
kind: claim
title: Flexible BS cycle surgery absorbs every exact low-mode coboundary
distinct_from:
  solenoid-absorption-cascade-converges: that must also remove the cycle-holonomy obstruction and produce a coboundary for the actual Weyl residual; this starts with an exact coboundary and removes its large inverse norm by flexibly changing the exact BS core.
  two-jump-cycle-refutes-functional-calculus-gauge-bound: that keeps the cyclic shift fixed; this cuts its two jump boundaries and turns the two plateaux into exact reducing cycles.
  bs14-exact-representation-variety-is-hs-locally-rigid: that aligns two nearby exact BS representations; this permits a small flexible change of one exact representation to absorb a far correcting gauge.
  pure-cycle-surgery-rate-contains-quantitative-z2-repair: that isolates the stronger quantitative theorem hidden in extending the pure long-cycle rate to length-one return monodromy; this retains the unconditional universal commuting-pair modulus.
---

Let `(V,H)` be an exact finite-dimensional `BS(1,4)` representation,
`H V H^(-1)=V^4`, with `V` of odd finite order.  Put `Z={V}'` and
`psi=Ad(H)|Z`.  Suppose `c in U(Z)` and

```text
e=c psi(c)^(-1),       ||e-1||_2=delta.                (FCS1)
```

Then there is a dimension-free modulus `g(delta)->0`, an exact BS pair
`(V~,H~)` in the same dimension, and `c_0 in U({V~,H~}')` such that

```text
||V-V~||_2+||H-H~||_2+||c-c_0||_2 <= g(delta).         (FCS2)
```

More quantitatively, for every integer `K>=2` the long fourth-power cycles
admit the bound

```text
C K delta+C/sqrt(K),                                  (FCS3)
```

while cycles of length at most `2K` add only the universal normalized-HS
almost-commuting-unitary modulus evaluated at `O(K delta)`.  With Glebsky's
explicit theorem, the complete estimate is

```text
C(K delta+K^(-1/2))+C(2K delta)^(1/9).                (FCS4)
```

Choosing
`K->infinity` and `K delta->0` proves `(FCS2)`.

Thus the unbounded inverse of `1-psi` is not itself a flexible-stability
obstruction.  A low-mode gauge can be converted into a multiplicity-
commutant gauge by cutting long cycles into periodic shadows.  What remains
for the actual Iwahori residual is the existence/Livsic holonomy problem:
`(FCS1)` is not automatic.  This theorem does not prove
`solenoid-absorption-cascade-converges`; it removes low-mode norm growth
after exact solvability and isolates finite cycle holonomy as the survivor.
