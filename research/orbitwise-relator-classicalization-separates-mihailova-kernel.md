---
rg: 2
id: orbitwise-relator-classicalization-separates-mihailova-kernel
kind: claim
title: Orbitwise relator classicalization of a Mihailova wreath model forces its kernel to be separable
distinct_from:
  mihailova-actor-liftable-ce-forces-q-hyperlinear: that reads the left-right quasi-regular coefficient from exact actor lifts and concludes hyperlinearity of Q; this uses the single vertical SL3 coset lamp and a finite classical orbit to conclude profinite separability of N in SL3.
  simple-lamp-hyperlinear-recovery-forces-action-sofic: that asks for full sofic-action charts from arbitrary microstates of a nonabelian-simple lamp wreath; this proves only subgroup separability, under an explicit orbitwise kernel hypothesis, for the binary Mihailova lamp.
  projective-trace-square-transfer-for-sl3-pair: that is a dimension-free commutant estimate for the dyadic arithmetic pair; this identifies a different exactification-plus-classicalization hypothesis and proves that projective transfer alone does not supply its orbitwise clause.
---

Let

```text
E=F_m < L=SL_3(Z),       Q=<x_1,...,x_m | r_1,...,r_t>,
pi:E->Q,                 N=ker(pi)=normal_closure_E(R),
R={r_1,...,r_t},         W_N=(direct_sum_(L/N) C_2) rtimes L.    (ORC1)
```

Write `a=a_N` for the centered binary lamp at the base coset.  Suppose a
hyperlinear model of `W_N` has a **regular orbitwise-relator classicalized
subsequence**: there are self-adjoint unitaries `A_j in M_(d_j)` and exact
projective representations `V_j:L->U(d_j)` such that

```text
tr(A_j Ad(V_j(g))(A_j)) -> 1_(g in N)                  (ORC2)
```

for every `g in L`, and, putting

```text
O_j^L={Ad(V_j(l))(A_j):l in L},
O_j^E={Ad(V_j(e))(A_j):e in E}.                        (ORC3)
```

every defining relator acts trivially on the whole **free-subgroup orbit**:

```text
Ad(V_j(r))(B)=B       (r in R, B in O_j^E).            (ORC4)
```

Then `N` is separable in `L`.

The `L`-orbit finiteness needed here is automatic from the displayed exact
projective format: `Ad V_j` is an exact finite-dimensional unitary
representation of `SL_3(Z)`, hence has finite image by higher-rank
superrigidity.  More abstractly the theorem needs only that `O_j^L` is finite
and that the resulting `L`-action is exact.

For the Mihailova choice with non-residually-finite `Q`, this is impossible:
separability of `N` in `L` would imply separability in `E`, and because `N`
is normal it would make `Q=E/N` residually finite.  Thus any hypothetical
hyperlinear model of `W_N` must fail at least one of exact projective actor
lifting or orbitwise relator classicalization.

The free-subgroup orbit is the weakest natural exact clause: it is precisely
what holds in the canonical action because `N` is normal in `E`, while the
relators generally do not fix lamp coordinates outside `E/N`.

The word **orbitwise** is load-bearing.  Requiring each `r in R` to fix only
the seed `A_j` does not suffice, even with zero actor defect and a finite
permutation orbit.  Conjugates of `r` need not fix the seed, so the normal
closure `N` need not lie in the finite action kernel.
