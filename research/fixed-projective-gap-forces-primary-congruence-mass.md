---
rg: 2
id: fixed-projective-gap-forces-primary-congruence-mass
kind: claim
title: A fixed SL3 projective far gap forces positive denominator-primary congruence mass
artifacts:
  - research/artifacts/sl3-primary-mass-extraction-2026-08-22.md
distinct_from:
  sl3-odd-correctable-sector-has-uniform-projective-modulus: that closes exact corrections whose entire congruence level is coprime to p; this quantitatively extracts a positive p-primary dimension mass from every mixed-level correction supporting a fixed far gap.
  sl3-near-exact-leaks-live-in-the-two-primary-tower: that confines the exact quasi-regular leak profile to the two-primary tower; this applies to arbitrary auxiliary unitaries and projective trace-square witnesses, with an explicit square-root mass interface.
  bounded-conductor-width-pays-uniform-first-exit: that lower-bounds boundary loss from the number of occupied conductor depths; this lower-bounds the total positive-depth mass before asking how it is distributed across depths.
---

Put

```text
Gamma=SL_3(Z[1/p]),       Lambda=SL_3(Z),
h=diag(p,1,p^(-1)).
```

Let `rho` be a finite-dimensional assignment of ambient defect `delta`, and
suppose `rho|_Lambda` is within generator distance `xi` of an exact unitary
representation `sigma` of `Lambda`.  Decompose `sigma` into irreducibles by
their minimal congruence conductors:

```text
sigma = sigma_coprime direct-sum sigma_primary,
m = dim(sigma_primary)/dim(sigma).                       (PMG1)
```

Here `sigma_coprime` is the sum of irreducibles whose minimal conductor is
coprime to `p`; `sigma_primary` is the sum of all remaining irreducibles, so
each of those has positive `p`-conductor.  For every auxiliary unitary `U`,
write

```text
E_Lambda(U,rho)=sum_(c in S_Lambda)
                 (1-|tr([U,rho(c)])|^2).
```

Let `eta_odd` be the uniform modulus from
`sl3-odd-correctable-sector-has-uniform-projective-modulus`, chosen
nondecreasing.  Then

```text
e(U,rho(h))
 <= eta_odd(delta+xi+2 sqrt(m)+E_Lambda(U,rho)).          (PMG2)
```

Consequently, for every fixed `epsilon>0`, choose any `s_epsilon>0` with
`eta_odd(s_epsilon)<epsilon`.  If

```text
e(U,rho(h)) >= epsilon,
```

then

```text
m >= (1/4)
     (s_epsilon-delta-xi-E_Lambda(U,rho))_+^2.            (PMG3)
```

In particular, along a fixed-gap projective far-sector with ambient defect,
vertex-correction error, and subgroup projective energy tending to zero,

```text
liminf m >= s_epsilon^2/4 > 0.                            (PMG4)
```

Thus the mixed-level residue cannot hide the denominator-prime in a
vanishing-dimensional summand.  A surviving exactifiable enemy must place a
fixed positive fraction of its dimension in irreducibles of positive
`p`-conductor.  This does not bound the conductor depth or prevent that mass
from spreading over an unbounded Folner profile; those are the remaining
contraction/coherence questions.

