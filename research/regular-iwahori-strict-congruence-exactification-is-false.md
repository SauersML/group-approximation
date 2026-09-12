---
rg: 2
id: regular-iwahori-strict-congruence-exactification-is-false
kind: claim
title: Regular Iwahori congruence exactification fails without flexible padding
distinct_from:
  regular-iwahori-relative-congruence-exactification: that is the corrected flexible target in generalized Hilbert--Schmidt distance; this refutes only its former same-dimensional formulation.
  sl2-half-explicit-strict-flexible-separation: that gives a central-trivial PSL2 near-representation; this balances it with a negative-central odd Weil endpoint to satisfy the regular-trace hypothesis for SL2.
  iwahori-local-global-defect-question: that is Dogon--Vigdorovich's flexible question and permits an asymptotically negligible dimension enlargement; the countersequence here is repaired by exactly one added line.
---

Put

```text
Gamma=SL_2(Z[1/2]),       C_+=C_-=SL_2(Z),
d_p=(p-1)/2.
```

Let `p` run through primes congruent to `5 mod 8`. There are exact
same-dimensional modular-vertex pairs

```text
pi_(p,+),pi_(p,-):C_+*C_- -> U(2d_p)                  (RSC1)
```

such that their Iwahori mismatch is `O(p^(-1/2))`, the induced
homomorphism of `Gamma` in the tracial matrix ultraproduct has the
regular character of **SL2**, and one constant `c>0` satisfies

```text
inf_(sigma:Gamma->U(2d_p)) d_2(pi_p,sigma)>=c          (RSC2)
```

for all sufficiently large `p`. Here an exact `sigma` is read as its two
compatible vertex restrictions. All fixed generating-set metrics are
interchangeable up to universal word-length constants.

More quantitatively, let `K` be the universal same-dimensional repair
constant for exact congruence vertex pairs. For every exact congruence
pair `rho_p` on `2d_p`,

```text
d_2(pi_p,rho_p) >= c-K def(rho_p).                     (RSC3)
```

Consequently no sequence of same-dimensional congruence pairs can be both
`o(1)`-close to `pi_p` and have Iwahori defect tending to zero. This
refutes the literal same-dimensional version formerly stated at
`regular-iwahori-relative-congruence-exactification`.

The central balance is load-bearing. The positive-central summand is the
torsion-normalized compression of the even Weil endpoint, of dimension
`d_p`. The other summand is the exact irreducible odd Weil endpoint, also
of dimension `d_p`, on which `-I` acts by `-1`. Thus the normalized trace
of `-I` is exactly zero, rather than one as it is for the central-trivial
compressed packet alone.

This is **not** a counterexample to Dogon--Vigdorovich's question in its
generalized flexible metric. Restoring the one deleted positive-central
line gives the exact representation

```text
E_p direct-sum O_p:Gamma->U(2d_p+1),                  (RSC4)
```

at generalized distance `O(p^(-1/2))`, and
`(2d_p+1)/(2d_p)->1`. The surviving open theorem must therefore allow
`o(d_p)` padding, or equivalently use generalized `d_2`.
