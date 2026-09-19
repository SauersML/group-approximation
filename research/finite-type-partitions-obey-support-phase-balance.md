---
rg: 2
id: finite-type-partitions-obey-support-phase-balance
kind: claim
title: Escaped finite-type partitions obey coefficientwise phase balance with no support leaves
artifacts:
  - research/finite-type-support-phase-balance-proof.md
distinct_from:
  finite-type-restriction-overlap-defect-formula: that computes pairwise positive L2 overlap from restriction data; this extracts the independent signed Fourier equations forced by the additive partition itself.
  term-pairing-does-not-bypass-signed-hecke-holonomy: that explains why imposing paired coefficient equalities does not preserve projection structure for free; this identifies exactly when a finite-type partition has already reduced to such pairings.
  finite-type-additive-overlap-obeys-row-column-capacity: that gives trace-capacity inequalities for two partitions; this gives element-by-element phase equations and applies already to one escaped context partition.
---

Let `K,H_1,...,H_n` be finite subgroups of a group `Gamma`, let

```text
pi in Irr(K),       rho_a in Irr(H_a),
q=z_(K,pi),         p_a=g_a z_(H_a,rho_a) g_a^(-1),
A_a=g_a H_a g_a^(-1).
```

Write `rho_a^g` for the transported irreducible character on `A_a` and
define, for `s in Gamma`,

```text
c_a(s)=d_a/|A_a| chi_(rho_a^g)(s^(-1))  if s in A_a,
       =0                                otherwise.     (SPB1)
```

If the `p_a` form a context partition of the root type,

```text
p_a p_b=0 (a!=b),             sum_a p_a=q,             (SPB2)
```

then the following finite equations are necessary:

```text
sum_a d_a^2/|A_a|=d_pi^2/|K|,                          (SPB3)

sum_a c_a(s)=d_pi/|K| chi_pi(s^(-1))  for s in K,
sum_a c_a(s)=0                         for s notin K.   (SPB4)
```

Consequently the effective support hypergraph outside `K` has no leaves:
every `s notin K` for which some `c_a(s)` is nonzero belongs to the
character support of at least two atoms. If exactly two coefficients are
nonzero at `s`, then they are antipodal with exactly equal modulus,

```text
c_a(s)=-c_b(s).                                        (SPB5)
```

More generally, the nonzero coefficients at every escaped support element
have zero in their convex hull; in particular they cannot all lie in one
open half-plane through the origin.

This gives a sharp syntax gate for
`finite-type-restriction-incidence-atlas-for-nonce-bcs`. A candidate can be
discarded before any restriction-inner-product computation if one escaped
support element is used by only one atom, or if its incident character
phases lie in an open half-plane. If every escaped support element has degree
two, all cancellation is coefficientwise term pairing and the construction
still has to solve the coherent cycle equations isolated by
`term-pairing-does-not-bypass-signed-hecke-holonomy`. Therefore a route
which does not solve that holonomy gate must contain an escaped support
element with at least three incident nonzero character coefficients.

There is also a useful positive-character boundary. If, at each
`s notin K`, all `c_a(s)` are nonnegative real numbers, then they all
vanish. Hence every `p_a` lies in `C[K]`, and `(SPB2)` is a partition
inside the finite root block `q C[K] q`. Such a packet is matricial and
cannot be a no-CE atlas.
