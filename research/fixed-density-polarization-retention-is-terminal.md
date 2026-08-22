---
rg: 2
id: fixed-density-polarization-retention-is-terminal
kind: claim
title: Fixed-density retention under character polarization already produces a canonical non-CE quotient
distinct_from:
  diagonal-tensor-trace-powers-forget-full-gns-tensor: that records the absence of any automatic recovery map from a diagonal tensor algebra; this identifies the consequence if a positive-weight recovery summand is actually constructed
  free-label-orthogonalization-erases-payload-trace: that analyzes independent free labels and their cancellation; this is an abstract domination theorem for any convergent family of characters
  unnamed-positive-density-fixed-space-is-terminal: that turns an approximate fixed contraction into a forbidden canonical moment; this turns a retained non-CE subrepresentation into a non-CE canonical quotient factor
---

Let `G` be countable, let `tau` be a character of `G`, and suppose that
characters `sigma_k` converge pointwise to the subgroup character

```text
phi_H(g)=1_{g in H},                                    (FPR1)
```

where `H` is normal.  Suppose there is a constant `beta>0` and, for every
`k`, a character `rho_k` and a number `beta_k>=beta` such that

```text
sigma_k=beta_k tau+(1-beta_k)rho_k.                     (FPR2)
```

Equivalently, the tracial representation of `sigma_k` has a reducing
summand of trace weight at least `beta` whose normalized character is
`tau`.  Then

```text
beta tau <= phi_H                                      (FPR3)
```

in positive-functional order.  Consequently `tau` factors through
`Q=G/H`, is normal with bounded central Radon--Nikodym density relative to
the canonical trace of `L(Q)`, and its GNS von Neumann algebra is a central
summand of `L(Q)`.

If `Q` is ICC, this is sharper: `L(Q)` is a factor, so the central density is
scalar and normalization forces `tau=phi_H`.  Thus an ICC canonical limit
cannot retain at fixed density any genuinely different factor character.

In particular, if the GNS algebra of `tau` is not Connes embeddable, then
`L(Q)` is not Connes embeddable and `Q` is non-hyperlinear.  Thus a
fixed-positive-density retention mechanism compatible with polarization is
already terminal: it does not merely help promote the bad trace; it proves
that the canonical factor of the polarized quotient is bad.

For diagonal tensor powers this gives a particularly explicit test.  Put

```text
H_tau={g in G: |tau(g)|=1}.                             (FPR4)
```

This is a normal subgroup, and `tau|H_tau` is a one-dimensional character.
There is an unbounded sequence `n_k` for which

```text
tau(g)^(n_k) -> 1_{g in H_tau}.                         (FPR5)
```

Therefore, if the diagonal tensor character `tau^(n_k)` contains the
original non-CE character with uniformly positive trace weight, then the
explicit quotient `G/H_tau` is non-hyperlinear.

A necessary finite-matrix inequality for any proposed retention is: for
every finite list `g_1,...,g_m` and scalars `c_1,...,c_m`,

```text
 beta sum_ij conj(c_i)c_j tau(g_i^-1 g_j)
 <= sum_ij conj(c_i)c_j tau(g_i^-1 g_j)^n.              (FPR6)
```

This positive-kernel domination, not merely pointwise comparison of scalar
moments, is the correct audit test for a claimed retained summand.
Already the two-point set `{e,g}` forces

```text
|tau(g)^n-beta tau(g)| <= 1-beta.                       (FPR8)
```

The full family `(FPR6)` is stronger and is exactly what self-similar fusion
or recursive-corner proposals must verify.

The conclusion is sharp even for ordinary representation fusion.  For the
normalized character `tau=chi_std/2` of the two-dimensional standard
representation of `S_3`, `tau^n` converges to the canonical character, while
the standard summand has trace weight tending to `2/3`.  It is precisely the
`M_2` central Plancherel block of `L(S_3)`, as the theorem predicts.
