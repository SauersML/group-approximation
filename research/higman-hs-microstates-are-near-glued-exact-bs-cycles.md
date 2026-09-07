---
rg: 2
id: higman-hs-microstates-are-near-glued-exact-bs-cycles
kind: claim
title: Higman HS microstates are exactly near-glued cycles of exact Baumslag--Solitar packets
artifacts:
  - research/artifacts/higman-cycle-bs-stability-gate-2026-08-21.md
  - research/artifacts/higman-hs-word-coefficient-lower-bound.md
  - research/artifacts/higman-qutrit-coefficient-bound.md
distinct_from:
  split-higman-cycle-has-haar-marginals-and-maximal-role-gap: that exhibits exact independent edge packets whose occurrence seams stay maximally large; this proves the quantitative equivalence after the seams tend to zero.
  one-product-holonomy-does-not-sew-four-bs-clocks: that refutes one scalar replacement for the four seams; this identifies the full four-seam problem with marked HS collapse for the actual Higman group.
  higman-host-restriction-stops-at-separating-partial-models: that concerns restricting microstates of an arbitrary Higman embedding host to an infinitely presented FFGS subgroup; this concerns the finite Higman four-cycle presentation itself.
---

Write Higman's group as

```text
Hig=<g_0,g_1,g_2,g_3 |
     g_i g_(i+1) g_i^(-1)=g_(i+1)^2, i in Z/4Z>.     (HBS1)
```

Let `omega_BS(delta)->0` be a same-dimension normalized-HS stability modulus
for `BS(1,2)`, available from Levit--Vigdorovich's HS stability of
`BS(1,n)`.

There is a quantitative two-way reduction between `delta`-microstates of
`(HBS1)` and exact edge representations

```text
(C_i,Z_(i+1)),
C_i Z_(i+1) C_i^(-1)=Z_(i+1)^2,                       (HBS2)
```

on one common matrix space whose repeated-generator seams

```text
eta=max_i ||C_i-Z_i||_2                               (HBS3)
```

are small:

1. A `delta`-microstate `(U_i)` yields exact packets `(HBS2)` with
   `||C_i-U_i||_2, ||Z_(i+1)-U_(i+1)||_2 <= omega_BS(delta)`, and hence
   `eta<=2 omega_BS(delta)`.
2. Exact packets with seam `eta` yield an `(at most 3 eta)`-microstate by
   setting `U_i=C_i`.

For item 2, replace `C_(i+1)` by `Z_(i+1)` in the conjugated occurrence at
cost `eta` and in its square at cost at most `2 eta`.

Every exact finite-dimensional representation of `Hig` is trivial: Higman's
group has no nontrivial finite quotient, while a nontrivial finitely
generated linear image would have a nontrivial finite quotient by Malcev.
Therefore the following are equivalent:

```text
(a) Hig is normalized-HS stable;
(b) every sequence of exact BS edge packets with eta->0 has
    max_i ||C_i-1||_2 ->0;
(c) every Higman microstate sequence has max_i ||U_i-1||_2 ->0.
                                                               (HBS4)
```

Likewise, failure of the single marked conclusion `||C_0-1||_2->0` in (b)
is exactly a separating normalized-HS microstate for the finite-residual
generator `g_0`.

Thus normalized-HS stability of the four BS vertex groups has already been
used completely when passing from `(HBS1)` to `(HBS2)--(HBS3)`.  It does not
force the mark to collapse.  The missing input is a dimension-free **near-
amalgamation theorem for the four exact packets**.  Proving it would prove
that Higman's group is nonhyperlinear; constructing a noncollapsing seam
cycle would give the requested explicit marked microstate escape.  Neither
conclusion follows from the BS stability theorem itself.

## Attempts

`three-higman-bs-seams-vanish-fourth-is-product-holonomy` classifies the exact
packets and tests the periodic-clock sector.  Optimal spectral transport
makes any three consecutive seams tend to zero while all four conjugator
occurrences stay at distance `sqrt(2)` from identity.  For four gauged copies
of one packet, the complete remaining condition is that four approximate
spectral matchers `P -> D` have ordered product one.  In the homogeneous
choice it is the single residual term `||[H^4,P]||_2`.  Thus no proper
subcycle uncertainty estimate can prove collapse; the fourfold matcher
holonomy is the narrowed terminal.

The exact coefficient test in
`higman-hs-word-coefficient-exceeds-nine-fifths` rules out the proposed
bound `e_(g_0)<=C sum_i e_(r_i)` whenever
`C<2748800041/1512087866`, already on rational 2-by-2 matrices.
This includes C=9/5. No valid larger coefficient is established. These
are positive-defect tuples; identity padding makes their marked energy
vanish too, so they do not solve either side of the seam problem.

The three-dimensional continuation
`higman-hs-word-coefficient-exceeds-sixteen` gives explicit rational
matrices with `e_(g_0)>16/7` and `sum_i e_(r_i)<1/7`. Every valid
all-dimensions coefficient must therefore exceed sixteen. In particular,
the earlier finite search at coefficient two missed a counterexample
in dimension three. These are still positive-defect tuples, with no
separating zero-defect limit.
