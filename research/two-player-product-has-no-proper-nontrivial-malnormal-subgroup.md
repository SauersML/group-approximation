---
rg: 2
id: two-player-product-has-no-proper-nontrivial-malnormal-subgroup
kind: claim
title: A direct product of two nontrivial groups has no proper nontrivial malnormal subgroup
distinct_from:
  toric-gap-is-a-relative-fd-central-word-face: that identifies the relative finite-dimensional character face and normal quotient for toric clauses; this rules out the strongest malnormal/Cohen-Lyndon construction of that face
  spherical-root-type-selection-is-phase-unsafe: that audits finite spherical roots and their graph characters; this concerns infinite clause subgroups in the full two-player direct product
---

ESTABLISHED.  Let `A` and `B` be nontrivial groups.  If

```text
K <= A x B
```

is malnormal and nontrivial, then `K=A x B`.  Consequently the universal
two-player game group admits no proper nontrivial malnormal clause subgroup.

## Proof

For a malnormal subgroup, every nonidentity `k in K` satisfies

```text
C_(A x B)(k) <= K,                                    (DPM1)
```

because a centralizer element `g` makes `k` lie in
`K intersect gKg^(-1)`.

Choose `1!=(a,b) in K`.  The elements `(a,1)` and `(1,b)` commute with
`(a,b)`, so every one which is nontrivial lies in `K` by `(DPM1)`.

If `a!=1`, then `(a,1) in K`, and its centralizer contains the whole factor
`{1} x B`; hence `{1} x B <= K`.  Since this factor is nontrivial and normal
in `A x B`, every conjugate of `K` intersects `K` nontrivially.  Malnormality
therefore leaves no element outside `K`, so `K=A x B`.  The case `b!=1` is
symmetric.  At least one case applies.

## Consequence for the toric lane

A tempting infinite replacement for the failed finite spherical root is to
choose an infinite-index malnormal `K`, use a character on `K`, and invoke a
Cohen--Lyndon/free-normal-closure theorem to extend the phase consistently
over all conjugates.  The theorem rules out that architecture in the required
direct-product player group before representation theory enters.

The surviving infinite character-face construction must therefore exploit a
highly non-malnormal subgroup.  It must simultaneously satisfy:

1. invariant phase extension over its normal closure;
2. infinite index, since finite-index faces have finite monomial models; and
3. exclusion of the entire face from finite-dimensional state closure.

Those are exactly the phase-factorization and relative-FD conditions already
isolated in `toric-gap-is-a-relative-fd-central-word-face`.  Thus replacing a
finite packet by a malnormal infinite root does not lower the terminal
compiler gate.

## Attempts

The proposed escape was an infinite malnormal character pair `(K,chi)` whose
normal closure is a free product of conjugates, making the phase extension
transparent.  It dies by `(DPM1)`: direct-product centralizers force a whole
player factor into `K`, and that normal factor contradicts proper
malnormality.

