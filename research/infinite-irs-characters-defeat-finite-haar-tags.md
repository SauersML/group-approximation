---
rg: 2
id: infinite-irs-characters-defeat-finite-haar-tags
kind: claim
title: An infinite-subgroup IRS character is nonregular on every finite-index subgroup
distinct_from:
  character-diracization-limit: that intersects independent IRS samples and obtains the regular character of the normal-core quotient only in a limit; this gives an exact obstruction on every finite-index subgroup of the original actor.
  haar-tag-cancellation-retention-is-group-realizability: that characterizes arbitrary tag cancellation by regularity on the tag-zero kernel; this proves that the required regularity is impossible for every finite tag when the payload is an infinite-subgroup IRS character.
  finite-invariant-partition-only-reduces-irs-to-fiber-irs: that conditions the IRS over a finite invariant partition and retains a fiber IRS; this concerns restriction of the original IRS character to finite-index actor subgroups and uses no auxiliary partition.
---

Let `mu` be a random subgroup of a countable group `Gamma`, supported on
infinite subgroups, and put

```text
chi_mu(g)=mu({H:g in H}).                                  (IFT1)
```

Then for every finite-index subgroup `K<=Gamma` there is a nonidentity
element `k in K` such that

```text
chi_mu(k)>0.                                                (IFT2)
```

Consequently `chi_mu|_K` is never the regular character of `K`.  In
particular, for every homomorphism to a finite group

```text
eta:Gamma -> F,
N=ker(eta),
```

the tag-zero restriction `chi_mu|_N` is nonregular.  Hence the diagonal
finite-Haar-tag construction of
`haar-tag-cancellation-retention-is-group-realizability` cannot turn this IRS
character into the canonical trace of a group.

Indeed, for every infinite subgroup `H<=Gamma`, the subgroup `H intersect K`
has finite index in `H`, at most `[Gamma:K]`, and is therefore infinite.  In
particular it contains a nonidentity element.  Thus

```text
1
=mu({H:H is infinite})
<=mu(union_(k in K minus {e}) {H:k in H}).                  (IFT3)
```

The union is countable.  If every set in it had measure zero, its union would
have measure zero, contradicting `(IFT3)`.  This proves `(IFT2)`.  Notice that
invariance of `mu` is not needed for the counting argument; invariance is only
what makes `(IFT1)` a character.

The result applies directly to the Manzoor non-cohyperlinear IRS, whose random
stabilizer is infinite almost surely.  It closes a tempting countable-group
shortcut: no finite quotient of the native free actor can supply a tag which
is faithful enough on the positive IRS moments.  Increasing the finite tag
does not help, since the obstruction holds separately for every finite-index
kernel.  An infinite tag can have trivial kernel, but then exact tag
cancellation erases the payload; if it has a nontrivial regular kernel which
retains the non-CE algebra, that kernel is already the group-factor
realization required by the main problem.
