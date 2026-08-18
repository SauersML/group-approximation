---
rg: 2
id: ce-characters-closed-multiplicative-semigroup
kind: claim
title: The matrix-microstate characters form a closed sub-semigroup of the character semigroup under pointwise product
distinct_from:
  balanced-replica-hs-amplification: that is a quantitative statement about one finite unitary table, bounding the multiplicative defect of a balanced tensor power; this is a qualitative closure property of the whole set of microstate characters, with no defect bookkeeping in it
  character-domination-collapse-equivalences: that is the domination/dimension-escape interface, equating qualitative collapse with one linear constant; this records only that the microstate locus is a closed multiplicative sub-semigroup, which that interface does not state
artifacts:
  - research/artifacts/universal-hyperlinearity-audit-2026-08-18.md
---

ESTABLISHED, elementary.  For a countable group `Gamma` let

```text
Ch(Gamma) = { normalized central positive-definite functions on Gamma },
CE(Gamma) = pointwise closure in Ch(Gamma) of
            { tr_d o pi : pi : Gamma -> U(d), d finite }.
```

`Ch(Gamma)` is compact in the topology of pointwise convergence (it sits in a
product of closed unit disks) and carries the pointwise product, which is the
character of the tensor product of representations.  Then:

1. **`CE(Gamma)` is closed** under pointwise limits -- by construction, it is
   a closure.
2. **`CE(Gamma)` is a sub-semigroup**: if `tau, sigma in CE` with microstates
   `pi_n, rho_n`, then `pi_n ⊗ rho_n` is a finite-dimensional unitary
   representation and `tr(pi_n ⊗ rho_n) = tr(pi_n) · tr(rho_n)`, so
   `tau·sigma in CE`.  It contains `conj(tau)` (conjugate representation) and
   hence `|tau|^2`.
3. **`CE(Gamma)` is convex**: interleave block sizes `~ lambda D` and
   `~ (1-lambda) D` in a direct sum.
4. For `N` normal, `1_N in CE(Gamma)` **iff** `Gamma/N` is hyperlinear -- this
   is the definition of hyperlinearity read through
   `hyperlinear-quotient-permanence-equivalence`.

## The consequence that does the work

Because `CE` is closed under both products and limits, **no sequence of
products of a Connes-embeddable character can leave `CE`, in the limit or
anywhere along the way.**  Any mechanism that manufactures a bad idempotent
character by multiplying a bad character with itself must therefore start
from a `tau` with `|tau|^2` already outside `CE`, and must keep the whole
sequence `|tau|^{2k}` *uniformly* outside: membership can only be gained in
a pointwise limit, never lost, and a sequence of non-`CE` points may perfectly
well converge into the closed set `CE`.

That is the exact reason the amplification programs need a `k`-uniform
separation rather than "every stage is bad"; see
`character-diracization-limit` for the mechanism and
`diracization-gap-equals-nonhyperlinear-group` for what the uniform version
costs.

Convexity is recorded here because it is what lets Hahn--Banach produce a
*finitely supported* separating functional, i.e. a finite-word certificate,
in the companion claim.
