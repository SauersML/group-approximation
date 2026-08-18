---
rg: 2
id: hyperlinear-implies-sofic-via-definetti-rounding
kind: route
title: Balanced replication, then dimension-free symmetric-extension rounding
target: hyperlinear-implies-sofic
requires:
  - definetti-group-table-rounding
  - balanced-replica-hs-amplification
---

Let `G` be hyperlinear, `F ⊂ G` a finite window and `eps > 0`; let `T` be the
multiplication table of `F`.  Take `m = m(T,eps)` and `eta = eta(T,eps,m)`
from `definetti-group-table-rounding`.

Hyperlinearity gives, for every `delta > 0`, a unitary microstate of `T` with
multiplicative defect `< delta` and regular-trace separation `< delta`, in
some dimension `d = d(delta)` over which we have no control.  Apply balanced
replication `U ↦ (U ⊗ conj(U))^{⊗m}`: by
`balanced-replica-hs-amplification` the replicated table has multiplicative
defect at most `sqrt(2m)·delta`, its separation statistic improves to
`|tau(U_w)|^{2m}`, and it is by construction `m`-symmetric-extendible and
balanced.  Choosing `delta < eta/sqrt(2m)` — legitimate, because `m` was fixed
before `delta` — puts the replicated table inside the hypothesis of the
rounding theorem, whose conclusion is a permutation model of `T` with Hamming
defect `< eps`.  As `F` and `eps` were arbitrary, `G` is sofic.

Two remarks on what this route does and does not assume.  The replication
step is where the dimension problem is disposed of: `m` never sees `d`, so no
error term of the form `d^C/m` can appear, which is the failure mode of every
naive quantum-to-classical conversion.  And the route is not a restatement of
its target: the premise is a single quantitative statement about one finite
table with an explicit rounding map, from which the group statement follows by
this argument but not conversely.
