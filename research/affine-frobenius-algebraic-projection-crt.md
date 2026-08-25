---
rg: 2
id: affine-frobenius-algebraic-projection-crt
kind: claim
title: Realize the Frobenius incidence prescriptions by one finite-support projection
distinct_from:
  shared-involution-right-ideal-interpolation-criterion: that gives the complete operator criterion and a von Neumann support projection; this asks for the load-bearing finite-support projection in the canonical group algebra with the required deficit ledger.
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that asks for exact common marginal observables in one common corner; this permits distinct noncommuting incidence masks and asks only for one projection solving their right-ideal prescriptions.
  bass-serre-algebraic-projections-are-stably-vertex-induced: that classifies projections over finite graphs of finite groups; this projection must be constructed after leaving that hyperlinear Bass--Serre class.
---

**OPEN.**  Correlate the fixed affine-Frobenius context packets and enlarge
their group so that, for every variable `x`, the incidence data

```text
q_i=q_(c_i,x),              e_i=(1-A_(c_i,x))/2        (AFPC1)
```

satisfy the compatibility equations `(SIC4)` and there is one finite-support
group-algebra projection

```text
p_x=p_x^*=p_x^2,
p_xq_i=e_iq_i                    for every i.           (AFPC2)
```

The masks must retain the strict weighted canonical deficit budget required
by `rowwise-hecke-crt-certificate-for-nonce-bcs`, without changing the fixed
context PVMs.  Then

```text
B_x=1-2p_x                                                (AFPC3)
```

is the required shared finite-support involution.

## Attempts

1. **Use the von Neumann support projection of `(SIC9)`.**  This always
   works once the Gram equations hold, but functional calculus generally
   leaves the algebraic group ring.  No finite-support Hecke coefficient is
   obtained without an algebraic spectral separator.
2. **Use a Julia or matrix dilation.**  Equation `(SIC10)` shows that this
   only replaces `p_x` by a stabilized algebraic projection with the same
   prescribed columns.  It does not remove the projection CRT.
3. **Ask only for compressed agreement.**  The Frobenius masks reduce their
   stored marginals, so `(SIC11)--(SIC12)` recover the full right-ideal
   equation.
4. **Keep the context packets freely placed.**  They violate `(SIC4)` and
   already pay the pairwise floor in
   `rowwise-shared-involution-forces-pairwise-marginal-closeness`.
5. **Solve `(AFPC2)` in a finite graph of finite packets.**  Such a group is
   hyperlinear and its algebraic projections are stably vertex-induced; the
   existing Bass--Serre firewalls rule out the strict non-CE budget.
6. **Force the defect row to be a scaled partial isometry.**  This is a
   genuine algebraic escape: `tight-defect-column-solves-algebraic-projection-crt`
   proves that the cubic identity `DD^*D=lambda D` makes
   `p=lambda^(-1)DD^*` the required finite-support projection.  The new
   frontier is `affine-frobenius-tight-defect-column-frame`: no packet is
   yet known which enforces that identity while retaining compatibility and
   the strict canonical deficit.
7. **Solve one noncommuting two-context cell first.**  This local problem is
   completely soluble and sharply calibrated by
   `projection-crt-deficit-forces-common-meet`.  Rank-one omissions from one
   common projection give noncommuting masks of deficit `1/d` and a
   finite-support reflection agreeing with both marginals.  Conversely every
   projection CRT solution forces the meet of all prescribed negative pieces
   to have trace at least `tau(p)-sum_i tau(1-q_i)`.  Hence a strict
   high-density certificate already contains a large literal common negative
   core, even without the tight-frame cubic.  The missing step is not a
   two-ideal algebraic formula; it is correlating all fixed nonaffine context
   PVMs around those variable-specific cores.  In a finite packet that global
   correlation would itself be the forbidden finite-dimensional BCS
   certificate.
8. **Scale the rational cells while retaining the BCS predicates.**  The
   exact dimension-independent obstruction is
   `bcs-gap-blocks-vanishing-crt-mask-budget`.  If the consistency-cell
   deficits tend to zero, the fixed BCS gap forces weighted forbidden mass at
   least `Delta-o(1)`.  Predicate masks which annihilate that mass have deficit
   at least the same amount, so the total mask budget is never `o(1)` and can
   never cross the strict `<Delta` threshold in finite dimensions.  This
   rules out a global finite-packet scaling of the sharp rank-one cell while
   leaving the intended infinite canonical group-algebra construction open.

The remaining viable construction must simultaneously correlate the fixed
marginals and create a non-vertex-induced algebraic projection, through a
non-Bass--Serre relation or an infinite nonamenable overlap algebra.
