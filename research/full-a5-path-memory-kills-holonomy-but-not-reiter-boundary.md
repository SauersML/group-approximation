---
rg: 2
id: full-a5-path-memory-kills-holonomy-but-not-reiter-boundary
kind: claim
title: Full A5 path memory kills the interior unitary holonomy but leaves exactly a Reiter boundary
distinct_from:
  two-site-a5-center-has-exact-boundary-countermodel: that shows a fixed marked-pair measurement forgets a disjoint transported pair; this retains a separate copy and the full transported center PVM at every path label, so no interior label is forgotten.
  orbit-transport-gauge-needs-a-closed-label-set: that treats near-orbits of abstract shadow matchings; this gives the source-specific Hilbert-space construction for the A5 center packet and proves that arbitrary path multiplicities still have precisely the actor Reiter boundary.
  finite-cylinder-mixed-traces-kill-normalizer-holonomy: that starts with a closed exact finite transformation-group table; this constructs the maximal partial table available from finite path memory and identifies why it is not near-total for the pinned actor.
---

**ESTABLISHED POSITIVE INTERIOR LEMMA AND BOUNDARY FENCE.**  Let `G` be the
pinned Kun--Thom actor, let `S` be a fixed finite symmetric generating set,
and let `U_g` be an exact unitary representation.  Fix the marked two-site
`A5` center PVM `(P_omega)_(omega in {0,1}^2)`.  For a finite path-label set
`A subset G`, put on the copy labelled by `a`

```text
P^a_omega=U_a P_omega U_a^*.                            (APM1)
```

Choose an orthonormal basis adapted to `(P_omega)` and transport it by
`U_a` to the `a`-copy.  Whenever `a,sa in A`, the arrow

```text
T_s:copy(a) -> copy(sa),       T_s=U_s,                 (APM2)
```

is a literal basis permutation and carries `P^a_omega` to
`P^(sa)_omega`.  On every path whose intermediate labels stay in `A`, the
actor products and all transported A5 center labels therefore compose
exactly.  Thus full path memory really does remove every interior
right-regular/external-multiplicity holonomy; no mixed-trace or property-`(T)`
argument is needed there.

The same statement is dimension-free for approximate matrices.  If
`U_sU_a=U_(sa)+O_2(delta)` on the fixed word window, the transported-basis
arrow in `(APM2)` is `O_2(delta)` from the corresponding block permutation.
The constant is only the fixed telescoping length of the chosen words and is
independent of matrix dimension.

What remains is exactly the path boundary.  Give label `a` multiplicity
`m_a`, put `M=sum_a m_a`, and extend

```text
mu(a)=m_a/M
```

by zero outside `A`.  The largest source/target matching on which `(APM2)`
can be used has normalized mass

```text
sum_a min(mu(a),mu(sa))
 =1-(1/2)||s mu-mu||_1.                                 (APM3)
```

Attaching the entire four-atom marked-pair PVM, or the full `A5` center
spectrum, tensors every label copy by the same finite probability packet and
does not change `(APM3)`.  Cylinder-resolved mixed traces classicalize the
matched stabilizer fibers after closure, but they create none of the missing
source or target copies.

Consequently a sequence of finite path-memory carriers on which every
generator arrow is near-total would give finitely supported probability
measures `mu_n` with

```text
||s mu_n-mu_n||_1 -> 0       for every s in S.           (APM4)
```

This is Reiter's criterion for amenability.  The pinned actor is infinite and
has property `(T)`, hence is nonamenable.  Therefore there are a fixed finite
`S` and `eta>0` such that every finite weighted path carrier has

```text
max_(s in S) (1/2)||s mu-mu||_1 >= eta.                 (APM5)
```

Full path memory thus proves a useful positive finite-window rounding lemma,
but it cannot by itself produce the near-total permutation actor table needed
by `two-site-a5-center-classicalization`.  A successful construction must use
a genuinely non-path finite chart carrier whose boundary is closed by the
matrix model itself.  Constructing precisely that carrier is the surviving
sofic-action/classicalization gate; enlarging a word-prefix tree is not it.

DERIVATION
full-a5-path-memory-reiter-boundary-proof

