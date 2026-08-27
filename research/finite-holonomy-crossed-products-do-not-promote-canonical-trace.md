---
rg: 2
id: finite-holonomy-crossed-products-do-not-promote-canonical-trace
kind: claim
title: Finite holonomy crossed products preserve CE and do not promote the payload to a canonical group trace
distinct_from:
  finite-index-extensions-preserve-connes-embeddability: that proves CE invariance for finite-index inclusions of finite factors using the basic construction; this treats arbitrary finite tracial algebras, including nonfactor BCS GNS algebras, and gives the explicit finite-holonomy regular representation.
  tensor-separated-holonomy-controller-is-circular: that shows an independent hyperlinear multiplicity group supplies matrix completions; this treats a genuinely payload-coupled finite action or cocycle crossed product and shows that its non-CE content is exactly the original payload.
  nonce-factor-in-group-factor-corner-forces-nonhyperlinear: that is the terminal group-factor corner criterion; this proves that realizing the finite-holonomy extension in such a corner already supplies the hypothesis of that criterion for the original payload.
  finite-rational-rank-flows-are-fd-dense: that separates rational rank flows from continuous cycle holonomy; this handles the first non-rank case when the holonomy is a finite action on the payload algebra.
---

**ESTABLISHED.**  Let `(M,tau)` be any finite tracial von Neumann algebra,
not necessarily a factor.  Let a finite group `K` act trace-preservingly on
`M`, allowing a finite unitary cocycle, and put

```text
N=M crossed_product_(alpha,omega) K.                              (FHC1)
```

With its canonical crossed-product trace,

```text
M is Connes embeddable  <=>  N is Connes embeddable.               (FHC2)
```

The reverse implication is restriction to the trace-preserving subalgebra
`M<=N`.  The forward implication follows from the regular covariant embedding

```text
N -> M tensor M_(|K|)(C),                                        (FHC3)
```

which is normal, faithful, and trace preserving.  Matrix amplification and
tracial von Neumann subalgebras preserve Connes embeddability.

Consequently a finite holonomy/two-cell algebra coupled to a non-CE BCS
completion remains non-CE, but this does not perform canonical trace
promotion.  If `(N,tau_N)` embeds trace-preservingly into a nonzero corner
`pL(Gamma)p`, then restricting that embedding to `M` already puts the original
non-CE payload in the same group-factor corner, and
`nonce-factor-in-group-factor-corner-forces-nonhyperlinear` applies directly.

Thus adjoining finite holonomy cannot be the missing groupifier by itself.
It can reorganize the payload or expose a useful finite word, but identifying
the resulting trace with a canonical group-factor corner is at least as hard
as doing so for the original BCS algebra.  If the holonomy algebra is merely
finite dimensional and independent of `M`, it is Connes embeddable and carries
no non-CE obstruction at all.

