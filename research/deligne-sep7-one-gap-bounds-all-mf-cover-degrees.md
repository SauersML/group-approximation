---
rg: 2
id: deligne-sep7-one-gap-bounds-all-mf-cover-degrees
kind: claim
title: A single Maslov operator gap bounds every MF covering degree quantitatively
artifacts:
  - research/artifacts/deligne-sep7-all-cover-mf-classification.md
distinct_from:
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that is the unresolved exclusion at one-third; this proves what any certified finite-window exclusion at any parameter would imply for all cover degrees.
  deligne-sep7-all-cover-mf-radical-classification: that gives the exact structural formula with an unknown integer; this bounds that integer and every MF degree by the size of one finite-window gap certificate.
---

Fix the normalized integral covering cocycle `b`, a nonempty finite set
`W subset Gamma x Gamma`, and a parameter `theta_0 in R/Z`. Suppose that
for some `epsilon>0`, every positive-dimensional unitary tuple indexed by
all elements `g,h,gh` for `(g,h) in W` has

```text
max_((g,h) in W)
 ||U_g U_h-exp(2 pi i theta_0 b(g,h))U_(gh)||_op >= epsilon.
```

Set `B=max_((g,h) in W)|b(g,h)|`. Then `B>0`, the norm-parameter subgroup
is finite of even order `m`, and

```text
m <= pi B/epsilon,
E_q is MF  ==>  q <= pi B/epsilon.
```

Any parameter absent from the norm-parameter subgroup has such a finite
window and positive gap. Thus one absent parameter bounds all MF covering
degrees, including degrees coprime to its denominator. This theorem assumes
the displayed gap; it does not supply one at `theta_0=1/3`.
