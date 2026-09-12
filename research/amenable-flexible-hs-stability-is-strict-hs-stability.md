---
rg: 2
id: amenable-flexible-hs-stability-is-strict-hs-stability
kind: claim
title: Flexible and strict HS-stability coincide for finitely generated groups with amenable maximal almost periodic quotient
distinct_from:
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that is the Becker--Lubotzky and Fournier-Facio--Gerasimova--Spaas exclusion of strict stability for infinite hyperlinear Kazhdan groups, where the two notions might differ; this proves they cannot differ on the opposite, amenable side.
  hyperlinear-flexibly-hs-stable-group-is-residually-finite: that shows flexible stability of a hyperlinear group forces residual finiteness; this shows that, once the maximal almost periodic quotient is amenable, flexible stability already forces strict stability.
  character-rigidity-equals-hyperfinite-hs-stability: that is the Dogon--Vigdorovich equivalence of hyperfinite HS-stability with character rigidity for higher rank lattices, a notion restricted to hyperfinite traces; this compares the flexible and same-dimensional notions over all asymptotic representations.
---

**ESTABLISHED.** Let `Γ` be a finitely generated group, and let `Rad_fd(Γ)` be
the intersection of the kernels of all finite-dimensional unitary
representations of `Γ`. If `Γ/Rad_fd(Γ)` is amenable (in particular, if `Γ` is
amenable), the following are equivalent:

```text
(a) Γ is flexibly HS-stable (Dogon arXiv:2211.10492v3, Definition 1.2:
    D_n >= d_n, lim D_n/d_n = 1, compressions P_n π_n(g) P_n);
(b) Γ is HS-stable (the same definition with D_n = d_n, Dogon's footnote 1).
```

**Consequence for the search for a separating group.** Dogon writes (p. 3):
"there is no known example of a group that is flexibly HS-stable, but not
HS-stable". A finitely generated example must have a non-amenable maximal
almost periodic quotient. If it is also hyperlinear, it is residually finite
by `hyperlinear-flexibly-hs-stable-group-is-residually-finite`, so
`Rad_fd(Γ) = 1` and the group itself is non-amenable. Dimension-parity
candidates among amenable groups cannot work: padding with trivial summands
absorbs any dimension mismatch, and injectivity of the limit trace removes the
remaining conjugacy obstruction.

For amenable `Γ`, (a) ⇒ (b) can also be read through Hadwin--Shulman
arXiv:1706.08405v3 Theorem 4. On an amenable group every character is
embeddable (their p. 9). Flexible stability makes each embeddable character a
pointwise limit of finite-dimensional traces (Steps 1--2 of the derivation).
That is their condition (3), which gives matricial stability.

DERIVATION
amenable-flexible-hs-stability-is-strict-hs-stability-proof
