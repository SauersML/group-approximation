---
rg: 2
id: lamplighter-fp-amenable-interface-is-directional
kind: claim
title: The lamplighter seed embeds in a finitely presented amenable group but has no finitely presented amenable cover
distinct_from:
  shift-raag-family-classifies-amenability: that identifies the total branch with the lamplighter group; this determines exactly which direction a finite-presentation interface to that branch may take.
  amenability-of-finite-presentations-is-pi2-complete: that asks for a uniform totality switch; this proves a sharp obstruction and a sharp positive ambient for its total seed, but not the uniform switch.
---

**ESTABLISHED.**  Put `L=Z wr Z`.  This is the group `G_J` of
[[shift-raag-family-classifies-amenability]] when
`J=Z_(>0)`.  The finite-presentation interface to `L` is asymmetric.

**Embedding direction exists.**  The Baumslag--Remeslennikov group

```text
H=<a,s,t | a^t=a a^s, [s,t]=1, [a,a^s]=1>             (LFI1)
```

is finitely presented and metabelian, and it contains `Z wr Z`.  Thus
`H` is amenable and the total recursive seed has an explicit finitely
presented amenable overgroup.

**Cover direction is impossible.**  `L` is finitely generated,
metabelian, and not finitely presented.  The Bieri--Strebel theorem implies
that every finitely presented group surjecting onto `L` contains a
nonabelian free subgroup.  Hence

```text
E finitely presented and E ->> L  implies  F_2 <= E,    (LFI2)
```

so `E` is nonamenable.  In particular no finitely presented amenable
overgroup of `L` can retain a retraction onto `L`.

For [[amenability-of-finite-presentations-is-pi2-complete]] this fixes the
compiler polarity.  A successful family cannot retain the total seed as a
quotient, cover, or retract.  It needs a uniform conditional
embedding-direction interface which is amenable on the total branch and
retains a free subgroup on every incomplete branch.  The existence of
`(LFI1)` shows that the total seed itself is not the obstruction.

**Source.**  M. G. Benli, R. Grigorchuk and P. de la Harpe, *Amenable
groups without finitely presented amenable covers*, Bull. Math. Sci. 3
(2013), 73--131, DOI `10.1007/s13373-013-0031-5`: Theorem 1.5 gives the
cover obstruction, and Remark A.4(c) records `(LFI1)`, its
metabelianity, and the embedded wreath product.

DERIVATION
[[lamplighter-fp-amenable-interface-directional-proof]]
