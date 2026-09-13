---
rg: 2
id: explicit-eighteen-relator-nonsofic-group
kind: claim
title: Thompson's V with one adjoined involution and ten relations is a finitely presented simple nonsofic group with eighteen relators
distinct_from:
  explicit-sixty-relator-nonsofic-group: that is the same group through a seven-generator, sixty-relator Steinberg-Weyl presentation; this is a four-generator, eighteen-relator presentation over Thompson's V, of total length 322.
  fp-simple-nonsofic-group: that is existence of a finitely presented simple nonsofic group; this names a presentation with eighteen relators.
  finitely-presented-nonsofic-group-exists: that is the kernel-checked existence of a finitely presented nonsofic group through a finite-table cover whose relators are never written; this writes them, eighteen in all.
---

**ESTABLISHED (2026-09-12)** through `explicit-eighteen-relator-nonsofic-group-proof`. The presentation
was reviewed on 2026-09-12 by `ex-verify-presentation`: completeness PASS, under the conditions stated on
`thompson-steinberg-presentation-of-leavitt-unit-group`, including Bleak--Quick's normal-closure statement for
(2.4) (`research/artifacts/ex-review-presentations-2026-09-12-part2.md`).

The group

```text
< a, b, c, x | eight Bleak--Quick relators for V,  x^2,  (ax)^3,
               three commutators of x with the copy of V on the cone 1,
               three commutators of x with V-conjugates of x,
               one Steinberg commutator law,  one splitting law >
```

of `thompson-steinberg-presentation-of-leavitt-unit-group` is finitely presented, simple and not
sofic. The eighteen relators have total length 322, of which the eight for `V` account for 136.

Put differently: adjoining to Thompson's group `V` (sofic status open, finitely presented,
simple) a single involution and ten relations of length at most 32 produces a nonsofic group.
`x` interacts with `V` only through three commutations with V-conjugates, one commutator
identity, one splitting identity, the order-three law `(ax)^3 = 1`, and commutation with a copy
of `V`.
