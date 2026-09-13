---
rg: 2
id: there-is-torsion-free-f-infinity-amenable-non-ea-group
kind: claim
title: Some torsion-free amenable group of type F_infinity is not elementary amenable
distinct_from:
  there-is-f-infinity-amenable-non-elementary-amenable-group: that is the answer to Zaremsky 1.12 with torsion allowed (Grigorchuk-type candidates have unbounded torsion); this is the torsion-free case, which also feeds Zaremsky 2.8 and Kropholler's finite-cd question.
---

**OPEN.** There is a torsion-free group of type `F_∞` that is amenable and not
elementary amenable.

**Why the torsion-free case gets its own node.** For torsion-free groups of type
`FP_∞`, membership in Kropholler's class `LH𝔉` is equivalent to finite
cohomological dimension. Finite cd gives a finite-dimensional free contractible
complex, hence `H_1𝔉`. The converse is Kropholler's theorem, cited as the key
finiteness theorem for `H𝔉`-groups of type `FP_∞` by Januszkiewicz–
Kropholler–Leary, arXiv:0908.3669v1, p. 1. So a torsion-free answer `G` falls in
one of two cases.

- `cd G < ∞`. Then `G` is an amenable group of finite cd that is not virtually
  solvable, a negative answer to Kropholler's question
  (`amenable-groups-of-finite-cd-are-virtually-solvable`).
- `cd G = ∞`. If Thompson's `F` is not amenable, then `G` contains no copy of
  `F`, since subgroups of amenable groups are amenable. So `G` answers Zaremsky
  2.8 (`omits-f-from-torsion-free-amenable-non-ea-f-infinity`).

## Attempts

- **Basilica-type candidates (open).** The Basilica group is torsion-free,
  weakly branch and amenable (Bartholdi–Virág). Its finite endomorphic
  presentation (Grigorchuk–Żuk) gives a finitely presented HNN extension; the
  statements are to be verified before import. A weakly branch base contains
  `Z^(2^n)` for every `n`, so any type-`FP_∞` extension has infinite cd and
  falls in the second case above. The finiteness beyond `FP_2` is untested, and
  the Alexander-module test of `grigorchuk-hnn-extension-is-fp-infinity`
  applies verbatim.
- **Thompson's `F` (conditional).** `F` is torsion-free and of type `F_∞`, so
  `thompson-f-is-amenable` would give this claim, since `F` is not elementary
  amenable. That fact still needs a verified import node.
