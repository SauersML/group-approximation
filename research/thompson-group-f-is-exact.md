---
rg: 2
id: thompson-group-f-is-exact
kind: claim
title: Thompson's group F is exact (equivalently T is exact, by Scarparo)
distinct_from:
  amenable-groupoid-full-groups-are-exact: that is exactness of all full groups of amenable ample groupoids, which implies this through V; this is the single group F.
  fp-simple-nonexact-group: that asks for a finitely presented simple non-exact group; the failure of this claim would give one, namely T.
---

**OPEN.** Thompson's group `F` has property A, i.e. `C*_r(F)` is exact.

- **Equivalent form.** Scarparo, *Relatively amenable actions of Thompson's groups*, arXiv:2109.01111 (Bull. Aust.
  Math. Soc.), read at source 2026-09-18. TeX l.283: "Thompson's group F is exact if and only if Thompson's
  group T is exact." The proof shows that `S^1` is a `(T, F)`-amenable `T`-space (l.143) and applies Brown–Ozawa
  Prop. 5.2.1 (l.164). The paper does not settle either side, and a bounded arXiv search (2026-09-18) found no
  later resolution.
- **If this fails**, `T` (finitely presented, infinite, simple) and `V ⊇ F` are non-exact. That proves
  `fp-simple-nonexact-group` and refutes `amenable-groupoid-full-groups-are-exact`. Coarse embeddability is not
  at stake either way: `F` is Haagerup (Farley).
- **If this holds**, it is a necessary first step toward "all finitely presented simple groups are exact". That
  statement would refute Boone–Higman by `exactness-separates-boone-higman-iff-fp-simple-groups-exact`. `T`,
  `V`, `nV`, the twisted Brin–Thompson groups, the Röver–Nekrashevych groups and Lodha's `S` all contain `F`.

## Lesson for general BH

Every exactness-based argument about Boone–Higman runs through Thompson's `F`:
- `F` exact is necessary for the falsity route "all finitely presented simple groups are exact".
- `F` non-exact would hand the proof side a finitely presented simple non-exact host, `T`, for free.

Its extra value on this graph is that it decides a whole column of the host census at once: every host that
contains `F`.
