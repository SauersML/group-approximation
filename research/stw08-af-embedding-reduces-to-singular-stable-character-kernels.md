---
rg: 2
id: stw08-af-embedding-reduces-to-singular-stable-character-kernels
kind: claim
title: Exact quasidiagonal AF-embeddability reduces to unique singular character algebras
distinct_from:
  stw07-bk-reduces-to-stable-character-kernels: that reduces stable finiteness versus quasidiagonality in the nuclear Blackadar--Kirchberg problem; this preserves quasidiagonality and detects failure of AF-embeddability in the exact problem.
  stw99-problem-ix2-exact-faithful-qd-trace-af-embeddable: the reduced algebra here has a unique quasidiagonal trace, but that trace is deliberately nonfaithful.
artifacts:
  - research/artifacts/stw08-singular-character-reduction-audit-2026-08-30.md
---

The following assertions are equivalent:

1. every separable exact quasidiagonal C-star algebra is AF-embeddable;
2. every nonzero separable unital exact quasidiagonal C-star algebra `E`
   having a character `chi:E->C` with stable essential kernel is
   AF-embeddable.

More precisely, if Problem VIII has a counterexample, then it has one `E`
with all of the following additional properties:

* `chi` is the unique tracial state of `E`; it is quasidiagonal and
  nonfaithful;
* `I=ker(chi)` has no nonzero bounded trace;
* `I` is not traceless: it admits a lower-semicontinuous tracial weight
  taking a finite nonzero value, and every such nonzero weight is unbounded.

One may take, from any counterexample `A`,

```text
I=A tensor K,             E=I~.
```

Thus a negative answer needs neither a complicated quotient nor several
bounded traces.  Its entire traceful obstruction may be confined to
unbounded weights on one stable essential ideal underneath a scalar split
quotient.
