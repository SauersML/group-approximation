---
rg: 2
id: matrix-corona-k1-vanishes
kind: claim
title: Every norm matrix corona has vanishing K-one
---

For any sequence `(d_n)` of positive integers,
`K_1(prod_n M_{d_n} / oplus_n M_{d_n}) = 0`.

Consequence for the non-MF program: no winding-number or Bott-type index of
the marked unitary alone can obstruct a corona representation.  A central
mark of infinite order, forced near the scalars, carries no `K_1` class to
be contradicted, so the "unwind the sign into a circle and count turns"
route into `torsion-free-finitely-presented-non-mf` is void.  Any surviving
index argument must be relative — an invariant of the mark **together with**
another almost-commuting operator, as in the Bott index of an almost
commuting pair — and not of the mark by itself.

## Priority check (2026-08-14 literature scout)

**No prior source located, and none is needed.** A targeted sweep — arXiv
full-text for corona algebras with K-theory, and for MF/matricial-field and
quasidiagonality work 2008--2026 — turned up nothing computing `K_1` or
`K_0` of `prod_n M_(d_n) / oplus_n M_(d_n)`. The nearby literature is about
coronas of *stable* or non-simple C-star algebras (multiplier/corona real
rank, projection lifting), which is a different object.

Treat the statement as folklore and prove it in place; it is three lines from
the six-term exact sequence of

```text
0 -> oplus_n M_(d_n) -> prod_n M_(d_n) -> corona -> 0,
```

using `K_1(prod_n M_(d_n)) = 0` (each `U(d_n)` is connected, and `K_1` of a
product of unital algebras is the product of the `K_1`s) together with
injectivity of `K_0(oplus) = oplus Z -> K_0(prod) = prod Z`. No novelty
should be claimed for it.

For the relative invariant this node calls for, see
`exel-loring-relative-quasirep-invariant`: the Exel--Loring pairing of
quasi-representations against `H_2` of the group is the developed form of
"Bott index of an almost commuting pair" at group level.
