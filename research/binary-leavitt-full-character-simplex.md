---
rg: 2
id: binary-leavitt-full-character-simplex
kind: claim
title: Every character of the full binary Leavitt unit group is a trivial-regular mixture
distinct_from:
  degree-zero-leavitt-core-characters-are-dirac-haar-mixtures: That classifies restriction to the locally finite degree-zero core; this proves the same formula on every element of the full unit group.
  monomial-root-elements-are-conjugate-in-the-leavitt-group: That controls monomial roots and certain finite subgroups; this treats arbitrary units by proper-corner conjugacy and prefix localization.
  thompson-v-character-simplex: That classifies the Thompson subgroup; this classifies the entire Leavitt unit group without transferring a subgroup theorem by containment.
artifacts:
  - research/artifacts/leavitt-full-character-classification-2026-09-08.md
  - research/artifacts/leavitt-root-projections-and-elementary-character-proof-2026-09-08.md
---

**Established by a written proof; not newly Lean-verified.** For
`H=L_(F_2)(1,2)^x`, every normalized positive-definite class function is

```text
chi=a*1+(1-a)*delta_1,       0<=a<=1.
```

The parameter is the existing degree-zero core parameter. The proof
shows that the core's invariant projection is central for the full
group, and that a character regular on the core vanishes on every
nonidentity unit. No assumption of extremality or embeddability is used.

The independent root fixed-projection proof identifies the same parameter
as `a=chi(x_12(1))` and establishes the full formula without a
finite-core character-classification input.

For every subgroup `Lambda<=H`, a character of `Lambda` extends to a
character of `H` exactly when it is a mixture of the trivial and
canonical regular characters of `Lambda`. In particular no nonembeddable
character of a hyperlinear subgroup can extend to `H`.

Consequently `H` is hyperlinear if and only if every character of `H`
is Connes embeddable. The classification does not construct a bad
character and does not decide which alternative holds.
