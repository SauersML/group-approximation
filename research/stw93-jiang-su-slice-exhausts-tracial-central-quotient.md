---
rg: 2
id: stw93-jiang-su-slice-exhausts-tracial-central-quotient
kind: claim
title: The canonical Jiang--Su slice exhausts the XCIII tracial central quotient
distinct_from:
  stw93-super-mcduff-tracial-central-quotient: that theorem identifies D/I abstractly with the central sequence factor of L(F_2) tensor R; this theorem proves that every class in that quotient is represented by the canonical tensor-factor copy of F(Z).
  stw93-all-z-central-slices-generate-quasitrace-null-ideal: that theorem enlarges a quasitrace-null subideal of I by using all unital copies of F(Z); this theorem does not enlarge that ideal and instead gives an exact quotient isomorphism for the single canonical copy.
  stw93-tensor-factor-central-quasitrace-rigidity: that theorem controls restrictions of quasitraces to the canonical slice but makes no assertion that the slice surjects onto D/I.
artifacts:
  - research/artifacts/stw93-xciii-free-group-jiang-su-si-audit-2026-08-30.md
---

Put

```text
A=C*_r(F_2) tensor Z,       D=A_omega intersect A',
I=J_tau intersect D,        E=J_(tau_Z) intersect F(Z),
```

and let `iota:F(Z)->D` be the canonical tensor-factor embedding.  The
induced map

```text
iota-bar:F(Z)/E -> D/I
```

is an isomorphism.  Equivalently,

```text
D=I+iota(F(Z)),             I intersect iota(F(Z))=iota(E).   (Q)
```

Thus every tracial central-sequence class for `C*_r(F_2) tensor Z` already
has a representative from the single canonical Jiang--Su slice.  Any
negative XCIII witness is therefore an obstruction in the norm-level
extension by `I`, not a tracial-quotient direction missing from that slice.
