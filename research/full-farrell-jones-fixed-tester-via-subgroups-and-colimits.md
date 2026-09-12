---
rg: 2
id: full-farrell-jones-fixed-tester-via-subgroups-and-colimits
kind: route
title: Combine the universal torsion-free host with Full Farrell--Jones inheritance
target: full-farrell-jones-fixed-fp-torsion-free-tester
requires: [whitehead-universal-finitely-presented-torsion-free-group, torsion-free-directed-colimit-recursively-presented]
---

Choose the finitely presented torsion-free group `U` from
[[whitehead-universal-finitely-presented-torsion-free-group]]. Its
Whitehead-injectivity is not used here; only that every countably generated
recursively presented torsion-free group embeds in `U`.

Suppose `U` satisfies Full Farrell--Jones and let `G` be torsion-free.
By [[torsion-free-directed-colimit-recursively-presented]], write

```text
G = colim_i K_i
```

with every `K_i` finitely generated, recursively presented, and
torsion-free. Each `K_i` embeds in `U`. Lueck, Theorem 8.12(ii)(a),
makes Full Farrell--Jones hereditary to subgroups, so every `K_i` belongs
to `FJ`. Theorem 8.12(ii)(f) closes `FJ` under directed colimits with
arbitrary structure maps. Hence `G` belongs to `FJ`.

Conversely, if every torsion-free group belongs to `FJ`, then `U` does
because `U` is torsion-free.

The coefficient-rich Full conjecture is essential: the proof uses subgroup
inheritance. No such claim is made for a bare fixed-ring, non-fibered
assembly statement.

Source: Wolfgang Lueck, *Survey on the Farrell--Jones Conjecture*, Bull.
Amer. Math. Soc. (N.S.) 63 (2026), 79--117,
DOI 10.1090/bull/1876; Definition 8.10, Definition 8.11, and
Theorem 8.12(ii)(a),(f). Remark 11.4 gives the analogous unrestricted
universal-finitely-presented-group argument. QED
