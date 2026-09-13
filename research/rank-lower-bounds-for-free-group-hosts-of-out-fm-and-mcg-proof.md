---
rg: 2
id: rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg-proof
kind: route
title: Compare virtual cohomological dimensions of guest and host
target: rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg
requires: []
---

**Inputs (standard; theorem numbers not re-read).**
- Culler--Vogtmann, *Moduli of graphs and automorphisms of free groups*, Invent.
  Math. 84 (1986): `vcd Out(F_n) = 2n − 3` for `n ≥ 2`.
- Harer, *The virtual cohomological dimension of the mapping class group of an
  orientable surface*, Invent. Math. 84 (1986): the mapping class group of the
  closed surface of genus `g ≥ 2` has `vcd = 4g − 5`.

**Host bound for Aut.** Let `Γ ≤ Out(F_n)`, `n ≥ 2`, be torsion-free of finite
index with `cd Γ = 2n − 3`. Its preimage in `Aut(F_n)` has finite index and is an
extension of `Γ` by `Inn(F_n) ≅ F_n`. It is torsion-free (a torsion element maps to
the torsion-free `Γ` trivially and so lies in `F_n`), and
`cd ≤ cd F_n + cd Γ = 2n − 2`. So `vcd Aut(F_n) ≤ 2n − 2`.

**Monotonicity.** If `L ≤ G` and `Γ ≤ G` is torsion-free of finite index, then
`L ∩ Γ` is torsion-free of finite index in `L` and `cd(L ∩ Γ) ≤ cd Γ`. By Serre's
theorem vcd does not depend on the torsion-free finite-index subgroup chosen, so
`vcd L ≤ vcd G`.

**Hosts of rank at most one.** `Aut(F_0)`, `Out(F_0)`, `Aut(F_1)` and `Out(F_1)`
are finite, while `Out(F_m)`, `m ≥ 2`, and closed-surface mapping class groups of
genus `≥ 2` are infinite. So `n ≥ 2` in both items.

**Item 1.** `2m − 3 ≤ 2n − 3` for an `Out(F_n)` host, and `2m − 3 ≤ 2n − 2` for an
`Aut(F_n)` host, so `2n ≥ 2m − 1` and, `n` being an integer, `n ≥ m`.

**Item 2.** `4g − 5 ≤ 2n − 3` for an `Out(F_n)` host, and `4g − 5 ≤ 2n − 2` for an
`Aut(F_n)` host, so `2n ≥ 4g − 3` and `n ≥ 2g − 1`.
