---
rg: 2
id: algebraic-atiyah-with-determinant-closed-under-colimits
kind: claim
title: Strong Atiyah over algebraic numbers with the determinant conjecture passes to subgroups and directed colimits
distinct_from:
  luck-determinant-fixed-two-generator-tester: that isolates the determinant conjecture alone at one group through its published colimit permanence; this proves colimit permanence for its conjunction with Strong Atiyah, which has no known unconditional colimit permanence.
  elementary-amenable-torsion-free-strong-atiyah: that certifies Strong Atiyah for one class of groups; this is a permanence theorem and certifies no group on its own.
---

Let `Qbar` be the field of algebraic numbers in `C`.  For a torsion-free
group `G` write `SA(G)` for the Strong Atiyah Conjecture over `Qbar`,

```text
dim_(N(G)) ker(r_A) in Z          for every A in M_(m,n)(Qbar[G]),
```

where `r_A: l2(G)^m -> l2(G)^n` is right multiplication, and `Det(G)` for
Lueck's determinant conjecture, `det_(N(G))(r_M) >= 1` for every
`M in M_(r,s)(Z[G])`.  Let `A` be the class of torsion-free groups `G` with
both `SA(G)` and `Det(G)`.

**Theorem.**  The class `A` is closed under subgroups and under directed
colimits `G = colim_i G_i`, with structure maps not required to be
injective.

## Why the determinant clause is there

Along a directed colimit the spectral measures of a fixed matrix converge
weakly, and weak convergence alone gives only

```text
dim ker r_A  >=  limsup_j dim ker r_(A_j).
```

Kernel mass of the stages can sit at small positive spectrum and reappear in
the limit as a fractional atom at zero.  The determinant conjecture for the
stages bounds the spectral mass in `(0, lambda^2]` by
`md log(kappa) / |log(c lambda)|`, where `m`, `d`, `kappa` and `c` depend only
on the matrix, and that uniform bound turns the inequality into an equality.
Strong Atiyah on its own has no known permanence of this kind, as
`luck-determinant-fixed-two-generator-tester` records; this theorem shows the
determinant conjecture is enough to supply it.

The mechanism is the classical Lueck--Schick approximation argument; Lueck,
arXiv:2102.04549v2, Theorem 3.14, is its instance for chains of quotients.
The route proves the directed-colimit form, and handles algebraic
coefficients by restriction of scalars.

**ESTABLISHED 2026-09-11** by [[algebraic-atiyah-determinant-colimit-proof]].
