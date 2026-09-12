---
rg: 2
id: congruence-kazhdan-groups-satisfy-strong-atiyah
kind: claim
title: Infinite torsion-free property (T) groups satisfying Strong Atiyah exist, e.g. Gamma(3) and E_3(3) in SL_3(Z)
distinct_from:
  p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah: that is the imported p-adic analytic class; this records that the class contains infinite Kazhdan groups and corrects the graph's scope notes that said no such group was known.
  kazhdan-edge-coproduct-rank-is-inner-rank: that is an open maximality question for amalgams over a Kazhdan edge; this supplies known Kazhdan groups satisfying Strong Atiyah, so that question's hypotheses are satisfiable.
  e33-no-unique-product-pairs-of-small-radius: that is a field-independent SAT census of unique-product failures on E_3(3); this proves E_3(3) has no zero divisors in characteristic 0 or 3 at all, so it remains a zero-divisor host only in the other characteristics.
---

**ESTABLISHED** by [[congruence-kazhdan-strong-atiyah-proof]].

Let `Gamma(3) = ker(SL_3(Z) -> SL_3(Z/3))` and
`E_3(3) = <e_ij(3) : i != j> <= Gamma(3)`. Then:

1. `Gamma(3)` and every subgroup of it, in particular every finite-index
   subgroup and `E_3(3)`, is infinite, torsion-free and has property (T);
2. each satisfies the Strong Atiyah Conjecture over `C`;
3. for each, `k[H]` is a domain over every field `k` of characteristic `0` or `3`.

The same holds for `Gamma(p)` in `SL_d(Z)` with `d >= 3` and `p` odd, and for
`Gamma(4)`, with characteristic `p` in part 3.

**Corrections this forces.**
- The scope notes in `kazhdan-edge-coproduct-rank-is-inner-rank` and in
  `research/artifacts/atiyah-coproduct-inner-rank-2026-09-12.md` Section 3 said
  that no infinite torsion-free property (T) group is known to satisfy Strong
  Atiyah. That is false. Besides these congruence groups, Fisher--Ng already
  gave torsion-free finite-index subgroups of `Out(F_n)` for `n >= 4`
  (`raag-out-and-mapping-class-virtually-strong-atiyah`), which have property
  (T) by Kaluba--Kielak--Nowak and Nitsche as cited in arXiv:2606.19606
  Section 1. The positive classes those notes checked (locally indicable, RFRS)
  do exclude Kazhdan groups. The p-adic analytic class does not.
- `E_3(3)` is not a zero-divisor host in characteristic `0` or `3`, by part 3.
  The SAT census in `e33-no-unique-product-pairs-of-small-radius` is valid, since
  it is field-independent, but its host-status paragraph said the host "avoids
  every proved class". The Farkas--Linnell class is proved and contains it. The
  host survives only over fields of characteristic `l` not in `{0, 3}`.
  `E_3(3)` is not residually 2, since its abelianization is a finite 3-group, so
  no 2-adic congruence argument applies to it over `F_2`.
