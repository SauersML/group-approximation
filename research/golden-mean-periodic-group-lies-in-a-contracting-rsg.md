---
rg: 2
id: golden-mean-periodic-group-lies-in-a-contracting-rsg
kind: claim
title: Nekrashevych's golden-mean periodic group lies in a full contracting rational similarity group, so a finitely presented simple group contains an infinite finitely generated simple periodic group, which is not residually finite
distinct_from:
  contracting-rsg-torsion-subgroups-are-residually-finite: that asserts every finitely generated torsion subgroup of a contracting RSG is residually finite; this exhibits a contracting RSG containing the non-residually-finite periodic group [F,F], so it proves the negation of that claim's main clause (its bounded-exponent corollary is untouched).
  fp-simple-groups-have-residually-finite-torsion: that is the uniform separator (RT) for all finitely presented simple groups; this gives an explicit finitely presented simple group violating (RT), so it proves the negation of (RT).
  brin-thompson-groups-contain-infinite-periodic-groups: that asks for a periodic group inside the specific hosts nV; the host here is a twisted Brin–Thompson group SV_G over a full contracting RSG, not nV.
  fp-simple-groups-can-contain-infinite-finite-exponent-groups: that asks for BOUNDED exponent; the exponent of the golden-mean group is not determined here.
  some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup: that is the bounded-exponent separator P_n; this settles only the unbounded (RT) form and does not decide P_n for any n.
artifacts:
  - experiments/golden-mean-rsg-2026-09-17/check_golden_mean_rsg.py
---

**ESTABLISHED (unreviewed).** Let `F = <a_i, b_i, c_i, d_i : i = 0,1,2>` be Nekrashevych's golden-mean fragmentation
group acting on `X^ω`, `X = {1,2}` (arXiv:1601.01033, §7, TeX l.1405–1433). Then:

1. Every element of `H = <V_2, F>` is a rational homeomorphism, and the nucleus of `H` lies in the 7-element set
   `N_0 = {id, b_0, c_0, d_0, b_0|_1, c_0|_1, d_0|_1}`. So `H` is a contracting RSG over the full binary shift.
2. `F` lies in the full contracting RSG `G = {f ∈ R_2 : Nuc_f ⊆ Nuc_H}`. Hence `F` embeds in a finitely presented
   simple group `Q` (BBMZ's twisted Brin–Thompson host `SV_G`).
3. `[F,F]` is an infinite, finitely generated, simple, periodic group that is not residually finite. It lies in the
   contracting RSG `G` and in the finitely presented simple group `Q`.

## Consequences

- **(RT) is false.** `fp-simple-groups-have-residually-finite-torsion` fails for `Q`. That node records: "an infinite
  non-residually-finite torsion subgroup in any finitely presented simple group would be the first evidence that
  Boone–Higman survives its Burnside test". This is such a subgroup.
- **The contracting-RSG torsion claim is false.** `contracting-rsg-torsion-subgroups-are-residually-finite` fails
  for `G`. Its Obstacle A (asynchronous local actions) is realized: the generators `b_i, c_i, d_i` are asynchronous.
- **Not settled:**
  - the bounded-exponent separator `some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup`, because the
    exponent of `F` is not determined here.
  - Whether `B(2,n)` embeds anywhere.

The Burnside test of Boone–Higman now runs only through bounded exponent. Periodicity plus non-residual-finiteness
are no longer an obstruction for finitely presented simple groups.

Proof route: `golden-mean-periodic-group-lies-in-a-contracting-rsg-proof`.

Novelty: checked only by greps of the graph, which found no node placing Nekrashevych's periodic groups in an RSG.
One web search found nothing. The literature was not checked further.
