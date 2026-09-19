---
rg: 2
id: bmw-census-solver-free-parity-kernel-certificates
kind: claim
title: Every BMW census class of degree (3,3), (4,3), (4,4) or (5,3) that is not certified reducible has an independently re-checked solver-free certificate that its parity kernel is not left-orderable
distinct_from:
  bmw-degree-44-53-parity-kernels-not-left-orderable: that proves the census theorem for (4,4) and (5,3) with two agreeing SAT solvers and excludes three classes; this covers every candidate of all four degrees, the three included, with explicit certificates and no solver
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that covers (3,3), (4,3) and torsion-free (4,4) with SAT; this re-derives those degrees without a solver as part of the whole census
  bmw-census-sat-free-klein-chain-certificates: that supplies 33 Klein chains checked by its own script; this re-checks them with a fresh script and combines them with all other certificate families
  bmw-census-klein-power-chain-certificates: that supplies the Klein-power chains; this re-checks them independently and proves coverage of the census
  bmw-census-survivor-cone-tree-certificates: that supplies 485 cone trees for part of the remaining classes; this re-checks them and closes coverage
  bmw-census-radius6-cone-lemma-certificates: that supplies the 509 cone-lemma certificates and their coverage of its own remaining list; this re-checks them with a separate reader and checks coverage against the census itself, including the classes settled before
artifacts:
  - experiments/bmw-census-solver-free-recheck-2026-09-18/README.md
  - experiments/bmw-census-solver-free-recheck-2026-09-18/recheck.py
  - experiments/bmw-census-solver-free-recheck-2026-09-18/recheck.log
  - experiments/bmw-census-solver-free-recheck-2026-09-18/mutate.py
  - experiments/bmw-census-solver-free-recheck-2026-09-18/mutate.log
  - research/bmw-census-solver-free-parity-kernel-certificates-proof.md
---

**ESTABLISHED (computer-checked, no SAT solver).** Proof:
`bmw-census-solver-free-parity-kernel-certificates-proof`.

**Setting.** Take the 20 census patterns `mpA_npB` of degrees (3,3), (4,3), (4,4) and (5,3), namely
30_30, 31_30, 31_31, 40_30, 41_30, 41_31, 42_30, 42_31, 40_40, 41_40, 41_41, 42_40, 42_41, 42_42,
50_30, 50_31, 51_30, 51_31, 52_30 and 52_31. The classes are those of
`experiments/bmw-census-left-orders-2026-09-17/census_<pat>.json`. For a class, `Γ` is the BMW
group of its squares and `Γ^+` is its parity kernel (both lengths even).

A class is *certified reducible* if the images of `⟨A⟩` in `Aut(T_V)` and of `⟨B⟩` in `Aut(T_H)`
are both finite. This is decided at cap 4000, and at cap 60000 for the one class `51_30#506`.

**Theorem.** For every class of these patterns that is not certified reducible, `Γ^+` is not
left-orderable. The proof is an explicit certificate of one of these kinds:
- a cycle of Klein relations `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}` and power steps;
- a cone-propagation tree;
- a list of cone lemmas.

**Result** (`recheck.log`):
- **Certificates:** 1206 certificates on 1203 classes checked, 0 rejected. Three classes have two
  certificates: `40_40` #193, #281 and #332.
- **Census:** 6964 classes. At cap 4000, 5763 are certified reducible. `51_30#506` is also certified
  reducible at cap 60000, with image orders 6 and 6912, as in `bigcap.log`.
- **Candidates:** 1200, and all 1200 have a checked certificate. The other 3 certified classes are
  reducible Promislow-type classes (`41_40` #1174, `41_41` #486 and #541).

| degree | patterns | classes | certified reducible | candidates | covered |
|---|---|---|---|---|---|
| (3,3) | 30_30, 31_30, 31_31 | 60 | 56 | 4 | 4 |
| (4,3) | 40_30, 41_30, 41_31, 42_30, 42_31 | 639 | 589 | 50 | 50 |
| (4,4) | 40_40, 41_40, 41_41, 42_40, 42_41, 42_42 | 3822 | 3133 | 689 | 689 |
| (5,3) | 50_30, 50_31, 51_30, 51_31, 52_30, 52_31 | 2443 | 1986 | 457 | 457 |
| total | 20 | 6964 | 5764 | 1200 | 1200 |

The candidate counts agree with the census claims:
- 62 for (3,3), (4,3) and `42_42` (`small-degree-irreducible-bmw-parity-kernels-not-left-orderable`);
- 301 for `40_40`, which includes #193, #281 and #332;
- 190 for `50_30`.

The certificates come from these families:

| family | classes |
|---|---|
| Klein chains (w6c) | 33 |
| Klein-power chains (w7) | 171 |
| frame chains (w8) | 3 |
| quaternionic cone trees (w9) | 2 |
| cone trees (w10) | 485 |
| cone lemmas (w11) | 509 |

**Corollary.** In degrees (3,3), (4,3), (4,4) and (5,3), every irreducible BMW lattice has a
non-left-orderable parity kernel, with no exception. The three former exceptions `40_40#193`, `#281`
and `#332` are covered. Reducibility is certified by §5 of
`small-degree-bmw-parity-kernels-not-left-orderable-proof`, and census completeness by §1 and §6
there. No SAT solver is used.

**Independence.** The certificates come from six lanes. `recheck.py` is a new reader with its own
rewriting, normal forms, certificate semantics and automaton minimisation, and it shares no code with
their checkers. `mutate.py` confirms that it rejects 18 kinds of corrupted certificate.
