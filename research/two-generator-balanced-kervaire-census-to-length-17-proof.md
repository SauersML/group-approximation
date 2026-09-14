---
rg: 2
id: two-generator-balanced-kervaire-census-to-length-17-proof
kind: route
title: Extend the certified two-generator balanced census to total length 17, recount it by orbit counting, and certify each new class trivial or with a verified finite quotient
target: two-generator-balanced-kervaire-failures-need-length-18
requires:
  - two-generator-balanced-kervaire-failures-need-length-16
  - deficiency-zero-kervaire-failure-forbids-finite-quotients
  - kervaire-laudenbach-holds-for-hyperlinear
artifacts:
  - research/artifacts/balanced-kervaire-census-16-2026-09-14.md
---

**Total length at most 15.** This is `two-generator-balanced-kervaire-failures-need-length-16`.

**Reductions and abelianization.** As in `two-generator-balanced-kervaire-census-proof`:
- free and cyclic reduction never increase total length;
- rotation and inversion of a relator, swapping the relators and the eight signed generator
  permutations give isomorphic groups;
- `H_1(G) = 0` exactly when the exponent-sum matrix has `det = +-1`, and otherwise `G` has a
  nontrivial finite quotient.

**Census.** `census_balanced.py 17`, unchanged from the length-15 run, lists 181842 classes with
`det = +-1`. Its first 24571 rows are byte-identical to the certified length-15 census (equal md5).

**Recount.** `rc_orbit.py` works block by block, for relator lengths `l1 <= l2`.
- It counts the ordered pairs of cyclically reduced words with `|det| = 1` exactly, by a
  transfer-matrix count of words by first letter, last letter and exponent sums.
- For each census representative it applies all `64 l1 l2` elements of the move group, which gives
  the stabilizer order and the orbit minimum.

On every block of total length at most 17 (MSI job 778223):
- each representative is its own orbit minimum and none repeats, so representatives lie in distinct
  orbits;
- the orbit sizes sum to the number of ordered pairs, so no orbit is missed.

So the census has exactly one representative per class. Calibration: the same script reproduces
the certified length-15 census, and fails on three corrupted controls.

**Classification of total lengths 16 and 17 (157271 classes).**
- **GAP 4.13.1**, `bal.g` unchanged, 200000 cosets, then low-index subgroups up to index 8: 157076
  trivial, 174 finite, 20 with a proper subgroup of index 7 or 8, and one undecided class, 137426
  `<x, y | XXYXYxxy, XYYYYXyXy>`. A follow-up on that class with 20000000 cosets closes the table:
  finite of order 5322240.
- **Independent HLT enumerator**, `tc_verify.py` unchanged, limit 200000: a closed table of the same
  order on each of the 157250 classes GAP closed, and overflow on the other 21.
- **Join by class id** (`join16.py`, calibrated on the length 14 and 15 outputs): all 157271 ids,
  157250 agree closed, 21 agree not closed, 0 contradictions, 0 budget differences.
- **Certificates.** `certs.g` exports a permutation representation for each nontrivial class: the
  regular action for the finite ones, the coset action for the low-index ones. `verify_certs.py`
  evaluates both relators letter by letter at every point and checks that the image is nontrivial.
  - 194 certificates for the first-pass finite and low-index classes: 194 pass, 0 fail.
  - The degree-5322240 regular action for class 137426: passes.

**Conclusion.** A trivial `G` is not a witness. Every other class of total length 16 or 17 has a
verified nontrivial permutation representation, hence a nontrivial finite quotient. So by item 3 of
`deficiency-zero-kervaire-failure-forbids-finite-quotients`, no word of exponent sum `+-1` kills it.

**Trust surface.**
- The census script, cross-checked by the orbit-counting recount.
- The two coset enumerators on the 157076 trivial classes, which agree class by class.
- The permutation certificates on the other 195 classes, checked letter by letter without coset
  enumeration. For class 137426 only GAP closed the table, so this certificate is the independent
  check there.

All scripts, logs and md5 sums are in the artifact.
