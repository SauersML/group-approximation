---
rg: 2
id: two-generator-balanced-kervaire-census-proof
kind: route
title: Enumerate every short two-generator balanced presentation, sieve by abelianization, and certify each survivor trivial, finite, or with a finite quotient
target: two-generator-balanced-kervaire-failures-need-length-16
requires:
  - deficiency-zero-kervaire-failure-forbids-finite-quotients
  - kervaire-laudenbach-holds-for-hyperlinear
artifacts:
  - research/artifacts/balanced-kervaire-search-2026-09-13.md
---

**Reductions.** A presentation `<x, y | r_1, r_2>` presents the same group after
free and cyclic reduction of each relator, which never increases total length. It
presents an isomorphic group after rotating or inverting a relator, swapping the
two relators, or applying one of the eight signed permutations of `{x, y}`. So it
suffices to treat one representative per class of pairs of cyclically reduced
relators of total length at most 15. An empty relator gives `H_1(G) != 0`.

**Abelianization.** `H_1(G) = Z^2 / (rows of M)`, with `M` the `2 x 2` matrix of
exponent sums of `r_1, r_2`. It vanishes exactly when `det M = +-1`. If it does
not vanish, `G` has a nontrivial finite quotient, and item 3 of
`deficiency-zero-kervaire-failure-forbids-finite-quotients`
rules out every killing word.

**Census.** `census_balanced.py` lists one representative per class with
`det M = +-1` and total length at most 15: 24571 classes. The per-length counts are
in the artifact. An independent recount, `census_check.py`, enumerates every
ordered pair of cyclically reduced words and takes orbit minima under the move
group, with no representative choice up front. At total length at most 15 it finds
the same per-length counts and 24571 classes, and the census representatives lie
in distinct recount classes with none missing (MSI job 753123).

**Certificates.** Every class was run through GAP 4.13.1 (`bal.g`; MSI jobs 748253
and 750364) with a coset enumeration over the trivial subgroup, then low-index
subgroups up to index 8. No class was left undecided.
- **Trivial (24539 classes).** The enumeration closes with one coset. An
  independent HLT enumerator, `tc_verify.py`, returns order 1 on each of them; it
  re-checks its final table as a consistent transitive action on which both
  relators close. Joined by class id with GAP's output, it agrees on all 3480
  classes of length at most 13 (job 750365) and all 21091 classes of length 14
  and 15 (job 751691), with 0 disagreements.
- **Finite, order 120 (24 classes).** Both enumerators return order 120. Each class
  also has an exported permutation representation of degree 120, the regular
  action read off GAP's coset table.
- **Finite quotient (8 classes).** GAP finds a proper subgroup of index 7 or 8.
  Each class has an exported permutation representation on the cosets.
- **Certificate check.** The 32 permutation representations (24 of degree 120, 3 of
  degree 7, 5 of degree 8; exported by `certs.g`, MSI job 751692) were checked by
  `verify_certs.py`, which evaluates both relators letter by letter on every point
  and checks the image is nontrivial: 32 pass, 0 fail.

**Conclusion.** A trivial `G` is not a witness. Every other class has a nontrivial
finite quotient: the regular action for the order-120 groups, or the coset action
for the other eight. So by item 3 of
`deficiency-zero-kervaire-failure-forbids-finite-quotients`, no
word of exponent sum `+-1` kills it.

**Trust surface.**
- The census script's enumeration of classes, cross-checked as recorded above.
- The GAP and `tc_verify.py` coset enumerators on the trivial classes; they agree
  class by class.
- The permutation certificates are checked letter by letter by `verify_certs.py`,
  which uses no coset enumeration.

All scripts, outputs and md5 sums are in the artifact.
