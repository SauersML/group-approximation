---
rg: 2
id: fake-surface-stable-ac-certificates-proof
kind: route
title: Certify every acyclic cellular fake surface of complexity at most 5 by a replayed stable Andrews–Curtis trivialization or an A₅ image
target: fake-surfaces-up-to-complexity-five-are-stably-ac-trivial
requires:
  - fake-surface-census-misses-acyclic-classes
artifacts:
  - research/artifacts/hl-andrews-curtis-fake-surfaces-2026-09-14.md
---

**Classes.** By `fake-surface-census-misses-acyclic-classes`, the file
`classes-t<t>.txt` produced by `fsenum.cpp` lists one representative of each
acyclic class, as (graph index, base-6 code of the edge matchings).

**Certificate language.** A certificate is a list of macros on the relators r_0, …,
r_n of P(F, T). Each macro is a composite of the moves (AC1)–(AC5) of
`stable-andrews-curtis-conjecture`:
- `conj i u`: r_i ← u r_i u⁻¹, by (AC3) letter by letter;
- `inv i`: r_i ← r_i⁻¹, by (AC2);
- `mulc j i u s` (j ≠ i, s = ±1): r_j ← r_j · u r_i^s u⁻¹. Conjugate r_i by u, invert
  it if s = −1, apply (AC1), then undo both on r_i; r_i ends unchanged;
- `destab g`: some r_k equals the single letter g, and g occurs in no other relator.
  Delete r_k and g, by (AC5).

A certificate is valid when replay, with free reduction after every step, ends with
no relators and no generators. Then P(F, T) is stably AC-trivial.

**Search (untrusted).** `fsac.py` produces the certificates:
- first by eliminating a generator occurring exactly once in some relator,
  recursively, then cleaning and destabilizing;
- then over all spanning trees;
- then by backtracking, with a bounded breadth-first product search whenever no
  generator occurs exactly once.

Nothing in the search is trusted.

**Check (trusted).** `acverify.py` shares no code with `fsac.py`. For each record
it:
1. rebuilds the disk words from (graph, code) by its own corner walk;
2. collapses the recorded tree and requires the relators to match the record exactly;
3. requires determinant ±1;
4. replays the certificate.

For case (b) it checks that the recorded images in A₅ are even permutations, satisfy
every relator, and are not all trivial. A nontrivial homomorphism shows π₁ ≠ 1.

**Coverage.** `coverage.py` joins the class files with every record and re-runs
`acverify.check` on each. Every class has a passing record:
- t = 1, 2, 3: all 2, 17 and 239 classes by first-pass certificates;
- t = 4: 4664 first-pass, 12 through another spanning tree;
- t = 5: 111,067 first-pass, 389 through another tree, 1 by backtracking, 2 by the
  product search, and 1 A₅ image.

MSI jobs: 780529 (certify), 781551 (rescue), 784298 (standalone verification), and
the coverage job recorded in the artifact.

**Trust surface.** The model of `fake-surface-census-recount-proof`; `acverify.py`;
and that the macros above are composites of (AC1)–(AC5), which is immediate from
their definitions.
