---
rg: 2
id: kms-hb2-groups-contain-genus-two-surface-subgroups
kind: claim
title: For every odd prime p, the hyperbolic KMS group G_HB2(p) contains a quasiconvex genus-two surface subgroup, so infinitely many hyperbolic Kazhdan groups do
distinct_from:
  ghb7-contains-a-genus-two-surface-subgroup: that is the single case p = 7, with labels in F_7 checked in SL_4(F_7); this covers every odd prime with one integer labelling checked in the integral vertex groups
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for every one-ended hyperbolic group; this answers it for the infinite family G_HB2(p), p >= 7, of hyperbolic Kazhdan groups
  flip-uniform-lattices-contain-surface-subgroups: that covers uniform lattices under the flip assumption; a uniform lattice with property (T) in a semisimple Lie group has virtual cohomological dimension at least 3, and these groups have at most 2
  closed-hyperbolic-3-manifold-groups-contain-surface-subgroups: that is the Kahn--Markovic case; closed 3-manifold groups have cohomological dimension 3, and these groups have virtual cohomological dimension at most 2
  cyclic-graphs-of-free-groups-contain-surface-subgroups: that covers groups splitting over virtually cyclic groups; for p >= 7 these groups have property (T)
artifacts:
  - experiments/kms-hb2-surface-subgroups/surface67-integer-labels.json
  - experiments/kms-hb2-surface-subgroups/verify_integer_certificate.py
  - experiments/kms-hb2-surface-subgroups/verify.log
  - research/artifacts/hl-surface-subgroups-2026-09-14.md
---

**ESTABLISHED (computer-certified).** For every odd prime `p`, the KMS group

```text
G_{HB_2^{(2)}}(p) = <a,b,c | a^p, b^p, c^p, [a,b,a], [a,b,b], [c,b,c], [c,b,b,c], [c,b,b,b], [c,a,c], [c,a,a,c], [c,a,a,a]>
```

contains a quasiconvex subgroup isomorphic to the fundamental group of the closed orientable surface
of genus 2. One 24-chamber labelled surface, with labels in `{−1, 1, 2}`, works for every odd prime.

Consequences:
- Every finite-index subgroup of `G_{HB_2^{(2)}}(p)` contains a closed surface group. It meets the
  genus-2 subgroup in a finite-index subgroup, which is a closed surface group of genus at least 2.
- For every prime `p ≥ 7`, `G_{HB_2^{(2)}}(p)` is an infinite hyperbolic group with property (T)
  (CCKW Corollary 7.8, item 5 of `cckw-kms-triangle-groups-structure`). So Gromov's surface subgroup
  question has a positive answer for infinitely many pairwise non-isomorphic hyperbolic Kazhdan groups
  (non-isomorphic for distinct `p` by CCKW Proposition 7.6).

Proof: `kms-hb2-groups-contain-genus-two-surface-subgroups-proof`.

## Why these groups are outside the classes covered on main

- *Virtual cohomological dimension at most 2.* `ψ : G → SL_4(F_p)` is injective on the three vertex
  groups (Step 0(d) of `kms-hb2-girth-surfaces-give-surface-subgroups-proof`). By Theorem 3.1(iv), `G` is
  virtually torsion-free. A torsion-free finite-index subgroup acts freely on the contractible
  2-complex `Y`, so it has cohomological dimension at most 2. This excludes closed 3-manifold groups
  and uniform lattices with property (T). The standard facts in this paragraph were not source-checked
  here.
- *No splitting for `p ≥ 7`.* Infinite groups with property (T) have Serre's property (FA), so they do
  not split over any subgroup and are one-ended. Standard, not source-checked here.
- *No involutions.* Every finite subgroup is conjugate into a vertex group (Theorem 3.1(ii)), a `p`-group
  with `p` odd. So these are not Coxeter groups.

## Literature boundary

- Web searches (2026-09-14) on surface subgroups of hyperbolic groups with property (T), of
  Kac–Moody–Steinberg groups, and of lattices in hyperbolic buildings found the following, none on KMS
  groups:
  - Kangaslampi–Vdovina, arXiv:1409.1401: no genus-2 periodic planes in most of 23 triangular-building
    lattices;
  - Kangaslampi, arXiv:1410.4655;
  - Constantine–Lafont–Oppenheim, arXiv:1407.3958, *Surface subgroups for lattices in Fuchsian
    buildings*. Its arXiv page says it was withdrawn for an error in the proof of Fact 3.
- The CCKW text extraction contains no occurrence of "surface".
- So "new" means not found in these sources.
