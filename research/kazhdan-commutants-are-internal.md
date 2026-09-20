---
rg: 2
id: kazhdan-commutants-are-internal
kind: claim
title: "Every finitely generated Kazhdan group has internal commutants in tracial matrix ultraproducts"
distinct_from:
  at-op62-holds-for-representation-lifts: "That proves the genuine-coordinate special case; this quantifies over arbitrary approximate lifts."
  kt-centralizer-normalization-hs: "That is invariance under ambient conjugation; this describes the coordinate algebra of the commutant."
  actor-commutant-has-liftable-masa-in-every-model: "That is a weaker partition-object claim at a particular pair with vertex-rounding assumptions; this is full internality for every Kazhdan homomorphism."
artifacts:
  - research/artifacts/liu-analytic-leaves-proof-acceptance-2026-09-20.md
  - research/artifacts/liu-theorem-five-assembly-cross-review-2026-09-20.md
  - research/artifacts/liu-section-six-acceptance-and-thom-bypass-2026-09-20.md
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
  - research/artifacts/liu-cairn-integration-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Theorem 1.2 / 6.7. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

**ESTABLISHED by the checked written chain for Jihao Liu's Theorem 1.2 / 6.7.** The graph now derives this claim from separately accepted analytic leaves and reviewed assembly, not a blanket citation of the final theorem. This is mathematical written-proof acceptance with named background imports, not a Lean certificate or an external human referee verdict.

For every finitely generated discrete group H with property (T), every nonprincipal ultrafilter omega on N, every sequence d_n>=1 and every homomorphism pi:H->U(M), where M=prod_omega(M_(d_n),tr_(d_n)), there are unital *-subalgebras A_n<=M_(d_n) with
```
pi(H)' cap M = [A_n]_omega.
```
The dimensions and ultrafilter are the specified originals. Pi need not be injective or preserve the regular character. The conclusion does NOT assert that supplied generator lifts are genuine representations or that their uncorrected exact coordinate centralizers suffice.

## Connections

This shared analytic premise feeds compression normalization and sequential Kazhdan heat rounding. It does not by itself assert dimension-free rounding of arbitrary bistochastic channels. The integration guide traces the two downstream group routes and their distinct scopes.

## Attempts

2026-09-20, initial pass: bounded parallel audits inspected §§3–8 and the Leavitt interface, leaving the long analytic imports open. That historical review boundary is superseded here by full written reconstructions of Theorem 3.2, Theorem 4.3, Lemmas 5.2–5.4, and the Section 6 matching/exhaustion implications, plus an independent cross-review of Theorem 5.1 assembly. Proposition 3.1 already had a checked direct proof. The route `kazhdan-internality-from-blocks-and-exhaustion` therefore has a closed derivation. Houdayer–Vaes, Ioana and standard property-(T)/finite-tracial-algebra facts remain explicitly credited background inputs. This does not certify every theorem in Liu's paper; in particular his stronger subgroup-only, one-model normalization statement has a separate review boundary.
