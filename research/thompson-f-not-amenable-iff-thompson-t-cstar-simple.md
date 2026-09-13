---
rg: 2
id: thompson-f-not-amenable-iff-thompson-t-cstar-simple
kind: claim
title: Thompson's group F is non-amenable iff Thompson's group T is C*-simple
distinct_from:
  thompson-f-amenable-iff-group-ring-is-ore: that turns amenability of F into the Ore condition for its group ring; this turns non-amenability of F into simplicity of the reduced C*-algebra of the overgroup T.
  thompson-t-disjoint-pair-cstar-simple-subgroup-criterion: that says a C*-simple subgroup of T containing a disjoint pair forces F non-amenable; this is the two-way equivalence for T itself, imported from the literature.
artifacts:
  - research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13-part2.md
---

**ESTABLISHED by citation.** The following are equivalent:
- (i) Thompson's group `F` is non-amenable;
- (ii) `F` is C*-simple;
- (iii) Thompson's group `T` is C*-simple, i.e. `C*_r(T)` is simple.

Sources:
- (iii) ⇒ (i): U. Haagerup and K. K. Olesen, *Non-inner amenability of the Thompson groups T
  and V*, arXiv:1609.05086, Theorem 4.5: "If C*_r(T) is simple, then F is non-amenable."
- (i) ⇒ (iii), and the full equivalence: A. Le Boudec and N. Matte Bon, *Subgroup dynamics
  and C*-simplicity of groups of homeomorphisms*, arXiv:1605.01651v3, Theorem 1.6. Their
  abstract states the converse of Haagerup–Olesen verbatim.

**Consequence.** C*-simplicity of `T` is a certificate class for non-amenability of `F`:
- `thompson-f-not-amenable-from-t-cstar-simple` goes one way;
- `thompson-t-cstar-simple-from-f-not-amenable` goes the other.

The two routes form a cycle through `thompson-t-is-cstar-simple`, which records an
equivalence and is not a fixpoint defect. The subgroup form of the certificate is
`thompson-t-has-cstar-simple-subgroup-with-disjoint-pair`.

**Scope.**
- Both theorem statements were read verbatim from the arXiv LaTeX sources on 2026-09-13; see
  the citation route.
- The Haagerup–Olesen proof outline was read; the Le Boudec–Matte Bon proof was not re-read.
- Le Boudec–Matte Bon also prove a stronger form: if `F` is non-amenable, every overgroup of
  `F` in `Homeo(S^1)` is C*-simple.
- Breuillard–Kalantar–Kennedy–Ozawa re-obtained (iii) ⇒ (i), as Haagerup–Olesen record.

Citation route: `thompson-f-not-amenable-iff-thompson-t-cstar-simple-citation`.
