---
rg: 2
id: some-simple-kazhdan-lef-groups-are-not-exact
kind: claim
title: Some infinite finitely generated simple Kazhdan LEF groups are not exact
distinct_from:
  subshift-elementary-groups-are-exact: that asks whether the Z-subshift groups G_X are exact; this shows that some lamplighter hosts are not.
  lef-groups-embed-in-simple-kazhdan-lef-groups: that embeds every f.g. LEF group in a simple Kazhdan LEF host; this applies it to Osajda's groups to get non-exact hosts.
  universal-recursive-lef-host-is-not-exact: that shows that the one universal host for recursively presented LEF groups is not exact; this is the existence statement from Osajda's published theorem alone.
artifacts:
  - research/artifacts/sk-free-1-exactness-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Route: `some-simple-kazhdan-lef-groups-are-not-exact-proof`.

There is an infinite, finitely generated, simple group G with property (T) that is LEF, hence sofic and hyperlinear, and that is not exact.
- So G has no property A, and C*_r(G) is not an exact C*-algebra.
- At the same time, L(G) embeds in R^ω.

**Scope.**
- Without (T), simple LEF non-exact groups already follow from Kionke–Schesler (arXiv:2304.09307, abstract: every f.g. residually finite group embeds in a f.g. LEF simple group) together with Osajda's theorem. The new ingredient is (T).
- **Not claimed:** failure of Baum–Connes with coefficients, or of coarse embeddability into Hilbert space.
  - Osajda's residually finite relators are not expanders (`osajda-rf-relator-covers-are-not-expanders`).
  - No residually finite or LEF finitely generated group is known to fail coarse embeddability. Arzhantseva–Tessera's non-embeddable extension (IMRN 2019, arXiv:1605.01192) is a permutational wreath product over monster groups. This was a bounded web search.

**Review (sk-verify-15, 2026-09-13): PASS.** RF ⇒ LEF, the reviewed host, the coarse-embedding step, property A passing to subspaces and the Guentner–Kaminker–Ozawa equivalence re-derived. Osajda's Main Theorem checked at source (arXiv:1703.03791 e-print l.119–128). See `research/artifacts/sk-verify-15-2026-09-13-part1.md` §2.
