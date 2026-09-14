---
rg: 2
id: cckw-kms-triangle-groups-structure-citation
kind: route
title: Import Caprace--Conder--Kaluba--Witzel Theorem 3.1, the KMS presentations of Section 7.2, Proposition 7.6, Theorem 7.7 and Corollary 7.8
target: cckw-kms-triangle-groups-structure
requires: []
---

Citation import, not a reproof.

Source: arXiv:2011.09276, read from the ghostscript text extraction on MSI
(`/scratch.global/sauer354/hs-cand/cckw2.txt`, the extraction already used by
`cckw-ghb2-kms-group-structure-citation`), 2026-09-14:
- Theorem 3.1 (i)–(v) with its proof sketch: extraction lines 772–820;
- the definition of half girth type and generalized triangle groups: lines 821–833;
- Theorem 1.3: lines 142–157;
- §7.1, Propositions 7.1 and 7.2: lines 2351–2420;
- §7.2, the class `C`, the ten presentations and Remark 7.5: lines 2540–2600;
- Proposition 7.6 (half girth types) and Theorem 7.7 (i)–(iv): lines 2600–2700;
- the (T) ranges in the proof of Theorem 7.7, the index-3 overgroups, and Corollary 7.8: lines
  2700–2730.

Verification boundary:
- **Not re-read:** the proofs of Theorem 3.1 (i), (v) (cited to Bridson–Haefliger II.12.28), of
  Theorem 7.7, and of Proposition 7.1.
- **Extraction damage:** sub- and superscripts are flattened, and minus signs can be lost. The
  presentations above were checked against the compiled `GHB p` presentation in
  `GroupApproximation/Kazhdan/KMSGroupPresentation.lean` for `G_{HB_2^{(2)}}` only. For the other
  families, the commutator words are read from the extraction.
- **Downstream use:** `kms-hb2-girth-surfaces-give-surface-subgroups-proof` uses only Theorem 3.1
  (i), (iv), (v), plus Corollary 7.8 for property (T). It proves the vertex group structure,
  intersections and link girths of `G_{HB_2^{(2)}}(p)` itself.

This route asserts only that the source says what the claim records.
