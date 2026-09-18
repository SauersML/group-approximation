# bh-writeup board

Status: pass done 2026-09-18 ~14:40 CDT (relaunched after the 14:15 restart).

- Recovered: no unlanded drafts. work/bh-writeup/research/artifacts/gq-bh-bh-writeup-state.md was identical to main (408c4dc50).
- Landed: c7f12fba7, research/artifacts/gq-bh-results-summary.md. Written from main at ddeea47ea.
  - The printed-problem ledger: 20 answered in full (2 refereed, 11 internally checked, 7 lane-only) and 10 in part (2 checked, 8 lane-only).
  - It also covers the mechanisms M1–M8, literature errors, the corrections and mislabels, and what is still OPEN.
- Lessons-by-mechanism summary: gq-bh-bh-writeup-state.md (10:51), unchanged.
- Next pass:
  - add the post-restart landings;
  - upgrade tags when referee or verify artifacts land. Candidates for review: 17.60, 21.73, 21.74(b,c), 21.75, MO 339541, Kohl, RSV.

## Update 2026-09-18 ~16:10 CDT
- Landed 9285faff1 (GQ_BASE edit, on top of bh-ref-misc's 6a0a3642f).
  - Counts are now 21 full answers (9 refereed, 12 checked, 0 lane-only) and 10 partial answers (2 checked, 8 lane-only).
  - Added: the LISW Q1.11 row; the Matui reduction to minimal free Z^N SFTs; §7a with centrality (C), P2′b ⇔ FSG, recorded-census JE/product closure, and E1 ⇐ (D).
- Held: the Kourovka rows are "priority check pending" until bh-openq-lists reports on Morrison arXiv:2607.17477.

## Update ~16:30 CDT
- Landed 83b72158d. It removes every priority hold (the user wants generous credit, not priority risk) and adds §0 Credits (2607.17477, Kochloukova–Luiz, Garrido–Reid, and the works our proofs rest on).
- New rows: FFWZ Q5.9, Reid non-fp, the wider Tanner result, and 21.74(a)/17.58 as open.
- Counts are now 22 full (9 R / 12 IC / 1 LP) and 10 partial. Pending referees: bh-ref-ffwz (Q5.9) and bh-ref-engines (Reid non-fp).

## Update ~16:50 CDT
- Landed 5517bb801: counts are now 22 full (12 R / 10 IC / 0 LP) and 10 partial.
- Not counted: T_{2,3}/T_tau/V_tau (the literature asserts them; credited in §5) and 21.140 (a reduction, §4).
- Next review: FFWZ Q5.9 part 2 through the repo criterion.

## Update ~16:58 CDT
- Landed 33608375d: the BS(1,2) chain nodes failed review (4b2fdd3d9) and are OPEN; added a restricted-wreath scope note. Counts unchanged.
- Flag (not my file): baumslag-gersten-in-b-a-from-a-root-separated-shift still says the chain node "settles the base K".
