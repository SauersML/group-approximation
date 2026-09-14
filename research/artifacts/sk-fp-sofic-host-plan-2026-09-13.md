# sk-fp-sofic-host: plan (2026-09-13, wave 10)

Lane sk-fp-sofic-host. This is the moonshot for the note's first question: is there an infinite finitely presented simple
Kazhdan group that is sofic? The note's Q1 cites Alekseev–Thom Open problem 6.1.

## What is already mapped (read on main, not re-derived)
- **Firewalls for simple candidates:**
  - `gap-sofic-approximations-are-local-embeddings` (gapped permutation targets force LEF);
  - `fp-simple-groups-have-no-classical-group-unitary-models`;
  - `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`;
  - `fp-simple-groups-escape-soft-hyperlinear-permanence`;
  - `sofic-permanence-closure-omits-simple-fa-nonsofic-groups`;
  - amenable and Haagerup orbit full groups.
- **Candidate gates:**
  - `km-246-lattice-is-sofic` (free rank-2 Levi charts; interpolation dead);
  - `titz-witzel-soficity-is-one-finite-csp`;
  - `sofic-fp-simple-kazhdan-group-from-fp-simple-ring` (gates a–c);
  - Leavitt units: nonsofic.
- **Non-simple 6.1 candidate on main:** `deligne-triple-cover-is-sofic` (OPEN), with the w4-deligne campaign's rank, sector and
  cosystole nodes.

## Status check at source (MSI, arXiv e-print 2608.05362, `main_final.tex`)
- Open problem 6.1 (l.1732) is verbatim as the note quotes it.
- The paper's review (l.1705–1724) separates three regimes:
  - Thom: f.g. LEF Kazhdan non-RF;
  - de Cornulier: f.p. non-Hopfian Kazhdan, with hyperlinear relatives (Thom);
  - Kar–Nikolov: f.p. sofic non-RF, not Kazhdan.
- A footnote (l.91) cites the OpenAI announcement of a nonsofic group that "can be taken finitely presented and Kazhdan".

## Angles
1. **A permanence firewall for 6.1 itself (no simplicity).** Every finitely presented Kazhdan group in the closure of the LEA groups
   under subgroups, directed unions, sofic-by-amenable extensions, graphs of groups and finite direct products is
   residually finite.
   - So no known soficity certificate answers 6.1, and neither does any certificate of this shape.
   - Sharpness: allowing amenable-KERNEL extensions breaks it, as Deligne's triple cover shows.
2. **Both recorded 6.1 candidates are amenable-by-residually-finite.**
   - Deligne's triple cover: C_3 central over Sp_4(Z).
   - de Cornulier's group: Prüfer centre, as Thom reads it.
   - So one permanence theorem, "central amenable-by-RF ⇒ sofic", would answer 6.1. Check at source whether that is open.
   - For the simple form Q1 the same theorem is useless: a simple group has no nontrivial amenable normal subgroup.
     Q1 needs approximations that do not come from permanence at all.
3. **Only if time remains:** a direct attack on one gate, the smallest Titz–Witzel CSP or the km-246 one-stable-letter form.

## Not duplicating
- sk-fp-sofic-a/b/c/d, ex-fp-kazhdan-*, w4-deligne-*.
- sk-sofic-host-hamming (the sofic host question).
- sk-answered-questions (printed questions in general).

## Deliverables
- A claim node plus proof route for angle 1, queued with sk-verify-13.
- A status artifact with verbatim quotes and search bounds.
- A proposal artifact only if the note's Q1 sentence has to change.
