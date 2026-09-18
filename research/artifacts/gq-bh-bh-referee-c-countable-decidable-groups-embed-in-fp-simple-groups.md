# Referee C (end-to-end, adversarial) — the countable-input form of Boone–Higman

Nodes:
- `countable-decidable-groups-embed-in-fp-simple-groups` (claim, OPEN);
- routes `countable-decidable-bh-from-boone-higman` (BH ⇒ countable form) and
  `boone-higman-from-countable-decidable-bh` (countable form ⇒ BH).

**Verdict: PASS.** The equivalence is correct as stated.
- **Countable form ⇒ BH.** A finitely generated group with solvable word problem,
  with its finite generating set as the enumeration, is a countable decidable group
  in the survey's sense (§3.2: an enumerated generating set plus an algorithm
  deciding which words are trivial). This is trivial.
- **BH ⇒ countable form (survey Cor. 3.5, via Prop. 3.3).**
  - The Higman–Neumann–Neumann embedding of a countable group `G = ⟨s_1, s_2, …⟩`
    into a 2-generated group `G*` is effective: the images of the `s_i` are
    computable words. It preserves solvability of the word problem relative to
    the given enumeration. BH then applies to the finitely generated `G*`.
  - Decidability is relative to the enumeration in both directions, and the
    claim's statement quantifies existentially over it. This matches the survey's
    definition.
- **Not checked.** I did not re-read the survey's verbatim wording of Prop. 3.3 and
  Cor. 3.5 at source. bh-lit is fetching the survey, so the quotes can be checked
  against the LaTeX there.
- **No fixes.**
