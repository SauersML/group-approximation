
## 37. w7-sub-multiletter follow-up (07136ca640)

Sources:
- Artifact `multiletter-split-borel-and-coefficient-firewalls-2026-09-12.md` (blob `e60bf257`), Section 6.
- `lex-decreasing-units-with-order-preserving-letters-are-amenable` (blob `1d8fdf38`).
- `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (blob `915925b1`).

**Verdict: PASS. The correction of 35.4 has been applied.**
- **Lemma 6.1.** The hypothesis now requires that, for each of the frames at `A` and `A1`, all positive roots move
  points in one common direction.
  - The "Same direction" step carries the direction at `A` to `S[A10]T[A110]`, and so to the whole frame at `A1`.
  - The "Not preserved" step is unchanged.
  - This is the corrected statement of 35.4, proved by the same two steps.
- **Remark.** The added remark reproduces the counterexample of 35.4, including the block order
  `[A0] < [A10] < [A111] < [A110]`. It rests item 1 of Section 6 on the common-direction hypothesis, which is what
  Theorem 3.5 uses.
- **Wording.** Two places now say "monotone in one common direction":
  - the Scope of the lex claim;
  - the w7-sub-multiletter bullet on the SUB target.
- **Status.** No claim statement changed, so the PASS of Section 35 carries over to the new blobs.
