# skf-approximants — ledger for tex 459–514 of simple_kazhdan_sofic_group.tex

Lane brief: `ct/ROSTER-sk.md` (session nonsofic-existence-49), range tex 459–514 at origin/main b965d63ba (subsec:approximants:
prop:marked, rem:fibonacci).

## Blocker: the committed note changed underneath the range

- At 18:54 origin/main landed bf961c128, "Replace the sofic simple Kazhdan note with its shortened version". The committed
  `simple_kazhdan_sofic_group.tex` is now 340 lines, md5 7b3dc4ec92b4581553bc0dc2b0edcb99. The roster target b965d63ba was
  970 lines, md5 3a11a03d23cb580bd629d313a6b7a1c1.
- The new text has no subsection "Finite simple approximants", no `prop:marked` and no `rem:fibonacci`. The
  PSL_{3N}(F_q) → S marked-group convergence and the Fibonacci first model (SL_15(F_p)) are not in the committed note.
- Nothing in the current note corresponds to tex 459–514:
  - its "Finite models" subsection (current tex 118–153) carries the LEF models, which were b965d63ba's sec:lef material;
  - Morse–Hedlund is cited only in the word-problem section (current tex 252), for Sturmian complexity.
- So there is no sentence to formalize in this range at the current tip. I built no Lean and appended no census rows.

## Structure of the committed note (bf961c128, 340 lines), for a re-split

| current tex | content |
|---|---|
| 1–66 | title, abstract, introduction, `thm:main` (l.44) |
| 67–117 | "Proof of Theorem 1": the ring and property (T), `eq:elementary` (l.88) |
| 118–153 | "Finite models": LEF models over F_2, entrywise; sofic and hyperlinear models |
| 154–228 | "A finite tower detects every normal subgroup", `eq:absorb` (l.168); includes GL_d(F_2) = SL_d(F_2) = PSL_d(F_2) (l.217) |
| 229–263 | "Every word-problem degree", the corollary (l.231); Morse–Hedlund for Sturmian complexity (l.252) |
| 264–340 | "Origin and authorship", bibliography |

The roster's label table (thm:degrees, lem:subshift, prop:simple-ring, lem:windows, prop:ultraproduct, lem:level, thm:root,
cor:consequences, prop:degree, ...) refers to b965d63ba and is obsolete at the tip.
