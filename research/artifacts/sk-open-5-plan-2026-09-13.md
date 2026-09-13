# sk-open-5 plan: the questions the note should end with

Lane `sk-open-5`, 2026-09-13. Lens: find sharp open problems whose answers would matter, and whose natural starting point is the note's construction. Settle any that fall quickly.

## Target
A §6 proposal for a closing subsection "Questions", at most ~15 lines of the note, with 2–4 questions. Each question gets:
- (i) a precise statement;
- (ii) a one-sentence motivation from the note;
- (iii) a bounded literature check that it is open, with the bound recorded;
- (iv) wiring to a Cairn root.

Cheap settlements land as Cairn claims with proofs. At most they become half-sentences that sharpen a question.

## Candidate questions (initial ranking)
1. **Finite presentation.** Is there a finitely presented infinite simple Kazhdan group that is sofic, or at least hyperlinear?
   - LEF cannot work: a finitely presented LEF group is residually finite.
   - Root on main: `hyperlinear-fp-infinite-simple-kazhdan-group`; parent `hyperlinear-fp-infinite-simple-group`.
   - To check: status of the Caprace–Rémy Kac–Moody lattices, Burger–Mozes lattices and Thompson-like groups; Pestov's guide §9; `ex-open-status-2026-09-12.md`.
2. **Beyond periodic patterns.** Is EL_3(LC(X,F_2) ⋊ Z²) sofic for a free minimal Z²-SFT X, e.g. Labbé's 19-tile shift?
   - Root on main: `free-minimal-subshift-elementary-groups-are-sofic`.
   - The periodic-model proof in the note fails for such X. The groups are simple mod centre, Kazhdan and F_q-linear sofic (`free-minimal-subshift-elementary-groups-are-simple-kazhdan`, unreviewed).
   - A yes, together with finite presentation of the ring route, gives question 1. A no gives a linear sofic nonsofic group.
3. **Rigidity.** Does G_X determine X up to flip conjugacy, or up to strong orbit equivalence?
   - Owned mathematically by sk-rigidity-ring and sk-rigidity-intrinsic. Related open node: `elementary-group-lef-growth-separates-subshifts`.
   - This lane only certifies the statement and its status.
4. **Characters**, if sk-characters leaves it open: are 1 and δ_e the only characters of G_X?
5. To test and probably discard: a torsion-free version; C*-simplicity; MF reduced C*-algebra; bounded elementary generation; stability.

## Quick settlements to attempt
- Flip conjugacy of X and Y gives G_X ≅ G_Y. Tower identity: for the k-level tower X^(k) (again an infinite minimal subshift), R_{X^(k)} ≅ M_k(R_X), so EL_{3k}(R_X) ≅ G_{X^(k)}. So the family {G_X} already contains EL_{3k} of every subshift ring. This calibrates the rigidity question.
- Stability: G_X is neither P-stable nor HS-stable (folklore). Check coverage on main before landing anything.
- Any candidate whose answer already follows from reviewed nodes on main.

## Not duplicating
- sk-fp-sofic-a/b work on questions 1–2 mathematically.
- sk-rigidity-* work on question 3; sk-characters on question 4.
- sk-questions-oa/ggt mine PUBLISHED questions that G_X answers.
- This lane chooses and certifies the questions the note should POSE, and closes the cheap ones.
