---
rg: 2
id: residually-finite-finitely-presented-non-exact-group
kind: claim
title: Some finitely presented residually finite group is not exact
distinct_from:
  fp-simple-nonexact-group: that asks for a finitely presented SIMPLE non-exact group, which is never residually finite; this asks for a finitely presented RESIDUALLY FINITE one, the opposite end.
  decidable-residually-finite-non-exact-group-exists: that is Osajda's residually finite non-exact group with decidable word problem, which is infinitely presented; this asks for a finite presentation as well.
  word-codings-of-t2-force-finite-presentation: that shows a word-coded T2 lift group would be a group of the kind asked for here; this is the standalone existence question.
---

**OPEN.** There is a finitely presented, residually finite group without property A, equivalently one
whose reduced C*-algebra is not exact.

**Who asked.** Neither this lane nor referee bh-ref-c (db76e030f3) found a printed statement of this
question, after searching arXiv and the web (Osajda, Sapir, Arzhantseva, Guentner, Willett–Yu). As far as we
know it is first recorded here. That is a statement about our search, not a claim that nobody has asked it.
- It was raised in this project in bh-ref-q12's review of `word-codings-of-t2-force-finite-presentation`
  (b8aa255019). That review corrected "finitely presented non-exact" to "finitely presented,
  residually finite, non-exact".
- The coordinator then asked that it be recorded.
- Its two halves are classical:
  - Gromov asked for finitely presented groups coarsely containing expanders; Sapir, arXiv:1103.3873, gives
    them.
  - Brown–Ozawa, Problem 10.4.6, asked for residually finite non-exact groups; Osajda, arXiv:1703.03791,
    gives them.
- If a printed source turns up, credit goes to it.

**What is known.**
- **Residually finite, not finitely presented.** Osajda's groups are "defined by infinite graphical small
  cancellation presentations" and are limits of hyperbolic CAT(0)-cubical groups (arXiv:1703.03791, pp. 1–2,
  read at source).
- **Finitely presented, residual finiteness unknown.**
  - Sapir's aspherical groups coarsely containing expanders (arXiv:1103.3873, abstract read).
  - Higman-type embeddings of recursively presented non-exact groups. These do not preserve residual
    finiteness in general.
- **Finitely presented residually finite, but exact.** The following classes are all exact:
  - linear groups over commutative rings (Guentner–Higson–Weinberger);
  - hyperbolic groups;
  - cocompactly cubulated groups (Campbell–Niblo);
  - the Kharlampovich–Myasnikov–Sapir solvable groups of arbitrary algorithmic complexity
    (arXiv:1204.6506).
- A finitely presented residually finite group has solvable word problem (McKinsey–Mal'cev). So a witness
  is automatically a decidable finitely presented non-exact group.

**Why it matters here.**
- By `word-codings-of-t2-force-finite-presentation`, item 2(b), a word coding of a T2 lift group needs such
  a group.
- A witness with a free-enough residual chain would also be the natural input for
  `one-sided-t2-lift-groups-are-periodically-closed-quotients`.
- **Routes.**
  - An embedding theorem preserving residual finiteness. It could only apply to non-exact groups with
    solvable word problem, since finitely generated subgroups of finitely presented residually finite groups
    have one. Osajda's groups from a recursive input sequence are decidable by
    `decidable-residually-finite-non-exact-group-exists` (ESTABLISHED there, unreviewed). Decidability of
    his groups in general is unchecked.
  - A finitely presented residually finite group containing Osajda's group, e.g. a finitely presented
    subgroup-separable or virtually special overgroup of a direct limit of his hyperbolic cubical groups.
    None is known.

## Attempts

(none yet)
