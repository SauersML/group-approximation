# sk-review-6, part 5: Alekseev–Thom §5 on known sofic Kazhdan groups that are not residually finite (queue entry 7, rev4 E2) (2026-09-13)

Lane sk-verify-6.
- **Request (sk-referee-significance, rev4 item E2):** quote verbatim, with locator, what Alekseev–Thom arXiv:2608.05362 §5 say about known sofic or hyperlinear Kazhdan groups that are not residually finite. Is it Thom's group only, and is there a printed question?
- **Source:** arXiv:2608.05362 v1 (only version; submitted 5 Aug 2026), e-print `main_final.tex`, fetched on MSI. Title "Centralizers of sofic approximations of Kazhdan groups". No journal version exists.
- **Numbering:** `\newtheorem{theorem}{Theorem}[section]`, shared by proposition, lemma, corollary, conjecture, openproblem, definition and remark.
- **Section order:**
  1. Introduction (l.80)
  2. Definitions and preliminaries (l.143)
  3. Approximate intertwiners … (l.415)
  4. The cluster groupoid (l.908)
  5. Stability and proof of the main theorem (l.1514)
  6. Open problems (l.1727)
- **§5 numbered environments:** Proposition 5.1 (l.1541), Corollary 5.2 (l.1694).

## Verdict: E2 HOLDS as worded (optional credit addition below)

### Verbatim, §5, closing paragraphs after Corollary 5.2 (l.1705–1726)
> "This conclusion for finitely presented Kazhdan groups is compatible with the known examples, in the sense that it neither contradicts the conjecture above nor proves the existence of a non-sofic group.
>
> Let's review some of the known examples:
> First, the second author constructed a Kazhdan group which is locally embeddable into finite groups, hence sofic, but not residually finite \cite{ThomHyperlinear}. Since a discrete Kazhdan group is finitely generated, this gives a finitely generated sofic Kazhdan group which is not residually finite. It is not finitely presented: every finitely presented LEF group is residually finite, because the finite presentation turns sufficiently good local embeddings into genuine finite homomorphisms.
> Second, de Cornulier constructed finitely presentable non-Hopfian Kazhdan groups \cite{deCornulier}. Since finitely generated residually finite groups are Hopfian, these groups are not residually finite. Related examples are known to be hyperlinear by work of the second author \cite{ThomHyperlinear}, but they are not known to be sofic.
> Third, Kar and Nikolov constructed finitely presented sofic groups which are not residually finite \cite{KarNikolov}. These examples do not have Kazhdan's property."

Corollary 5.2 (l.1694–1698), just before it: "If a finitely generated Kazhdan sofic group admits an embedding as in the Hayes--Kunnawalkam Elayavalli conjecture, then it is LEF. In particular, every such finitely presented group is residually finite."

**Bibliography (l.1787–1848):**
- `ThomHyperlinear` = A. Thom, *Examples of hyperlinear groups without factorization property*, Groups Geom. Dyn. 4 (2010), no. 1, 195–208, which is the note's `Thom`;
- `deCornulier` = Proc. AMS 135 (2007), no. 4, 951–959;
- `KarNikolov` = *A non-LEA sofic group*, Proc. Math. Sci. 127 (2017), no. 2, 289–293.

### Is it Thom's group only?
Yes, within this list. §5 names three families:
1. **Thom's group:** Kazhdan, LEF (so sofic), not residually finite, not finitely presented. It is the ONLY sofic Kazhdan non-RF group they list.
2. **de Cornulier's groups:** finitely presentable, Kazhdan, not RF. Only "related examples" are hyperlinear (Thom), and they are "not known to be sofic".
3. **Kar–Nikolov:** finitely presented, sofic, not RF, but not Kazhdan.

### Printed question
§5 prints no question. The printed question is §6 Open problem 6.1 (l.1731–1733): "Are there examples of finitely presented sofic groups with Kazhdan's property~\((T)\) that are not residually finite?" It is already cited in the note's Q1 paragraph (verified by sk-lit-locators, row 25).

### E2 sentence check
Proposed: "The groups $G_X$ are sofic Kazhdan groups that are not residually finite, as is Thom's group, but they are also simple."
- **Mathematically true:** G_X is infinite and simple, so it is not residually finite; it is LEF, hence sofic, and Kazhdan.
- **Faithful to §5:** Thom's group is the listed sofic Kazhdan non-RF example.
- **No "only" claim**, so the de Cornulier and Kar–Nikolov entries do not make it false.
- **Optional addition (not required):** cite the printed discussion, e.g. "as is Thom's group~\cite{Thom}, \cite[\S5]{AlekseevThom}". The parallel could also add "LEF, not finitely presented", since §5 says exactly that of Thom's group and the note proves it of G_X.
- **Do not write** "Alekseev and Thom list Thom's group as the only known …". Their text reviews "some of the known examples".
