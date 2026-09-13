# RF_fp and LEF_fp Π⁰₂-completeness: open-status and priority pass (2026-09-13)

Lane `ex-novelty`, 00:10–00:45 CDT, run at the coordinator's request.

**Claims checked.** Both are from ex-complexity-sofic, passed by ex-verify-groups at 20a6a58d14
(`research/artifacts/ex-review-groups-2026-09-12-part3.md`, §3.2).
- `residual-finiteness-of-finite-presentations-is-pi2-complete`: RF_fp is Π⁰₂-complete and NONRF_fp is
  Σ⁰₂-complete, with hardness already inside finitely presented groups of A_p²A.
- `lef-of-finite-presentations-is-pi2-complete`: the same for LEF_fp, through Vershik–Gordon.

**Method.**
- LaTeX sources fetched on MSI from `arxiv.org/e-print`:
  - KMS 1204.6506v5;
  - Bridson–Wilton 1401.2273;
  - Rauzy 2002.02540, 2002.02541, 2111.01190, 2111.01179 and 2605.30138;
  - Darbinyan–Rauzy 2508.11973.

  I grepped them for decidability, completeness, Π⁰₂/Σ⁰₂, Higman and open-question passages, and read the hits
  in context.
- arXiv abstracts.
- OpenAlex citing works of KMS: 19, titles only.
- arXiv search listings.

**Limits.** Web search was exhausted, and OpenAlex rate-limited most title searches.

**Tags.**
- S: source read.
- A: abstract.
- T: title only.
- C: Cairn text on main.

## (a) Where the question is printed

- **The completeness question itself is not printed anywhere I found.** KMS §1.1.7 ("What next?") prints a
  different question (S): "Thus it would be very interesting to find out whether every finitely generated residually
  finite group with solvable word problem embeds into a finitely presented residually finite group." They call it "the
  residually finite version of the Higman embedding theorem".
- **Cairn's baseline fuses two questions.** It says "`Pi^0_2`-completeness of `RF_fp` is the residually finite Higman
  problem, open in the literature" (C: `residual-finiteness-of-enumerated-presentations-is-pi3-complete` and its
  two-generator sibling). That joins the repository's complexity cell to the printed embedding question.
  - The cell is framed by the repository.
  - The name records where a property-safe Higman compiler dies (C: `open-cells-arithmetical-complexity-of-group-properties`,
    Attempts).
- **The printed embedding question was answered negatively.** Rauzy, *Obstruction to a Higman embedding theorem for
  residually finite groups with solvable word problem*, arXiv:2002.02540 (v2, 17 Mar 2021; J. Group Theory, DOI
  10.1515/jgth-2020-0030), (S, A):
  > "the authors ask whether ``unsolvability of the word problem is the only obstacle'' ... We answer negatively to
  > that question: There exists a finitely generated residually finite group with solvable word problem, that does not
  > embed in any finitely presented residually finite group."

  Darbinyan–Rauzy, arXiv:2508.11973, subsection "Obstructions for Higman's embedding theorem for RF groups with
  decidable WP, and a generalization" (S), strengthens this through Turing degrees of residual-finiteness growth.
- **Consequence on main.** `rf-higman-embedding-for-decidable-groups` is marked OPEN, but Rauzy 2020 refutes its
  universal statement. Consumers that assume a positive answer need rewording:
  - the route `unbounded-prime-torsion-via-rf-higman-embedding`;
  - `regular-tree-torsion-obstruction-2026-09-12.md`;
  - `fp-rf-boone-higman-via-fp-self-similar-overgroups`.

  Rauzy's group is not the group they apply the question to, so a specific embedding stays possible. Only the general
  theorem is refuted.

## (b) Was Π⁰₂-hardness or completeness of RF_fp or LEF_fp known?

Within this bound, no.

- **KMS 1204.6506v5 (S).** The machine groups come with residual finiteness under a single hypothesis. Theorem (label
  `t:rfg1`):
  > "If a Minsky machine M is sym-universally halting then the group G(M) is residually finite. Its word problem is at
  > least as hard as the halting problem for M."
  - The introduction says informally that "for the group to be residually finite the Minsky machines should be
    sym-universally halting". No converse is stated, and recognition complexity is not discussed.
  - Section 6 strengthens Slobodskoi: "the universal theory of any set of finite groups that contains all finite
    solvable groups of class 3 is undecidable".
  - The lane's converse (Lemma A: a divergent pumped configuration forces failure of residual finiteness) is not in
    KMS.
- **Bridson–Wilton,** *The triviality problem for profinite completions*, arXiv:1401.2273 (Invent. Math. 2015) (S, A):
  "There is no algorithm that can determine whether or not a finitely presented group has a proper subgroup of finite
  index". The set is "recursively enumerable but not recursive". This is undecidability, not a Π⁰₂ lower bound for
  residual finiteness.
- **Rauzy,** *Remarks and problems about algorithmic descriptions of groups*, arXiv:2111.01190v2 (IJAC 2025) (S),
  Proposition "RF not CE":
  > "The set of finitely presented residually finite groups is not computably enumerable (for ν_FP), and furthermore it
  > cannot be contained in a ν_FP-c.e. set of finitely presented groups with uniformly solvable word problem."

  The proof combines McKinsey with KMS. This is the nearest printed lower bound: RF_fp ∉ Σ⁰₁. Completeness implies it,
  and it should be credited wherever the ledger records the strict placement of RF_fp.
- **Rauzy,** *Residual properties of finitely generated groups in the Weihrauch lattice*, arXiv:2605.30138 (28 May 2026)
  (S). Classical descriptive set theory on the space of marked groups:
  - The introduction: "The set of residually finite groups is Σ⁰₃-complete ... answers a problem of [Benli2019]".
  - The appendix: "the set of residually finite groups is boldface Π⁰₃-complete in the space of marked groups (a question
    left open in [Benli2019], where the upper bound Π⁰₄ was given)".
  - The Σ/Π mismatch is in the source itself.
  - This is boldface complexity of a subset of the space of marked groups, not the lightface index set on finite
    presentations. It is still prior art to cite beside `residual-finiteness-of-enumerated-presentations-is-pi3-complete`.
- **Rauzy,** arXiv:2002.02541 and 2111.01179 (S, A). Computable finite quotients, and effective Borel classifications,
  e.g. "the set of LEF groups is a closed set that is computably a G_δ, but not computably closed". No completeness result
  for RF_fp.
- **Darbinyan–Rauzy,** arXiv:2508.11973 (S, A). Growth and Turing degrees. Nothing on recognizing RF_fp, which agrees with
  the lane's own note.
- **Bilanovic–Chubb–Roven,** arXiv:1903.05143 (C, from the ledger's 2026-08-26 sweep; source not re-read). Π⁰₂-hardness of
  Markov properties on recursively presented groups. Their only Π⁰₂-completeness example on finite presentations is
  Lempp's result on torsion-freeness. RF_fp is not covered.
- **OpenAlex citers of KMS** (19, T). Among them: the two Rauzy papers above, computability of Følner sets, residual
  finiteness growth, Dehn functions of metabelian groups. No title suggests a complexity result for recognizing residual
  finiteness.
- **"Cirisanu."** No OpenAlex author and no arXiv search hit. The name may be misspelled.
- **Kharlampovich's 1980s results,** read only through KMS's summary.
  - [Kh81]: a finitely presented group with undecidable word problem in A_p²A ∩ ZN_3A.
  - Slobodskoi 1981: undecidability of the universal theory of finite groups.
  - Neither is a Π⁰₂-hardness statement for residual finiteness. The originals were not read.

## (c) Credits the nodes should carry

- **KMS arXiv:1204.6506v5** (Bull. Math. Sci. 2017): the groups G(M), their A_p²A structure, and the sufficiency theorem
  above. Imported by the lane in `rf-fp-pumped-minsky-part1-2026-09-12.md` §1. Adequate.
- **Kharlampovich 1981,** through KMS, for Minsky-machine groups in A_p²A.
- **McKinsey 1943** (finitely presented and residually finite ⇒ solvable word problem) and **Vershik–Gordon** (finitely
  presented LEF groups are exactly the residually finite ones). Both already used.
- **Rauzy arXiv:2111.01190,** Proposition "RF not CE", for the non-c.e. half of the placement, and **Bridson–Wilton
  1401.2273** for undecidability of nontrivial finite quotients. The lane's novelty paragraph (C: part 3, §5) cites neither.
- **Lempp** (torsion-freeness of finitely presented groups is Π⁰₂-complete) and **Bilanovic–Chubb–Roven,** as precedents
  for Π⁰₂ results on finite presentations.
- **Universal halting.** It is a classical Π⁰₂ phenomenon for counter machines. The lane proves its clocked version directly
  (Lemma C). No specific source was checked here.

## Verdict

- **Novelty.** No prior statement of Π⁰₂-completeness for RF_fp or LEF_fp was found; within this bound, the result is new.
  The nearest printed results are partial:
  - RF_fp is not c.e. (Rauzy 2021, from KMS);
  - having a nontrivial finite quotient is undecidable (Bridson–Wilton 2015);
  - residual finiteness is boldface Π⁰₃-complete on the space of marked groups (Rauzy 2026).
- **Framing.** The question as stated appears in no source found. Do not present the result as solving "the residually
  finite Higman problem". The printed embedding question of KMS §1.1.7 was answered negatively by Rauzy (arXiv:2002.02540),
  so `rf-higman-embedding-for-decidable-groups` is stale on main.
- **Bound.**
  - 8 sources grepped;
  - 19 citing titles;
  - no web search and no MathSciNet;
  - the Kharlampovich and Slobodskoi originals not read;
  - most OpenAlex title searches rate-limited.
