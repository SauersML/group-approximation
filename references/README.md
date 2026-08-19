# references/

These documents are from **OpenAI's paper** on the nonsofic group
construction. They are kept here for reference only:

- `counterexample.tex` — the expander-matching criterion and counterexample
  material (an excerpt; its page numbering continues from the source
  document).
- `reasoning.tex` — the chapter *Constructing a Non-Sofic Group*.

Nothing in this directory is imported by the Lean library or used by any
proof, audit, or CI gate, and these files are distinct from the repository's
own manuscripts, `non_mf_groups_exist.tex` and `property_tt_leavitt.tex`.

## Do not inherit these two things from the copy

They are verbatim from the source and are left untouched here, but the
repository's own writing must not repeat them.

1. **Kun's year.** `counterexample.tex` cites the expander decomposition as
   `[Kun19] … preprint, 2019, arXiv:1606.04471v5`.  The paper is
   arXiv:1606.04471, **June 2016**; 2019 is a revision date.  Our own
   manuscript already dates it "preprint, 2016" and
   `notes/CREDIT_AND_PRIORITY_AUDIT.md` credits "Kun 2016 / Kun–Thom 2019"
   for the (T)-rigidity-of-approximations engine.  Keep it that way.

2. **"The soficity conjecture."**  The chapter title and abstract say the
   soficity conjecture is disproved, and the introduction says the question
   "became known as the soficity conjecture" while citing it as
   `[Pes08, Open Question 3.8]` — an open question, not a conjecture.  Weiss,
   who named sofic groups, wrote in the same 2000 paper that not all groups
   are likely to be sofic; the expectation in the literature was that a
   counterexample exists.  The current PDF retitles the chapter *Nonsofic
   groups exist*; both versions are tabulated in
   `research/openai-leavitt-unit-nonsofic.md`.

Related: the priority claim "no progress … for at least a decade" was
redacted from the announcement on 2026-08-03 and is citable via
Fournier-Facio, arXiv:2608.02025, footnote 2.  Kun–Thom's own v3
introduction describes Proposition 2.3 as "a creative and effective
application of the results and techniques of this paper and the ones in
[18]", which is the attribution the copy's framing obscures.

https://openai.com/index/ten-advances-in-mathematics/
https://cdn.openai.com/pdf/ten-proofs-oai.pdf
