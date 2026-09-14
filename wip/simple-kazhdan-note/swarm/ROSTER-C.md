# SK roster C: arbitrary choices, cuts, necessity

Added ~18:50 after the user asked: "what about things in manuscript that are arbitrary? what about that which is unnecessary and can be dropped? etc."
Line numbers refer to `$SK/manuscript-disk-1646.tex`. Each brief is a starting point, not a cage (RULES §1).

## sk-arbitrary
Examine every choice in the note that nothing forces:
- the hypotheses, the ring, n = 3, F_2;
- constants: 2w+3, d ≥ 9, 2k+1, N > twice the exponent;
- symmetric index ranges (|a| ≤ m);
- conventions: (Tx)_n = x_{n+1}, [g,h];
- generating sets, the choice of s and of translates;
- the Sturmian family and √2−1;
- notation: E_ab(W), B_m(U), D_y; section order.

For each one: is it forced? If not, give the canonical choice, or the general statement at no extra length.

Main's seeds (verify them, do not trust them):
1. l.180: 2w+3 → 2w+2, since only levels |a| ≤ w+1 are used.
2. l.189-193: translates are unnecessary, since e_C u = E_{0,-1}(C) and e_C u^{-1} = E_{01}(C) lie in B_1(C).
3. l.200: only d ≥ 3 is used, so d ≥ 9 is noise.
4. l.95: the generator 1 is redundant (1 = Σ e_a).
5. l.96: the commutator convention affects neither eq. (1) nor the argument.
6. l.205-215: the E_bb commutator re-derives [t_xy,t_yz] = t_xz, so one sentence suffices.
7. EL_3 → EL_n for every n ≥ 3, at no cost.
8. F_2 is the one field with no centre quotient and no signs: say so, or generalize.

Deliverable: `sk-arbitrary-proposal` in §6 format, with verbatim before/after for each item.
Peers: sk-cut-sentences, sk-proof-minimal-concrete, sk-coefficients, sk-hypotheses-sharp.

## sk-cut-sentences
Audit every sentence of the disk note for deletion. The question for each: does a careful reader need it to follow or trust the mathematics, or to know what is new and whom to credit?

Classify each sentence:
- KEEP.
- CUT: a restatement, metacommentary, a statement about the proof, a duplicated justification, text the reader is about to read anyway, or a citation the argument never uses.
- MERGE: two sentences doing one job.
- COMPRESS.

Seeds:
- abstract l.32-33;
- l.55;
- l.60-62;
- l.102-104 (a citation and a direct proof of the same fact; keep one);
- l.150-152;
- the subsection title with "detects";
- duplicated statements across the abstract, the intro and the theorem.

Procedure:
1. Write the maximally cut note as a full candidate `$SK/lanes/sk-cut-sentences/sk-cut-sentences-candidate.tex`. Never write at the repo root.
2. Add back only what a reader needs, and report the final line count.

Deliverable: a proposal quoting every cut verbatim. Peers: sk-cut-structure, sk-exposition.

## sk-cut-structure
Decide which parts of the note should exist at all:
- the theorem's clauses (infinite, f.g., sofic, hyperlinear);
- the Z(G) computation;
- the direct proof that R is simple, versus a citation;
- the Thom, Nekrashevych and Stepanov sentences;
- the word-problem section (l.229-262, about 10% of the note, and its only source of "continuum many");
- the bibliography entries that become unused.

Build three candidate notes in your lane dir, each with a line count:
- (A) the minimal answer: theorem and proof only, no corollary;
- (B) the current scope, cut down;
- (C) the enriched version, with slots for the best verified corollaries from other lanes.

For each candidate, state what the reader gains and what the reader loses.

Deliverable: proposal. Peers: sk-cut-sentences, sk-word-problem, sk-rigidity-ring.

## sk-hypotheses-sharp
Test whether each hypothesis is necessary:
- minimal;
- infinite;
- a subshift (expansive, so the ring is f.g.);
- a finite alphabet;
- F_2, versus F_q or infinite fields;
- n ≥ 3;
- the crossed product by Z, versus other groups;
- EL_n, versus GL_n or E_n.

For each, give a counterexample showing the conclusion fails without it, or show the hypothesis can be dropped. Possible counterexamples:
- non-minimal X gives ideals, hence normal subgroups;
- periodic X gives a matrix ring over Laurent polynomials;
- non-expansive minimal Cantor systems give groups that are not f.g.;
- n = 2 loses (T).

A hypothesis that a one-line example shows to be necessary makes the theorem look canonical. A removable one is arbitrary.

Deliverable: a proposal with at most one sentence per hypothesis in the note, if any. Peers: sk-arbitrary, sk-coefficients, sk-general-actions-a.
