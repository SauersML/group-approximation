# Idea lane nh-small-cancellation (target `non-hyperlinear-group`)

**Date:** 2026-09-13
**Status:** idea file only. Nothing here is established, and no Cairn node was edited.
**Lens:** small cancellation and graphical small cancellation: Gromov monsters,
Olshanskii towers, Osin/Arzhantseva–Delzant constructions.

## Facts used by the kill tests

- **F1.** `local-approximation-properties-are-marked-closed` (ESTABLISHED).
  Hyperlinearity is hereditary, local, and closed in the space of `k`-generated
  marked groups. If `G` fails it, some radius `R` works: every marked group that
  agrees with `G` on words of length `<= R` also fails it (clause 3).
- **F2.** Wise, "Cubulating small cancellation groups" (GAFA 2004), plus Agol's
  theorem. Seen only through search summaries; the primary sources were not
  re-read. Finitely presented classical `C'(1/6)` groups are cocompactly
  cubulated, hence virtually special, hence `Z`-linear and residually finite. The
  same summaries report that `C'(1/6)` quotients, by finitely many relators, of
  free products of virtually compact special groups are virtually special.
- **F3.** Osajda, *Residually finite non-exact groups*, GAFA 28 (2018) 509–517,
  arXiv:1703.03791. Abstract, verbatim: "We construct the first examples of
  residually finite non-exact groups. The construction is based on author's
  earlier construction of groups containing isometrically expanders using a
  graphical small cancellation."
- **F4.** Pestov, *Hyperlinear and sofic groups: a brief guide*, arXiv:0804.3968,
  pp. 21–22, read from the PDF text.
  - "Open question 9.4 (Weiss [79]). Is the free Burnside group of a finite
    exponent n sofic?"
  - "As the free Burnside group of large exponent is a direct limit of word
    hyperbolic groups (see [62], Ch. 6), a negative answer to Question 9.4 would
    in particular imply the existence of a non residually finite word hyperbolic
    group".
- **F5.** Becker–Lubotzky, *Group stability and Property (T)*, arXiv:1809.00632,
  from the search summary of the abstract. An infinite hyperlinear group with (T)
  is not stable with respect to `(U(n), d^HS_n)`. The repo node
  `kazhdan-hyperbolic-b2-group-flexibly-hs-stable` records the same boundary.

## A1. Towers whose stages kill low-dimensional microstates

- **Idea.** Build `F_m = G_0 -> G_1 -> ...`, where
  `G_(n+1) = G_n / <<R_n>>` and `R_n` satisfies small cancellation over the
  hyperbolic group `G_n`. Choose `R_n` to annihilate every unitary microstate of
  dimension `<= f(n)` at scale `eps_n`. Every stage stays hyperlinear, and the
  lacunary hyperbolic limit is meant to fail.
- **What it would prove.** A non-hyperlinear lacunary hyperbolic group.
- **Kill test.** F1, clause 3. The limit `G` is the marked limit of the `G_n`,
  since the normal subgroups increase and balls stabilize. If `G` failed, some
  radius-`R` ball would witness the failure. `G_n` shares that ball for large `n`,
  so `G_n` would fail too, contradicting the assumption that all stages are
  hyperlinear.
- **Verdict: KILLED as stated.** A tower can only ever show what some finite stage
  already shows. The dimension schedule `f(n)` is irrelevant, because
  hyperlinearity does not depend on dimension.

## A2. Encoding a non-approximable pattern in a classical `C'(1/6)` presentation

- **Idea.** Encode a relation pattern that has no approximate unitary solutions,
  and pad the relators until `C'(1/6)` holds. Greendlinger's lemma keeps the
  marked word nontrivial.
- **What it would prove.** An explicit non-hyperlinear hyperbolic presentation.
- **Kill test.** F2. Every finitely presented group of this kind is virtually
  special, hence residually finite, hence hyperlinear, whatever the relators
  encode.
- **Verdict: KILLED** for finite classical `C'(1/6)` presentations over free
  groups, and, per the F2 summary, over free products of virtually compact special
  groups. A small-cancellation mechanism has to leave cubulable classes, as in A4
  and A5.

## A3. Gromov monsters: expanders as a spectral obstruction

- **Idea.** Embed expander sequences, via graphical small cancellation, so that
  the spectral gap obstructs tracial approximation.
- **Kill test (i).** F3. Osajda's groups contain isometrically embedded expanders
  and are residually finite, so sofic and hyperlinear. Expander geometry alone
  never obstructs hyperlinearity.
- **Kill test (ii).** F1. An infinitely presented graphical small cancellation
  group `Q` over finite graphs `Theta_1, Theta_2, ...` is the marked limit of its
  truncations `Q_N`, which use only `Theta_1..Theta_N`. So `Q` fails only if some
  finitely presented truncation fails. Monsters therefore reduce to finitely
  presented hyperbolic groups; I did not re-check hyperbolicity of the truncations
  against a source.
- **Verdict: KILLED as a mechanism.** What remains is the finitely presented
  host question, which is A4.

## A4. Small cancellation over non-cubulable Kazhdan hyperbolic bases

- **Idea.** Take a hyperbolic Kazhdan group `Gamma` with `b_2 >= 1`, for instance
  the repo's certified torsion-free congruence kernel of `GHB(7)`
  (`ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`, `b_2 >= 1380`), and
  form small cancellation quotients `Gamma/<<R>>`. Quotients keep (T), and
  small cancellation over a hyperbolic group keeps hyperbolicity. Kazhdan groups
  admit no unbounded action on a CAT(0) cube complex, so A2's residual-finiteness
  certificate cannot apply. Choose `R` to destroy the structures behind
  flexible-stability failures, such as finite quotients and low-dimensional
  representations, in the spirit of the Kozma–Lubotzky effect recorded in
  `nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md` §5.
- **What it would prove.** Suppose some quotient keeps `b_2 >= 1` and is flexibly
  HS-stable. Then `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity`
  (ESTABLISHED) gives a non-hyperlinear hyperbolic finite central extension,
  through the route `non-hyperlinear-via-hs-stable-kazhdan-hyperbolic`.
- **Kill tests run.**
  - F5 leaves only flexible stability. That is consistent, not fatal.
  - The repo attempt `flexible-hs-stability-passes-to-kazhdan-kernel-quotients`
    covers quotients by Kazhdan normal subgroups. A normal closure of finitely
    many small-cancellation relators need not be Kazhdan, so no transfer in either
    direction is recorded.
  - The class-wide screen `classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan`
    applies. An argument for all small cancellation quotients of all hyperbolic
    Kazhdan groups would reach Belegradek–Osin covers, so the argument must use
    something specific to the chosen relators.
  - Open: whether adding relators keeps `b_2 >= 1`. It depends on asphericity of
    the new presentation complex.
- **Verdict: UNCLEAR, the best host lens.** What is missing is a stability
  mechanism that relators can create. One target: relators forcing every
  normalized-HS almost-representation to almost factor through a finite quotient
  that is injective on vertex groups. I found no source in which small
  cancellation improves HS stability.

## A5. Free Burnside groups through an HS-stable exponent law

- **Idea.** Take `B(m,n)` with `n` large and odd.
  - It is infinite and non-amenable (Adian, as quoted in F4).
  - Every finite quotient factors through the finite restricted Burnside group
    `R(m,n)` (Zelmanov), so it is not residually finite.
  - It is a direct limit of hyperbolic groups (F4).
  - Suppose exponent laws were HS-stable on balls: any unitary tuple with
    `d_HS(w^n, 1)` small for all words of length `<= R` is flexibly close to a
    representation of a finite exponent-`n` group, of order at most `|R(m,n)|`.
    Then approximate models could not separate a ball with more than `|R(m,n)|`
    distinct elements, so `B(m,n)` would be non-hyperlinear.
- **What it would prove.**
  - Non-hyperlinearity, hence non-soficity, of `B(m,n)`, which is a "no" to
    Weiss's Question 9.4.
  - By F4, a hyperbolic group that is not residually finite.
  - By F1, a non-hyperlinear hyperbolic stage.
- **Kill tests run.**
  1. Question 9.4 is still open in F4, so no known sofic or hyperlinear
     approximation of `B(m,n)` refutes the idea.
  2. The repo's `operator-norm-restricted-burnside` works the operator-norm
     corona version. Its Attempt 3 records that normalized-HS approximations of
     periodic groups do not become operator-norm ones. So this HS version is a
     separate statement, not a duplicate.
  3. Hand check, one generator: a unitary with `u^n ≈ 1` in normalized HS rounds
     to an exact exponent-`n` unitary at small HS cost, by moving eigenvalues to
     `n`-th roots of unity. Rounding the generators does not round products,
     though, so the all-words version is the whole difficulty.
  4. Sanity bound: the stability statement would make every f.g. hyperlinear
     group of exponent `n` finite. One web search did not settle whether some
     infinite f.g. sofic or amenable group of bounded exponent is known.
- **Verdict: UNCLEAR, bold.** Next test: find any infinite f.g. hyperlinear group
  of bounded exponent, which would kill A5 outright. If none turns up, test HS
  stability of the exponent law on words of length `<= 2` in small dimensions,
  numerically on MSI.

## Summary

| # | Approach | Verdict |
|---|---|---|
| A1 | Microstate-killing towers | killed (F1) |
| A2 | Finite `C'(1/6)` encodings | killed (F2) |
| A3 | Gromov monsters / expanders | killed as a mechanism (F3, F1) |
| A4 | Small cancellation over Kazhdan hyperbolic bases, feeding the stability route | unclear (best host) |
| A5 | Free Burnside groups and HS-stable exponent laws | unclear (bold) |

Lesson for the lens: by F1, infinite presentations and limits never add
existence power. Small cancellation can only help by producing a finitely
presented, non-cubulable host (A4), or by carrying an exponent law whose
approximate version is rigid (A5).

## Sources

- Osajda, arXiv:1703.03791, abstract: https://arxiv.org/abs/1703.03791
- Pestov, arXiv:0804.3968, pp. 21–22, from the PDF text: https://arxiv.org/pdf/0804.3968
- Becker–Lubotzky, arXiv:1809.00632, from a search summary: https://arxiv.org/abs/1809.00632
- Wise, GAFA 2004, from a search summary: https://link.springer.com/article/10.1007/s00039-004-0454-y
