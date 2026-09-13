# Guba Question 1: credit and novelty check (2026-09-12)

Claim: `thompson-f-one-minus-x1-is-ore-with-every-element` (4f3e5243a, review-swarm4 §33 PASS with
bounded novelty). The question is arXiv:2201.02308 Question 1, which is also Question 3.20 of the survey
arXiv:2305.07113v4: is it true that for every `b` in `K[F]`, `(1 - x_1)u = bv` has a nonzero solution?

## Verdict

No prior answer was found.
- **The record §33 could not read.** It is T. Nishinaka's 2022 RIMS Kôkyûroku note. It answers neither
  Question 1 nor the rescaled-binomial generalization
  (`thompson-f-rescaled-x0-binomials-have-common-multiples`).
- **Last statement by Guba.** The JGCC survey (2023-10-19) still lists the question as open.
- **Later work.** No searched source addresses it after that date.
- **Consequence for the claim.** It needs no `## Prior work` note. Its novelty bullet now points here.

## The record §33 could not read

T. Nishinaka (University of Hyogo), *R. Thompson's group F and its group algebras*, RIMS Kôkyûroku 2229
(2022), 103–110.
- **Workshop.** "Logic, Algebraic system, Language and Related Areas in Computer Science", RIMS,
  2022-02-16 to 02-18.
- **Identifiers.** Semantic Scholar CorpusId 275143141; KU repository handle 2433/279750.
- **PDF.** https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2229-13.pdf

All 8 pages were read.
- **§1–2.** Background, then Kielak's theorem: if `K[G]` is a domain, `G` is amenable iff `K[G]` is Ore.
  Then a restatement of Guba's results as Theorem 2.2:
  - linear `A, B` in `K[M]` have a common multiple;
  - so do quadratic forms in `x_0, x_1, x_2`;
  - `1 - x_0` has a common multiple with every `B` in `K[F]`.

  The section ends: a non-Ore pair "need[s] to be of somewhat large degree".
- **§3.** If `A = a_1 + … + a_m` and `B = b_1 + … + b_n` have a common multiple, a DSR-graph argument
  gives a relation `w_1 ⋯ w_k = 1` among the quotients `a_i a_(i+1)^-1`, `b_j b_(j+1)^-1`, subject to a
  condition (Q).
  - Proposition 3.1: if some `a_i, b_j` admit no such relation, `F` is non-amenable.
  - One trial example with three-term `A, B`.
- **Abstract.** "Unfortunately we have not been able to reached the answer."

It never mentions `1 - x_1`, Question 1, or binomials `1 + λg`.

## Other sources read or screened

**Guba's own later work** (arxiv.org author search "Guba, V", and Crossref).
- arXiv:2305.07113 (JGCC 15:1, 2023-10-19). The TeX source was checked: the section "Equations in group
  rings and their systems" states the question and says "we do not know whether any equation of the form
  $(1-x_1)u=bv$ has a nontrivial solution."
- arXiv:2304.04322, *On zero-measured subsets of Thompson's group F* (J. Algebra, 2026). Measures of a
  7-part partition of `F`. The abstract has no group-ring content.
- arXiv:2210.12304, *Cayley graphs of R. Thompson's group F: new estimates for the density* (J. Comb.
  Algebra, 2025). Densities only, by the Crossref abstract.
- arXiv:2112.09812 (IJAC 2022) and *R. Thompson's group F and the amenability problem* (Uspekhi 2022,
  10.4213/rm10040). Both are superseded by the 2023 survey.
- arXiv:2308.01092 and arXiv:2609.10640 are physics papers by Vyacheslav O. Guba, a different author.

**Citing records** (Semantic Scholar graph API).
- **arXiv:2201.02308 and its journal version** (Comm. Algebra 2022, 10.1080/00927872.2022.2082461):
  - the survey;
  - Nishinaka 2022.
- **Guba, *On the Ore condition for the group ring of R. Thompson's group F*** (Comm. Algebra 2021,
  10.1080/00927872.2021.1927068):
  - the survey, both 2022 Guba papers, and Nishinaka 2022;
  - Nishinaka, *On group algebras of R. Thompson's group F*, Kôkyûroku 2193 (workshop 2021-02-17 to 19,
    before the question);
  - *On hypernearring of quotients* (Comm. Algebra 2023), which cites Guba for Ore conditions in general;
  - Dvurečenskij–Fuchs–Zahiri, *Non-commutative Bézout domains and pseudo MV-algebras* (JMAA 2025). It
    is not on arXiv, and no abstract or citation context was available, so it was screened by title and
    venue only.
- **Guba, Semigroup Forum 2021** (10.1007/s00233-021-10173-2):
  - *Green's relations and left amenable semigroups* (Canad. Math. Bull. 2025);
  - *Amenability of semigroups and common multiples in ℓ^1_+* (2021);
  - the survey, and both Nishinaka notes.
- **The survey:** only V. Shpilrain, *Complexity of some algorithmic problems in groups: a survey*,
  arXiv:2401.09218.
- **OpenCitations v2** returned empty lists for the survey DOI and for 10.48550/arXiv.2201.02308.

**RIMS Kôkyûroku.**
- **Scan.** The contents pages of volumes 2193–2354 were scanned byte-wise for Thompson, Guba, "Ore
  condition", "Ore domain" and "amenab".
  - 2354 is the latest volume; 2355–2362 return 404.
  - Controls: 2193-15 and 2229-13 both matched. A first pass with the shell `grep` wrapper matched
    nothing, including the controls, so it was discarded.
- **2265-02.** B. B. Solie, *Some questions on primitivity and Thompson's group* (workshop 2023-02, dated
  2023-05-17). All 3 pages were read. It proves the FC-center of `F` is trivial, and asks whether
  primitivity of `RG` has an `R`-linear cellular-automaton characterization. There are no Ore equations.
- **Other hits,** unrelated by title: 2219-03, 2227-05, 2243-12, 2260-09, 2296-07 and 2303-04 (braided
  Thompson divergence, links via `F`, subgroups of `F`, Golden–Thompson, Thompson-like divergence,
  Kirby–Thompson).
- **Nishinaka's series.** In the 2023 (2265) and 2024 (2291) volumes, Nishinaka appears only as
  organizer.

**arXiv search pages.**
- Abstracts containing "Thompson" and "Ore" gave 8 results:
  - Guba's three Ore papers;
  - five papers where "Ore" means Ore categories or semigroup C*-algebras (forest-skein groups,
    Thompson-like groups from Ore categories, and similar).
- Abstracts containing "group ring" and "Thompson" gave 11 results. The only one after 2023 is F. Flores,
  arXiv:2607.28316: primitivity of group rings of mixed-identity-free groups with free subgroups, which
  does not apply to `F`.

**Crossref.** The query "Thompson group F Ore condition group ring", restricted to works published since
2022-01-01, returned 25 rows. Only Guba 2022 is relevant.

## Unavailable

- **Blocked services:**
  - MathSciNet was not tried.
  - zbMATH: 403 and socket hang-ups.
  - Google Scholar and DuckDuckGo: CAPTCHA.
  - OpenAlex: domain not verifiable.
  - ScienceDirect: 403.
- **arXiv export API:** empty bodies all day, so the arxiv.org search pages were used instead.
- **WebSearch:** the session quota was exhausted.
- **Out of reach by this method:** a paper that answers the question without citing any of Guba's
  2021–2023 papers.

## Bearing on review-swarm4 §33

§33 asked that priority not be claimed until the unread citing record had been read. It has now been read
(Nishinaka 2022, above), and it contains no answer.
