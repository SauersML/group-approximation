# Unique Games: SoS algorithms and integrality gaps, source record (2026-09-12)

Recorded by the literature scout `lit-probability-tcs` at the request of the
fork `ugc-2`, now working the algorithmic side for 2-to-1 games whose pairing
families are admissible designs. Each entry was read from its arXiv abstract
page through an automated fetch on 2026-09-11/12. Only abstract-level
statements are recorded; theorem numbers and exact running times beyond the
abstracts were not checked and must be read from the papers before use in a
proof step.

## 1. Barak--Brandão--Harrow--Kelner--Steurer--Zhou

*Hypercontractivity, Sum-of-Squares Proofs, and their Applications*,
arXiv:1205.4484v3 (v1 21 May 2012, v2 30 Oct 2012, v3 16 Nov 2014). From the
abstract:

> Constant rounds of the "Sum of Squares" semidefinite programing hierarchy
> certify an upper bound on the 2->4 norm of the projector to low-degree
> polynomials over the Boolean cube, as well certify the unsatisfiability of
> the "noisy cube" and "short code" based instances of Unique Games considered
> by prior works.

The abstract also says this improves on the previous bound of exp(poly log n)
rounds for the short-code instances. It does not state the degree.

## 2. Barak--Gopalan--Håstad--Meka--Raghavendra--Steurer

*Making the long code shorter, with applications to the Unique Games
Conjecture*, arXiv:1111.0405v1 (2 Nov 2011). From the abstract:

> An n variable integrality gap for Unique Games that survives
> exp(poly(log log n)) rounds of the SDP + Sherali Adams hierarchy, improving
> on the previously known bound of poly(log log n).

This is SDP + Sherali--Adams, not the Lasserre/SoS hierarchy, and item 1
shows that constant-degree SoS refutes the short-code instances.

## 3. Bafna--Barak--Kothari--Schramm--Steurer (BBKSS)

*Playing Unique Games on Certified Small-Set Expanders*, arXiv:2006.09969v3
(v1 17 Jun 2020, v2 24 Jun 2021, v3 26 Jun 2021). From the abstract:

> We give an algorithm for solving unique games (UG) instances whenever
> low-degree sum-of-squares proofs certify good bounds on the
> small-set-expansion of the underlying constraint graph via a hypercontractive
> inequality. Our algorithm is in fact more versatile, and succeeds even when
> the constraint graph is not a small-set expander as long as the structure of
> non-expanding small sets is (informally speaking) "characterized" by a
> low-degree sum-of-squares proof. Our results are obtained by rounding
> low-entropy solutions -- measured via a new global potential function -- to
> sum-of-squares (SoS) semidefinite programs.

The abstract page's summary lists polynomial-time algorithms, with the
guarantee independent of alphabet size, for UG on the noisy hypercube, the
short code and the Johnson graph.

## 4. Bafna--Minzer

*Solving Unique Games over Globally Hypercontractive Graphs*,
arXiv:2304.07284v1 (14 Apr 2023; CCC 2024). From the abstract:

> We study the complexity of affine Unique-Games (UG) over globally
> hypercontractive graphs, which are graphs that are not small set expanders
> but admit a useful and succinct characterization of all small sets that
> violate the small-set expansion property. This class of graphs includes the
> Johnson and Grassmann graphs, which have played a pivotal role in recent PCP
> constructions for UG, and their generalizations via high-dimensional
> expanders. [...] we are able to deal with instances with arbitrarily small
> (but constant) completeness, and most importantly, their algorithm gets a
> soundness guarantee that degrades with other parameters of the graph (which
> in all PCP constructions grow with the alphabet size), whereas our doesn't.
> Our result suggests that UG is easy on globally hypercontractive graphs, and
> therefore highlights the importance of graphs that lack such a
> characterization in the context of PCP reductions for UG.

The abstract does not state the running time.

## Not located

- Guruswami--Khot--O'Donnell--Popat--Tulsiani--Wu, *SDP gaps for 2-to-1 and
  other Label-Cover variants* (ICALP 2010). The arXiv full-text search for
  "SDP gaps for 2-to-1" returns nothing, and the web search budget for this
  session was exhausted, so its degrees and completeness were not checked.
- No newer SoS/Lasserre integrality gap for Gap-UG, and no algorithm specific
  to rich or randomly paired 2-to-1 instances, was found. Web search was not
  available, so this records a search gap, not evidence that none exist.
