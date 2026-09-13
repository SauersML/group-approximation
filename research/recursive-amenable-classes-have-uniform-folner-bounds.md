---
rg: 2
id: recursive-amenable-classes-have-uniform-folner-bounds
kind: claim
title: Recursively presented amenable groups have subrecursive Følner functions, uniformly over every recursively enumerable class of presentations
distinct_from:
  amenability-two-generator-recursive-is-pi2-complete: that places amenability of recursive presentations in the arithmetical hierarchy through Kesten's return probabilities; this bounds the size of Følner sets of such groups, uniformly over any c.e. class of amenable presentations.
  thompson-f-folner-function-exceeds-every-tower: that is a lower bound for one finitely presented group, vacuous unless it is amenable; this is a recursive upper bound for every amenable recursively presented group, and a uniform one for every c.e. class of them.
---

**ESTABLISHED (literature import).** M. Cavaleri, *Følner functions and the
generic Word Problem for finitely generated amenable groups*, J. Algebra (2018),
arXiv:1703.04133v2 (3 Jul 2018). Pages 1--9 of the PDF were read on 2026-09-12.

**Theorem 3.1**, verbatim: "Suppose that Γ is recursively presentable. Then the
following are equivalent: (i) Γ is amenable; (ii) Γ has subrecursive Følner
function; (iii) there exists an algorithm with INPUT: n ∈ N, OUTPUT: F ⊂ F_X
finite, such that π_Γ(F) contains an n-Følner set; (iv) Γ has computable Reiter
functions."

**Corollary 3.4**, verbatim: "For every n ∈ N fixed, the set of finitely
generated recursive presentations of groups admitting n-Følner sets is
recursively enumerable." The same page records, as Remark 3.5, that "for every
n ∈ N fixed the property of admitting n-Følner sets is a presentation property,
not a group property." The consumer is
`uniform-folner-gap-switches-have-sigma1-amenable-locus`.

**Corollary 3.6**, verbatim: "For every recursively enumerable class C of
finitely generated recursive presentations of amenable groups there exists a
recursive function U_C such that for every P_i ∈ C: F_(Γ_i,X_i) ≤ U_C
eventually."

**Definitions** (same source):
- `Ω` is an `n`-Følner set when `|Ω \ xΩ| / |Ω| <= 1/n` for every generator `x`;
- `F_(Γ,X)(n)` is the least size of an `n`-Følner set;
- a function is *subrecursive* when it has a recursive upper bound.

**Gromov's question.** Cavaleri's introduction quotes Gromov's question (d),
cited as "[15, p.578, Gromov]" (that bibliography entry was not read): "Is
there an universal bound on the asymptotic growth of the Følner functions of
finitely presented amenable groups by a recursive (primitively recursive?)
function? (Maybe there is such a bound in every given recursive class of
presentations?). Or, at another extreme, are there finitely presented amenable
groups with so fast growing Følner function, such that their amenability is
unprovable in Arithmetic?"

Cavaleri writes that "the behaviour for finitely presented groups remained
open", and presents the two statements above (his Theorem A) as a partial
answer. They settle the parenthetical form, one c.e. class at a time. The
universal form over all finitely presented amenable groups is the open claim
`folner-functions-of-fp-amenable-groups-have-no-recursive-bound`, stated there
as its negation.

DERIVATION
recursive-amenable-classes-have-uniform-folner-bounds-citation
