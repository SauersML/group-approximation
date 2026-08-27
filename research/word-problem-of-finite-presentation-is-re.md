---
rg: 2
id: word-problem-of-finite-presentation-is-re
kind: claim
title: The word problem of a finite presentation is recursively enumerable
distinct_from:
  novikov-boone-fp-group-undecidable-word-problem: That is established and says some finitely presented group's word problem is NOT computable; this says the positive instances of any finite presentation's word problem are enumerable, which is compatible with it and is what turns "undecidable" into "not even r.e." on the other side.
  markov-post-undecidable-monoid-word-problem: That is the monoid statement and is about undecidability; this is an enumerability statement about groups, and neither implies the other.
  literal-word-problem-solvable: That is a DECIDABILITY statement about one specific group, the manuscript's E, proved by an explicit algorithm; this is enumerability of the positive instances for an arbitrary finite presentation, which is strictly weaker per presentation and quantified over all of them.
artifacts:
  - GroupApproximation/Computability/WordProblemRE.lean
  - GroupApproximation/Computability/AdianRabinWordProblem.lean
  - GroupApproximation/Computability/PresentationCodes.lean
---

ESTABLISHED (2026-08-17), `WordProblemRE.rePred_wordProblemPred`.  For a coded
finite presentation `c` and a coded word `w`,

    REPred (fun x : PresentationCode x List (N x Bool) => WordProblem x.1 x.2).

Item **D2** of the cost table in [[adian-rabin-transform-for-mf]] -- estimated
300--600 lines, and the one genuinely separable piece of that claim.
Unconditional, no literature input; axiom closure `[propext, Classical.choice,
Quot.sound]`.  The route is
[[word-problem-of-finite-presentation-is-re-proof]].

## The mathematics that was already done

`Computability/AdianRabinWordProblem` proves the characterization the
enumerability rests on, and does it in the awkward direction that matters:

* `mem_normalClosure_iff` -- an element lies in the normal closure of `s`
  exactly when it is a finite product of conjugates of elements of `s` and
  their inverses.  Mathlib has the analogue for `Submonoid` and `Subring` but
  not for `Subgroup`, so `exists_list_of_mem_closure` is proved there from
  `Subgroup.closure_induction`;
* `RawCertificate = List (List (N x Bool) x List (N x Bool) x Bool)` -- a
  `Primcodable` certificate carrying no dependent data;
* `wordProblem_iff_exists_rawCertificate` and its packaged form
  `wordProblemPred_iff` -- a coded word dies in the coded group exactly when
  some raw certificate decodes to it.

Soundness is unconditional by design: a relator word the code does not list
decodes to `1` rather than to garbage, so a search over *all* certificates can
only ever produce genuine positive instances.

## What remained was computability, and the obstruction was a dependent type

`rawValue c cert` lands in `FreeGroup (Fin (genCount c))`, whose *type depends
on the code*.  Equality there is decidable, but a search space a partial
recursive function ranges over must be `Primcodable`, and a dependent family is
not.  So the certificate equation had to be re-expressed on code-independent
raw data before any computability lemma applied — which is what
`Computability/WordProblemRE` does, in exactly the three steps below:

1. `certWord` builds, by list surgery alone, a raw word the code reads as the
   product of conjugates a certificate names (`wordOf_certWord`).  The element
   of the dependent type is never formed, so nothing has to be reduced inside
   `FreeGroup (Fin n)`;
2. `wordOf_testWord_eq_one_iff` restates the matrix of `wordProblemPred_iff` as
   one equation between raw words, so `searchCheck` is a `Bool`-valued test on
   the `Primcodable` type `(PresentationCode x List (N x Bool)) x
   RawCertificate` and `wordProblemPred_iff_exists` is the resulting
   existential;
3. `primrec_certWord`, `primrec_searchCheck` and `computable_searchCheck` are
   the tedious half: `Primrec` plumbing for the fold that decodes a
   certificate.

## The bridge used, and the one avoided

Mathlib's pinned copy calls the notion **`REPred`**, not `RePred`
(`Mathlib/Computability/RE.lean`).  The finish is `rePred_exists_eq_true`,
which is

    Partrec.dom_re : Partrec f -> REPred fun a => (f a).Dom

applied to `fun x => (Nat.rfind fun n => Part.some (decide (matrix x n))).map
fun _ => ()`, whose domain is exactly the set of `x` admitting a certificate,
then `REPred.of_eq` against `wordProblemPred_iff_exists`.

`Computable.find` in the same file looks like the right tool and is not: it
requires `∀ x, ∃ n, P x n`, a *total* search, and the whole point here is that
the search diverges on the negative instances.

## What it buys

Only the second assertion of the manuscript's undecidability corollary --
"not even recursively enumerable" -- and nothing else in the corpus depends on
it.  Post's theorem needs enumerability of the positive side *and*
undecidability, so it is this claim together with
[[uniform-word-problem-on-presentation-codes-undecidable]] that makes
`WordProblemRE.not_rePred_compl_wordProblemPred` and
`WordProblemRE.operatorMF_negative_side_not_re` unconditional.  That is why it
was worth roughly 5% of [[adian-rabin-transform-for-mf]] and was done
independently of [[rabin-chain-effective-collapse-dichotomy]], which was read
as the critical path once
[[novikov-boone-fp-group-undecidable-word-problem]] closed.
