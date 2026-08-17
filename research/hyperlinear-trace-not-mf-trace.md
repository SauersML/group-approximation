---
rg: 2
id: hyperlinear-trace-not-mf-trace
kind: claim
title: A hyperlinear trace that is not an MF trace
distinct_from:
  hyperlinear-not-imply-mf: That established claim is the group-level separation; this is its trace-level consequence for a single trace on a single C-star algebra, and it answers a question posed in the literature.
  mf-hyperlinear-radical-divergence: That claim separates two radicals elementwise inside one group; this one separates two classes of traces on a C-star algebra.
  regular-character-not-mf-trace: That is the Lean-exact statement, a finite-test-set condition on the group unitaries of one explicit group; this is the statement in Shulman's own vocabulary, an asymptotic condition on every element of a C-star algebra, and the step from that one to this one is the definitional comparison recorded below.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Endpoint/NonMFImpact.lean
  - GroupApproximation/Sofic/MFTraceRecognition.lean
---

There is a separable unital C-star algebra carrying a trace which is
hyperlinear but not MF, in the senses of Shulman, *Sections and cones*,
arXiv:2507.22783v3.  Take `A = C^*(E)` for the literal finitely presented
group `E`, with `tau` its canonical trace.

This answers, negatively, one of the two converse implications that paper
records as open.  Verbatim: "Clearly every quasidiagonal trace is amenable and
every MF-trace is hyperlinear.  Whether the converse implications hold is an
open problem."  The present claim refutes `hyperlinear => MF`.  It says
nothing about `amenable => quasidiagonal`, which involves completely positive
maps and remains open.

## The quote is source-verified, and the problem is current

Re-read from the arXiv full text on 2026-08-17: the sentence is **Remark 2**,
in the Preliminaries section of arXiv:2507.22783v3, where the four trace
classes are defined.  The repository's citation is correct.

Currency has a second, sharper witness.  The same author's companion paper —
*Homotopy lifting, asymptotic homomorphisms, and traces*, arXiv:2508.00125,
**v5 uploaded 2026-07-31** — still carries "all hyperlinear traces on `B` are
MF" as a *hypothesis* of its theorems rather than a fact.  That is seventeen
days before this claim was written, and it is the best available timestamp for
the problem being open.  Any priority sentence should cite v5's date, not this
repository's v3 reference.

## Which witness to use

Either of two groups serves, and the finitely presented one is now the better
choice:

- `E`, the literal forty-one-relator group.  `LiteralSoficAssembly.markedGroup_isSofic`
  is unconditional — "no hypothesis, no literature input" — and
  `markedGroup_finitelyPresented_sofic_nonMF` gives finitely presented, sofic
  and not CDE-operator-MF in one theorem.  Earlier revisions of this node used
  `W` because soficity of `E` was at that time conditional on the completeness
  of the printed base presentation.  It no longer is.
- `W`, the concrete Clifford witness of `sofic-non-mf-witness`, which is
  finitely generated rather than finitely presented.

## The external cross-check, and the gap in it

Schafhauser, *Finite dimensional approximations of certain amalgamated free
products of groups*, arXiv:2306.02498, offers a shorter-looking route:

- his **Definition 1.1** is an MF group condition which he says verbatim is
  "(a priori) quite a bit *stronger* than the definition of MF group in [6]",
  the Carrion--Dadarlat--Eckhardt one;
- his **Proposition 2.2** ties that group condition to his MF-trace condition
  on the canonical trace of `C^*_lambda(G)`.

Given the entry arrow, the rest is immediate: `E` is not CDE-MF, hence not
Schafhauser-MF, hence `tau_E` is not a Schafhauser-MF trace.

**The entry arrow is the gap.**  Schafhauser's Definition 2.1 asks for a map
`phi : A -> M_d` that is *exactly* linear and *exactly* self-adjoint, with
approximate multiplicativity and trace-correctness.  Shulman asks only for
*asymptotic* linearity and *asymptotic* star-preservation.  Shulman's
condition is therefore formally the weaker one — more traces satisfy it — so

    tau is a Shulman-MF trace  ==>  tau is a Schafhauser-MF trace

is not a definitional identity and has to be proved.  Proposition 2.2 does not
retire the in-house argument; it moves the work from "manufacture unitaries
from non-unitary images" to "rigidify asymptotic linearity into exact
linearity on a separable algebra".  Cite it as a cross-check, print the
comparison, and do not elide it.

## Formalization boundary

The not-MF half is formalized and the hyperlinear half is not; see
[[regular-character-not-mf-trace]] for exactly what the Lean says and what it
does not.

## Why it is a contrast rather than a contradiction

That paper's Theorem 30 — "all hyperlinear traces on cones are MF" — is
exactly a contrast: a cone is homotopically trivial and its traces are soft,
whereas the obstruction here is the property-`(T)` compression rigidity that
makes `E` non-MF while `E` is sofic.

Consequence for this repository: the non-MF theorem has a trace-level
corollary in the operator-algebra literature's own vocabulary, independent of
the group formulation.
