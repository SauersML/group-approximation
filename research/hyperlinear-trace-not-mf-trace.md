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

Read from the **LaTeX source** of arXiv:2508.00125, *Homotopy lifting,
asymptotic homomorphisms, and traces*, in the preliminaries immediately after
the four trace classes are defined:

> "Clearly every quasidiagonal trace is amenable and every MF-trace is
> hyperlinear.  Whether the converse implications hold is an open problem."

and from its introduction: "Another open problem is whether every hyperlinear
trace is MF."  That paper's **v5 was uploaded 2026-07-31**, and it carries "all
hyperlinear traces on `B` are MF" as a *hypothesis* of its theorems rather than
a fact — Corollary `BNuclear` concludes it only for algebras homotopy dominated
by a nuclear `B` with that property.  Seventeen days before this claim was
written, and the best available timestamp for the problem being open.

**Cite 2508.00125 for the open-status sentence.**  An earlier revision of this
node attributed it to arXiv:2507.22783v3 (*Sections and cones*) on the strength
of a fetch summary; that attribution was never confirmed against a source and
two fetches of the same URL disagreed about remark numbering.  The companion
relationship is real — 2508.00125 cites *Sections and cones* for "any
hyperlinear trace on any cone C-star algebra is MF" — so the sentence may
appear in both, but only one of them has been read.

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

## Formalization boundary, as of 2026-08-17

**The not-MF half is done, in Shulman's own definition.**
`Analysis/ShulmanTraceClasses.IsMFTrace` transcribes it verbatim,
`Sofic/ShulmanMFTraceBridge.isOperatorMF_of_isMFTrace_canonicalMaximal`
carries it to operator MF for the group, and
`LiteralTraceConsequence.markedGroup_canonicalMaximalTrace_not_isMFTrace`
composes it at the literal group.  Printed as `cor:mftrace`, badged, and
hypothesis-free: the manuscript's zero-input and unconditionality gates both
pass with it in place.  See [[regular-character-not-mf-trace]].

`Analysis/ShulmanTraceNorms.lean` now also has `IsHyperlinearTrace` — the same
five clauses with the three defect norms changed to `||.||_2` — together with
`isHyperlinearTrace_of_isMFTrace`, which is the check that the two definitions
are parameterized consistently.

**What remains is the hyperlinear half for the specific trace `tau_E`.**  Three
named obligations, all in `Analysis/TracialMatrixUltraproduct.lean` or
downstream of it: a `CStarAlgebra` instance on the quotient (without it the
lift out of `C^*(E)` cannot fire), the ultratrace bundled as a **continuous**
functional (`canonicalMaximalTrace_eq_of_generator` takes `->L[C] C`), and the
quotient staying in `Type 0` so the lift's universe constraint is met.  None of
the three is a mathematical obstacle; all three are the kind of thing that
compiles in isolation and fails to compose.

## The premise is not hypothetical here, and that is the whole point

An external referee-style read of the argument (2026-08-17) confirmed both
halves as standard and correct, and then added the caveat that would be right
for anyone else: *"No sofic non-MF group is known to exist ... this argument
shows that IF a sofic non-MF group exists, its canonical trace is hyperlinear
but not MF — it does not yet produce an actual example."*

**That caveat does not apply to this development.**  The sofic non-MF group is
Theorem A together with Theorem D, both machine-checked and both unconditional:

- `LiteralSoficAssembly.markedGroup_isSofic` — docstring reads "Unconditional:
  no hypothesis, no literature input";
- `LiteralSoficAssembly.markedGroup_finitelyPresented_sofic_nonMF` — finitely
  presented, sofic, and not `IsCDEOperatorMF`, in one theorem.

So the conditional is discharged at its own premise.  Anyone reading the trace
argument in isolation will reach for that caveat, which is a reason to state
the dependence on Theorem A/D explicitly at the point of use rather than leave
a reader to supply the objection themselves.

**The reverse implication is not available and should not be suggested.**  `E`
being an MF *group* would not obviously make `tau_E` an MF *trace*: an
operator-norm embedding of the group need not recover the canonical trace.  The
conditional runs one way only.

## Two refinements from the same read, worth keeping

**Where the trace condition earns its keep.**  In the MF half, injectivity of
`g -> Phi(u_g) + (1 - p)` comes from the *trace* clause, not from `Phi` being a
`*`-homomorphism.  A bare `*`-homomorphism into `prod M/(+)M` would not give
injectivity on the group at all.  Worth one sentence in the paper, because it
tells the reader why the definition carries a trace clause.

**Keep the filters consistent, and note the Lean does.**  The printed proof
quotients by `(+)_(2,omega)` in the hyperlinear half and by the `c_0`-type
`(+) M_(k_n)` in the MF half.  Both conventions are fine, but the displayed
limits in the contradiction must be taken along the *same* filter as the
quotient they belong to.  Shulman's two definitions both use ordinary
`n -> infinity` limits; the ultrafilter enters only through her reformulation
remark.  Our Lean predicates are both at `atTop`, and the formal hyperlinear
route is built at `atTop` precisely so that no filter conversion is ever
needed — an independent confirmation of that design choice.

Also from the same read, and useful for the introduction: each `M_(d_n)`
embeds trace-preservingly into `R`, so the tracial ultraproduct embeds into
`R^omega`, which is what ties this to Connes-embeddability in the vocabulary
the operator-algebra reader already has.

## Why the region was empty, and the novelty sentence that says so

The best sentence available for the introduction is not "Shulman asked this
question".  It is the one that explains why nobody had answered it.

Schafhauser, arXiv:2306.02498, records the state of the art immediately before
his Proposition 2.2: **the previously known non-MF traces are those arising
from the failure of the Connes embedding problem, and those do not factor
through `R^omega`** — so they are not hyperlinear at all.  Every known non-MF
trace was outside the hyperlinear class for the same reason.  That is exactly
why the separation had no witness, and it is the contrast our example lands in.

As a diagram of trace classes on a C-star algebra:

```text
all traces  ⊋  hyperlinear traces  ⊇  MF traces
              ↑                      ↑
        MIP*=RE makes           this one had no known
        this strict             strict instance
```

MIP*=RE supplies traces outside the hyperlinear class; ours is the first inside
it and outside MF.  Stated structurally rather than as one odd trace:
`T_MF(A) ⊊ T_hyp(A)` for `A = C^*(E)`.

**The direction of the surrounding literature makes the contrast sharper, not
weaker.**  Substantial recent work runs the *other* way — proving the two
classes coincide for ever larger families: Rainone--Schafhauser for broad
classes of crossed products, Shulman for cones and suspensions
(arXiv:2507.22783), and further positive cases under Hilbert--Schmidt
stability and homotopy domination (arXiv:2508.00125, arXiv:2603.13564).  So the
honest framing is: equality was being established family by family, the general
question was posed, and it fails.

## Citation lineage, for whoever writes the introduction

Two historical lines meet here:

```text
Brown (Mem. AMS 184(865), 2006)  ->  Rainone--Schafhauser (Adv. Math. 347)
  ->  Shulman's question  ->  this separation

Radulescu / Elek--Szabo  ->  E is sofic  ->  tau_E is hyperlinear
```

**Attribution wrinkle, do not get this wrong.**  Schafhauser writes that the MF
trace notion was introduced in Rainone--Schafhauser.  But Hadwin--Li--Li--Shen,
arXiv:1109.0673 (2011), is titled *MF-traces and a lower bound for the
topological free entropy dimension* and its abstract says it introduces a
notion called "MF-trace".  So **never write "MF traces were introduced by
Rainone--Schafhauser" unqualified.**  Write "the operator-norm approximation
notion of an MF trace developed by Rainone--Schafhauser and used by Schafhauser
and Shulman", and put Hadwin--Li--Li--Shen in a terminology footnote if at all.
Do not use it as the *definition* citation without first checking that their
microstate formulation agrees with the class in use here.

**The manuscript bibliography currently has neither.**  As of 2026-08-17 it
carries exactly two of the relevant keys — `Schafhauser` (2306.02498) and
`Shulman` (2603.13564, the amalgamated-free-products paper).  Missing and worth
adding: Shulman 2508.00125 (the definitions and the open problem — this is the
primary citation), Shulman 2507.22783 (cones and suspensions, the positive
contrast), Rainone--Schafhauser 1601.06090, Schafhauser 1705.06555, Brown
math/0304009, and optionally Musat--Rordam 1903.10182 and Radulescu
math/0004172.

**One convention sentence is mandatory.**  Schafhauser's Definition 1.1 group
notion is a priori *stronger* than Carrion--Dadarlat--Eckhardt's, adding
approximation of the regular character and of the reduced norm.  Our group-MF
convention is CDE throughout.  Without that sentence a careful reader meets his
Proposition 2.2 (`G` MF iff `tau_G` MF) and asks why we reprove a direction; the
answer is that his left-hand side is the stronger property and our full-`C^*(G)`
recognition theorem gives the implication for the weaker one.

## Why it is a contrast rather than a contradiction

That paper's Theorem 30 — "all hyperlinear traces on cones are MF" — is
exactly a contrast: a cone is homotopically trivial and its traces are soft,
whereas the obstruction here is the property-`(T)` compression rigidity that
makes `E` non-MF while `E` is sofic.

Consequence for this repository: the non-MF theorem has a trace-level
corollary in the operator-algebra literature's own vocabulary, independent of
the group formulation.
