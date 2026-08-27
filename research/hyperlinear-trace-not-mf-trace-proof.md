---
rg: 2
id: hyperlinear-trace-not-mf-trace-proof
kind: route
title: Soficity gives the hyperlinear trace, the non-MF theorem forbids the MF one
target: hyperlinear-trace-not-mf-trace
requires: [sofic-non-mf-witness, regular-character-mf-trace-implies-group-mf]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Endpoint/NonMFImpact.lean
  - GroupApproximation/Sofic/LiteralTraceConsequence.lean
---

## Why sufficient

Let `G` be sofic and not operator MF — either the literal finitely presented
`E` of `literal-group-sofic` and `literal-group-fails-mf-conventions`, or the
finitely generated Clifford witness `W` of `sofic-non-mf-witness`.  Put
`A = C^*(G)`, separable and unital, and let `tau` be its canonical trace.

### `tau` is hyperlinear — the short route

`G` is sofic, hence hyperlinear, hence `L(G)` embeds in `R^omega` in a
trace-preserving way.  Compose

    A = C^*(G)  ->  L(G)  ->  R^omega

and the canonical trace is carried to `tr_omega`.  A trace that factors
through a tracial matricial ultraproduct *is* a hyperlinear trace, so this is
the whole argument.

**Source check DISCHARGED against the LaTeX source, 2026-08-17.**  The
characterization is the remark `hypTraceReformulation` in the preliminaries of
**arXiv:2508.00125**, *Homotopy lifting, asymptotic homomorphisms, and traces*:

> "Equivalently, one can say that `tau` is hyperlinear if `tau = tr o f`, for
> some `*`-homomorphism `f : A -> prod M_(k_n)/(+)_2 M_(k_n)`, for some
> `k_n`'s, where `(+)_2 M_(k_n)` is the ideal of all sequences that converge to
> zero in the 2-norm and `tr` is a trace on `prod M_(k_n)/(+)_2 M_(k_n)`
> defined by the formula `tr([(T_n)]) = lim_(n->omega) tr T_n`, where `omega`
> is some non-trivial ultrafilter on `N`."

The remark continues with the `(+)_(2,omega)` ideal — the tracial ultraproduct,
"a von Neumann algebra with the faithful trace" — states the iff for that
version too, and adds that one may replace it by `R^omega`.  Three admissible
targets; the `(+)_2` one puts no ultrafilter in the ideal and is the cheapest
to build.

**CITATION CORRECTION.**  An earlier revision of this node placed the remark in
arXiv:2507.22783v3 (*Sections and cones*) as "Remark 1".  That came from a
fetch summary, not from a source read, and it is not supported.  The verbatim
text above is from 2508.00125.  The two papers are companions and both discuss
these trace classes, so the sentence may well appear in both — but **cite
2508.00125 for it**, which is the one we have read.  Two independent fetches of
the 2507.22783 HTML also disagreed with each other about remark numbering,
which is reason enough never to take a remark number from a fetch.

So this route stands on the author's own equivalence and the longer route
below is a fallback, not the primary.

### The lifting step needs no Bartle--Graves, and no citation

**Superseded, 2026-08-17, under the standing directive that nothing may be
conditional and nothing may enter as a literature input.**  The route below
uses Bartle--Graves to produce a continuous section, and an earlier revision of
this node was willing to take Shulman's equivalence between the sequential and
factorized definitions on citation.  Neither is needed and neither is allowed.

The reason is in a sentence Shulman **commented out** of her own source
(arXiv:2508.00125), which is the proof of the equivalence:

> "Indeed the homomorphism `f : A -> prod M_n/(+) M_n` can be lifted to a
> linear (not necessarily continuous) map by sending any element of a Hamel
> basis of `A` to any its preimage and extending it linearly to `A`.  Then
> `phi` can be defined as the `n`-th coordinate of this lift."

Her maps are **not required to be continuous**, which is exactly why no
section theorem is needed.  Take a Hamel basis of `A`, choose any preimage in
the bounded product of `f(b)` for each basis vector, extend linearly to get
`Phi : A ->L[C] prod M_(k_n)` -- linear, not continuous -- with `q . Phi = f`,
and set `phi_n a := (Phi a) n`.  Then the linearity defect is **exactly zero**
rather than asymptotically zero; the multiplicativity and star defects lie in
the ideal, which is precisely `||.||_2 -> 0`; and the uniform bound is free
because `Phi` lands in the *bounded* product.  In Lean this is `Basis.constr`
plus `Classical.choice`, both already inside the permitted axiom set.

**One real gap, named rather than hidden.**  `tr` on the quotient is an
*ultralimit*, while the sequential definition asks for an ordinary
`lim_(n->infinity)`.  Closing that needs a subsequence extraction against a
countable dense subalgebra -- available, since
`maximalGroupCStar_separableSpace` is proved.  Until that extraction is
written, the sequential trace clause is the one step of this route not in
hand, and it must be stated as such and not absorbed into a citation.

### `tau` is hyperlinear — the Bartle--Graves route, retained only as history

Soficity gives unitaries `u_n : G -> U(k_n)` with
`||u_n(g)u_n(h)-u_n(gh)||_2 -> 0` and `tr(u_n(g)) -> 0` for `g != 1`, so the
induced map into the unitary group of the tracial ultraproduct
`R^omega = prod_n M_(k_n)/J`, `J = {x : lim_omega ||x_n||_2 = 0}`, is a group
homomorphism.  By the universal property of the **full** group C-star
algebra it extends to a `*`-homomorphism `pi : A -> R^omega`, and
`tr_omega circ pi` agrees with `tau` on the group elements, hence on their
dense span, hence everywhere.

Now lift.  By the Bartle--Graves theorem — in the sharpened form that opens
arXiv:2507.22783, a continuous section of norm exactly one — the quotient
map `prod_n M_(k_n) -> R^omega` admits a continuous section `s` of norm one.
Put `phi = s circ pi` and let `phi_n` be its coordinates.  For all `a,b` and
scalars, the elements

```text
phi(ab)-phi(a)phi(b),   phi(la+mb)-l phi(a)-m phi(b),
phi(a^*)-phi(a)^*
```

map to `0` in `R^omega`, hence lie in `J`, so their coordinates are
`||.||_2`-null along `omega`; also `sup_n||phi_n(a)|| <= ||a||` and
`lim_omega tr(phi_n(a)) = tau(a)`.  Since `A` is separable, apply these
countably many conditions to a countable dense `Q(i)`-subalgebra and extract
a subsequence along which all of them hold as ordinary limits; continuity of
`s` and the uniform bound propagate them from the dense subalgebra to all of
`A`.  Along that subsequence `phi_n` witnesses that `tau` is a hyperlinear
trace.

A third route avoids both: `tau` is an amenable trace because `L(G)` is Connes
embeddable, and amenable traces are hyperlinear by inspection of the
definitions.  That one replaces the section by Brown's characterization of
amenable traces.

### `tau` is not MF

If it were, `regular-character-mf-trace-implies-group-mf` would make `G`
operator MF, contradicting the non-MF theorem.  End proof.

For `G = E` the *finite-test-set* form of this half is now machine-checked and
composed: [[regular-character-not-mf-trace]].

## Trust surface

Four inputs, in decreasing order of what a reviewer should check.

1. **The definitional comparison, and it is the real one.**  The Lean predicate
   `IsMFRegularCharacter` is a finite-test-set condition on the group
   unitaries; Shulman's MF-trace condition is asymptotic and quantifies over
   every element of `A`.  Nothing in the tree relates them.  Every claim that
   the machine-checked half *is* the trace-level half passes through this
   comparison, and it is unproved in both directions.
2. `sofic-non-mf-witness`, or for the finitely presented witness
   `literal-group-sofic` + `literal-group-fails-mf-conventions` — this
   repository's own theorems, Lean-checked, frozen pending specialist review.
   Everything here inherits that status.
3. The definitions of hyperlinear trace and MF trace, quoted verbatim from
   arXiv:2507.22783v3 in `regular-character-mf-trace-implies-group-mf`.  They
   impose no positivity, only pointwise-bounded asymptotic linearity,
   multiplicativity and `*`-preservation; the argument uses exactly those.
4. Bartle--Graves, used only in the fallback route, and only to produce a
   continuous section.  Any continuous section of any norm serves; the norm-one
   refinement is not needed.

## The two definitions differ only in the norm

Read from arXiv:2507.22783v3: the hyperlinear and MF trace definitions are the
same sentence with a different norm on the multiplicativity defect —
`||.||_2` (normalized Hilbert--Schmidt) for hyperlinear, `||.||` (operator)
for MF.  That is why "every MF trace is hyperlinear" is immediate and why the
converse is the hard direction: it is the same rank-visibility gap that makes
`mf-implies-hyperlinear` open at the group level, transposed to traces.

## The external cross-check, and a correction to it

Schafhauser arXiv:2306.02498 Proposition 2.2 looks like a shortcut around the
whole "not MF" half.  On 2026-08-17 this node recorded that it is not, because
his Definition 2.1 asks for exactly linear, exactly self-adjoint maps where
Shulman asks only for asymptotically linear ones.

**That objection is answered by Shulman herself, and the reference is not the
one we guessed.**  Read from the LaTeX source of arXiv:2508.00125:

> "In the definition of an MF-trace one can additionally require the maps
> `phi_n` to be `*`-linear \cite[Prop. 2.2]{RainoneSch}.  The same argument
> works also for hyperlinear traces."

`RainoneSch` is **Rainone--Schafhauser, *Crossed products of nuclear C-star
algebras and their traces*, Adv. Math. 347 (2019) 105--149** — not
Schafhauser's amalgamated-free-products paper arXiv:2306.02498, which is where
a forwarded analysis put the Proposition 2.2 we were arguing about.  Two
different papers, both by Schafhauser with different coauthors, both with a
load-bearing Proposition 2.2; the collision is easy to make and was made.

Consequences: the `*`-linear strengthening is free and applies to BOTH trace
classes, so the entry arrow the earlier objection called missing exists.  The
objection is withdrawn.  We still print our own corner-and-polar route, because
that is what makes the result depend on our mathematics rather than a citation.

Either way we print our own route: the corner-and-polar argument is the thing
that makes the result depend on our mathematics rather than on a citation.
His Definition 1.1 group notion being "(a priori) quite a bit stronger" than
Carrion--Dadarlat--Eckhardt is verified verbatim and costs nothing.
