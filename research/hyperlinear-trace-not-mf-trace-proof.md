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

**Source check owed.**  That last sentence is the load-bearing one and it is
reported rather than verified here: the characterization "hyperlinear trace
iff it factors through a tracial matricial ultraproduct" was attributed to
Shulman's arXiv:2508.00125 in a forwarded analysis and has NOT been read from
the source in this repository.  Before this route is used in print, read
arXiv:2508.00125v5 and confirm the characterization and its exact hypotheses
(separability, unitality).  Until then the longer route below is the one that
stands on definitions we have quoted ourselves.

### `tau` is hyperlinear — the definitional route, kept as a fallback

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

## The external cross-check

Schafhauser arXiv:2306.02498 Proposition 2.2 looks like a shortcut around the
whole "not MF" half.  It is not, quite: his Definition 2.1 asks for exactly
linear, exactly self-adjoint maps where Shulman asks only for asymptotically
linear ones, so entering his proposition from Shulman's hypothesis is itself a
step.  The comparison is written out in [[hyperlinear-trace-not-mf-trace]].
His Definition 1.1 group notion being "(a priori) quite a bit stronger" than
Carrion--Dadarlat--Eckhardt is verified verbatim and is the part of the
cross-check that costs nothing.
