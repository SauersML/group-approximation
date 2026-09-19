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
---

## Why sufficient

Let `W` be the witness of `sofic-non-mf-witness`: sofic, and not operator MF.
Put `A = C^*(W)`, separable and unital, and let `tau` be its canonical trace.

**`tau` is hyperlinear.**  Soficity gives unitaries `u_n : W -> U(k_n)` with
`||u_n(g)u_n(h)-u_n(gh)||_2 -> 0` and `tr(u_n(g)) -> 0` for `g != 1`, so the
induced map into the unitary group of the tracial ultraproduct
`R^omega = prod_n M_(k_n)/J`, `J = {x : lim_omega ||x_n||_2 = 0}`, is a group
homomorphism.  By the universal property of the **full** group C-star
algebra it extends to a `*`-homomorphism `pi : A -> R^omega`, and
`tr_omega circ pi` agrees with `tau` on the group elements, hence on their
dense span, hence everywhere.

Now lift.  By the Bartle--Graves theorem --- in the sharpened form that opens
arXiv:2507.22783, a continuous section of norm exactly one --- the quotient
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

**`tau` is not MF.**  If it were, `regular-character-mf-trace-implies-group-mf`
would make `W` operator MF, contradicting `sofic-non-mf-witness`.  End proof.

## Trust surface

Three inputs, in decreasing order of what a reviewer should check.

1. `sofic-non-mf-witness` --- this repository's own theorem, Lean-checked as
   `witness_sofic_hyperlinear_nonMF`, and frozen pending specialist review.
   Everything here inherits that status.
2. The definitions of hyperlinear trace and MF trace, quoted verbatim from
   arXiv:2507.22783v3 in
   `regular-character-mf-trace-implies-group-mf`.  Note that they impose no
   positivity, only pointwise-bounded asymptotic linearity, multiplicativity
   and `*`-preservation; the argument uses exactly those.
3. Bartle--Graves, used only to produce a continuous section.  Any continuous
   section of any norm serves; the norm-one refinement is not needed.

If instead one prefers the completely positive route, `tau` is an amenable
trace because `L(W)` is Connes embeddable, and amenable traces are
hyperlinear by inspection of the definitions; that argument replaces the
section by Brown's characterization of amenable traces and is the same
statement.
