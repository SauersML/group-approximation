---
rg: 2
id: generic-masa-perturbation-high-type-proof
kind: route
title: Perturb one code reflection off a separating diagonal masa
target: high-type-mass-is-discontinuous-at-exact-code-tuples
requires:
  - dellm-all-dual-presentation-has-many-unique-neighbors
---

Choose an active coordinate `i_0`.  Since puncturing `C_n` at `i_0` has
kernel contained in `{0,e_(i_0)}` and the distance is at least two, it is
injective.  Select `d_n` codewords using both values at `i_0`.  On the basis
indexed by these words define

```text
 D_i e_c=(-1)^(c_i)e_c.
```

The joint eigenvalue strings of `(D_i)_(i!=i_0)` are distinct, so those
reflections generate the diagonal masa `A_n`.

Let `P_0=(I-D_(i_0))/2`.  Generic projections in its unitary orbit have no
zero matrix entries, and such projections occur arbitrarily close to `P_0`:
each zero-entry condition is a proper real-analytic subvariety of the orbit.
Choose `U_n->I` outside their finite union and put

```text
 Q_(i_0)=U_n D_(i_0) U_n^*,       Q_i=D_i otherwise.
```

If a diagonal matrix `diag(x_a)` commutes with
`U_nP_0U_n^*`, then
`(x_a-x_b)(U_nP_0U_n^*)_(a,b)=0` for all `a,b`; full off-diagonal support
forces every `x_a` equal.  Hence the tuple has scalar commutant and generates
`M_(d_n)`.

Replacing one factor of any fixed-width relation changes its normalized-HS
value by at most `||Q_(i_0)-D_(i_0)||_2`; a commutator changes by at most
twice this amount.  All presentation widths are fixed, so choosing
`U_n->I` proves `(HTD1)`.

Finally, `M_(D+1)` does not satisfy the standard identity `s_(2D)`.
Choose one violating contraction tuple there and tensor it with identity
matrices.  Both operator norms and normalized-HS norm of the polynomial are
unchanged under tensor amplification, giving the uniform PI violation
asserted in the claim.
