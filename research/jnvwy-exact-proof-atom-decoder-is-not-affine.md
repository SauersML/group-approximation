---
rg: 2
id: jnvwy-exact-proof-atom-decoder-is-not-affine
kind: claim
title: The abstract JNVWY Boolean-cube decoder is nonadditive off the accepted PCP domain
distinct_from:
  jnvwy-low-degree-pcp-reflects-affine-unsafety: that starts with honest proof tables whose first two polynomials are canonical linear encodings; this obstruction concerns arbitrary positive proof atoms extracted from a perfect answer-reduced strategy.
  dfnqxy-pcpp-contract-allows-nonlinear-proof-views: that appends a nonlinear proof bit to an abstract PCPP contract; this is the literal decoding map and literal low-degree proof domain in JNVWY Theorem 10.25.
  jnvwy-perfect-introspection-forces-full-seed-support: that proves every source perfect model is affine-unsafe; this explains why exact atomwise decoding of a later model does not yet transport that conclusion.
  jnvwy-positive-perfect-proof-atoms-have-boolean-input-cubes: that uses the explicit padded succinct-decider clause families to show that the first two tables of every everywhere-accepted proof atom lie in the Boolean domain on which the decoder is linear.
---

**ESTABLISHED DOMAIN WARNING, NOT AN OBSTRUCTION ON PERFECT ACCEPTED
ATOMS.**  At perfect
success the JNVWY line--point acceptance equations do yield more than the
paper's robust low-degree theorem.  For a fixed oracle question, exact
diagonal line consistency makes every pair of `POINT_6` PVMs commute, because
every two points lie on a sampled diagonal line.  Joint atoms therefore give
full vector-valued tables.  Axis-line consistency forces their coordinates to
be individual-degree-`d` polynomials, and the `POINT_i--POINT_6` checks give
legal proof tuples

```text
Pi=(g_1,...,g_5,c_0,...,c_(m')).                       (NAD1)
```

The PCP game check accepts every evaluation of every positive atom.  Thus
JNVWY Theorem 10.25 decodes `g_1,g_2` to an accepted source answer pair.  This
is an exact atomwise decoder and requires no limiting or robust strategy
theorem.

On the full legal low-degree domain this decoder is **not an affine map**.
JNVWY defines

```text
Dec_{0,1}(g)_y = g(y) if g(y) is 0 or 1, and 0 otherwise (NAD2)
```

on the Boolean cube.  Let `theta` be any field element outside `{0,1}`.  Since
the field has characteristic two, `theta+1` is also outside `{0,1}`.  For one
Boolean point `y`, put

```text
g^(1)=theta ind_y,   g^(2)=(theta+1) ind_y,   g^(3)=0. (NAD3)
```

These are legal multilinear, hence individual-degree-`d`, polynomials.  Yet

```text
Dec(g^(1))=Dec(g^(2))=Dec(g^(3))=0,
Dec(g^(1)+g^(2)+g^(3))=Dec(ind_y)=e_y.                 (NAD4)
```

So restriction/evaluation of proof tables is linear, but the source-answer
decoder used in Theorem 10.25 is not even odd-additive on the exact legal proof
domain.

The two displayed algebraic PCP checks, viewed without the special form of
the succinct circuit, do not include a separate Booleanity equation for all
values `g_i(y)`.  Pointwise perfect acceptance implies the identities

```text
c_0 = phi_arith product_i(g_i-o_i),
c_0 = sum_j c_j zero(z_j),                              (NAD5)
```

and hence that on every selected Boolean clause at least one `g_i(x_i)` equals
its Boolean literal.  For a generic clause system this need not state that
every other `g_i(x_i)` belongs to `{0,1}`.  On that abstract domain it supplies
no identity

```text
Dec(sum_i g_i) = xor_i Dec(g_i).                        (NAD6)
```

Thus exact atomwise decoding plus *generic* low-degree linearity would not be
enough for odd-xor reflection.

For the literal JNVWY verifier, however, the missing source-specific fact is
true.  The equality and unit-clause families of `PaddedSuccinctDecider` force
`g_1,g_2` to be Boolean on their cubes for every everywhere-accepted proof
atom; see `jnvwy-positive-perfect-proof-atoms-have-boolean-input-cubes`.
Therefore `(NAD3)--(NAD4)` cannot occur on the accepted perfect-atom domain,
`(NAD6)` does hold there, and
`jnvwy-perfect-answer-reduction-reflects-affine-safety` closes the former
support-projection seam.  The warning remains relevant only when one replaces
the explicit JNVWY clause generator by an arbitrary PCP contract or considers
legal low-degree tables not accepted everywhere.
