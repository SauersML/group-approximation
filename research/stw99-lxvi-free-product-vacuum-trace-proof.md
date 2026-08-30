---
rg: 2
id: stw99-lxvi-free-product-vacuum-trace-proof
kind: route
title: Use the CAR trace as a faithful vacuum trace and descend simple full products
target: stw99-lxvi-tracial-free-constructions-are-stably-finite
requires: []
---

Write `tau=tau_D`.  We first treat crossed products.  Uniqueness of the CAR
trace gives

```text
tau after alpha_g=tau                         (g in G).
```

Let `E:D crossed_product_(alpha,r) G ->D` be the canonical expectation.
It is faithful.  On the algebraic crossed product, invariance and traciality
of `tau` show directly that `tau after E` is tracial.  Indeed the only
nonzero case for two monomials has `h=g^(-1)`, and then

```text
tau(E((a u_g)(b u_h))) = tau(a alpha_g(b))
                        = tau(b alpha_(g^(-1))(a))
                        = tau(E((b u_h)(a u_g))).
```

Since `tau` and `E` are faithful, `tau after E` is faithful.  A unital
C*-algebra with a faithful tracial state is stably finite: the matrix traces
are faithful, and a projection equivalent to a proper subprojection would
give a nonzero complementary projection of trace zero.  This proves the
reduced crossed-product assertion.

The full crossed product maps unitally onto the reduced crossed product.  If
the full crossed product is simple, the kernel of this nonzero quotient is
zero.  It is therefore isomorphic to the reduced crossed product and is
stably finite.

Now form the reduced amalgamated free product

```text
(A,E)=star_D (A_i,E_i).
```

Faithfulness of the `E_i` makes the vacuum expectation `E:A->D` faithful in
the reduced construction.  The standard reduced-word calculation shows
that

```text
Tau=tau after E
```

is tracial.  For completeness, center each letter by replacing `a in A_i`
with `a-E_i(a)`.  Alternating products of centered letters from distinct
factors have vacuum expectation zero.  Expanding products into these
reduced words, cyclically moving a letter either leaves a reduced word, in
which case both vacuum values vanish, or performs a multiplication inside
one factor.  In the latter case the two values agree because
`tau after E_i` is tracial and each `E_i` is `D`-bimodular.  Induction on
word length gives `Tau(xy)=Tau(yx)` on the algebraic free product, hence on
`A` by continuity.

The CAR trace is faithful, so

```text
Tau(x* x)=0 => E(x* x)=0 => x=0.
```

Thus `Tau` is a faithful trace and the reduced amalgamated free product is
stably finite.  As above, simplicity makes the canonical quotient from the
full amalgamated product to the reduced one injective, proving the full
assertion.

For an ordinary reduced free product, use scalar amalgamation.  The CAR
trace and the prescribed faithful traces on the other factors give exactly
the faithful free-product trace just constructed.  This proves the last
case.

Faithful traces restrict faithfully to unital hereditary corners, and their
matrix extensions are faithful.  Hence every matrix algebra and every
unital corner of each reduced construction is finite.  The established
injective-limit permanence theorem then rules out assembling an unstable
seed from an injective system of these corners.

The argument explains the coherence obstruction.  Automorphisms preserve
the unique CAR trace, and trace-preserving free amalgamation preserves it as
the vacuum trace, so no multiplicity imbalance can first appear at a matrix
amplification.  A viable LXVI construction must leave this entire
trace-preserving reduced framework, even when its CAR inclusion has infinite
module index.
