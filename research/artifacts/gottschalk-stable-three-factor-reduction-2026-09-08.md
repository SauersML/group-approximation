# Stable reduction to three-input interactions

Date: 2026-09-08. Purely algebraic reduction; no computation is used.
Gottschalk's surjunctivity conjecture remains open. The theorem identifies
a universal class to which a proof would have to apply; it does not prove
that injective maps in that class are surjective.

## Universal finite-alphabet statement

Let `G` be any group, let `A` be a finite alphabet with `q>=2` symbols,
and let `F:A^G -> A^G` be a cellular automaton. Identify `A` with the
underlying set of the ring `R=Z/qZ`.

There are a finite number `N` of tracks, reversible cellular automata
`S,T` on `(R^N)^G`, and a cellular automaton

```
H=T o (F × id_((R^(N-1))^G)) o S
```

such that each output coordinate of `H` is a finite sum of terms of the
form

```
c product_(l=1)^d phi_l(x_(j_l)(g s_l)),       0<=d<=3,
```

where `c∈R`, each `phi_l:R -> R` is a unary function, each `j_l` is a
track index, and each `s_l` is a memory element. Both domain and codomain
are the same full shift `(R^N)^G`. The input and output changes `S,T`
are finite compositions of explicitly invertible local shears.

Consequently `H` is injective exactly when `F` is injective, and is
surjective exactly when `F` is surjective. The same statement holds for
an initial finite number of tracks. The one-symbol alphabet is trivial.

Here the bound three counts unary factors. It is not a bound on ordinary
polynomial degree over `Z/qZ`: the unary lookup functions need not be
polynomial functions over this ring.

## Initial finite expression

Choose finite memory `M` containing the identity. Every local rule
`mu:R^M -> R` has the exact expression

```
mu((X_s)_(s∈M))
  = sum_(p∈R^M) mu(p) product_(s∈M) delta_(p_s)(X_s),
```

where `delta_a(t)` is one if `t=a` and zero otherwise. At every input
exactly one product is one. This uses no field assumption. With several
input tracks, use the corresponding track-address pairs in place of
`M`. Thus the local rules admit finite sums of products of unary
functions, initially with no fixed bound on their factor lengths.

We keep an explicit finite expression, allowing repeated term
occurrences. Uniqueness of an expression for a function is unnecessary.

## One reversible cancellation

Suppose one output coordinate `F_i` has a selected term `cAB` of factor
length `d>=4`. Split its unary factors into two products `A,B` with

```
2<=a=length(A)<=d-2,       2<=b=length(B)<=d-2,
a+b=d.
```

All quantities below are evaluated at the same output site `g`; the
products `A(x)(g),B(x)(g)` may use arbitrary addresses in `M`.

Add two fresh identity tracks `u,v`. Precompose by the domain shear

```
S_step(x,u,v)=(x,u+A(x),v+B(x)).
```

It is reversible, with inverse obtained by subtracting `A(x),B(x)`.
Its old input tracks are unchanged, so the old output rules remain
`F_j(x)`. Its two new outputs are `u+A(x),v+B(x)`.

Postcompose by the output shear

```
T_step(y,r,s)=(y-c r s e_i,r,s),
```

where the product is pointwise and `e_i` selects the old output track
`i`. This shear is reversible by adding the same product, since its
tracks `r,s` are unchanged. The resulting old coordinate `i` is

```
F_i(x)-c(u+A(x))(v+B(x))
  = (F_i(x)-cAB)-cuv-cuB-cvA.
```

Thus the selected term cancels exactly. The replacement terms have
factor lengths `2,b+1,a+1`, and the two new coordinates have expressions
`u+A`, `v+B`, with lengths `1,a,1,b`. All seven newly introduced term
occurrences have length strictly smaller than `d`. The new variables
`u,v` appear as unary identity functions. Existing lookup functions and
all other output terms remain unchanged.

## Finite termination and exact preservation

For a finite expression define the positive integer

```
Phi = sum_(all output term occurrences m) 8^(length(m)).
```

The cancellation removes one contribution `8^d` and introduces at most
seven contributions, each at most `8^(d-1)`. Therefore `Phi` strictly
decreases. This includes the two newly added identity terms; increasing
the number of tracks is not omitted from the count. Terms with zero
coefficients may simply be deleted. Every step is finite, and a strictly
decreasing sequence of nonnegative integers cannot be infinite. The
procedure therefore ends with every term of length at most three.

Every intermediate map has memory contained in the original `M`:
factorization and the displayed products introduce new tracks, but no
new spatial addresses. The final composed changes `S,T` and their
inverses may have larger memory, but are finite compositions of local
maps and consequently still have finite memory. Stabilizing earlier
shears by identities gives the displayed final equality with `F`.

Adding identity tracks preserves injectivity and surjectivity in both
directions. Precomposition or postcomposition by a bijection also
preserves both properties in both directions. Hence no implication is
lost at any cancellation step.

In particular, for each fixed group, Gottschalk's assertion for all
finite alphabets is equivalent to its assertion for the three-factor
class above, for all integers `q>=2` and all finite track counts.

## Ordinary cubic polynomial version over finite fields

If the original alphabet is a finite-dimensional vector space over a
finite field `k`, first write its local rules as ordinary polynomials in
the finitely many scalar input variables. Such an expression exists by
finite-field interpolation. Apply the same cancellation, now splitting
ordinary monomials and counting total degree. Every new term again has
strictly smaller degree, so the same integer potential proves
termination with total degree at most three. All shears and their
inverses are polynomial cellular automata over `k`.

This finite-field conclusion is stronger than a bound of three unary
lookup factors for that alphabet. It is a separate use of the argument;
one must not replace a lookup function by a higher-degree polynomial
after termination and still claim a cubic degree bound.

The finite-dimensional stabilization method is classical: see
Bass, Connell, and Wright, *The Jacobian conjecture: reduction of degree
and formal expansion of the inverse*, Chapter II, Proposition 3.1
([author-uploaded primary text](https://www.researchgate.net/publication/38390367_The_Jacobian_conjecture_Reduction_of_degree_and_formal_expansion_of_the_inverse),
[DOI](https://doi.org/10.1090/S0273-0979-1982-15032-7)). The proof above
checks the equivariant local version directly and the finite-alphabet
lookup extension separately. No Jacobian hypothesis or
characteristic-zero theorem is used.

## Why the existing elimination results do not finish the problem

The reduction imposes neither a bipartite operand graph nor
homogeneous-linear dependence on a block of input tracks. It does not
make any auxiliary track a preserved certificate. For example, over
`F_2`, the scalar expression

```
F(x)=x+x_a x_b x_c x_d
```

with `A=x_a x_b`, `B=x_c x_d` becomes

```
H_x=x+uv+u x_c x_d+v x_a x_b,
H_u=u+x_a x_b,
H_v=v+x_c x_d.
```

The auxiliary outputs depend on `x`; they are not identity certificate
tracks. The `x` output is not homogeneous linear in the whole `x` track
for fixed `u,v`, since it has both a constant-in-`x` term `uv` and
products of two shifted `x` values. The pure quadratic controls in
[the block-elimination artifact](gottschalk-quadratic-block-elimination-2026-09-08.md)
also do not cover the cubic terms. The zero-auxiliary-output equations
give `u=A(x),v=B(x)` in this example, and substitution returns exactly
the original scalar rule. They do not provide a known bijective fiber.

The example describes the transformed architecture; it makes no claim
that the displayed scalar rule is injective. A theorem making every
injective member of this universal three-factor class surjective would
settle the headline conjecture, but no such theorem is established here.
