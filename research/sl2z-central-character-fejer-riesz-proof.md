---
rg: 2
id: sl2z-central-character-fejer-riesz-proof
kind: route
title: Split the modular central amalgam before applying Theorem B
target: sl2z-central-split-inherits-operator-fejer-riesz
requires: []
---

Write

```text
Lambda=<u,v | u^4=v^6=1, u^2=v^3>,
z=u^2=v^3.
```

The element `z` is a central involution: it is central in each cyclic
vertex group and the two copies are identified in the amalgam. Therefore

```text
e_+=(1+z)/2,       e_-=(1-z)/2
```

are orthogonal central projections with sum one. If `A=C*(Lambda)`, then

```text
A=e_+A direct_sum e_-A.                                  (MCP1)
```

## Identify both central fibers

In the positive fiber, with unit `e_+`, set

```text
a_+=e_+u,        b_+=e_+v.
```

Then `a_+^2=e_+` and `b_+^3=e_+`. Conversely, any unitaries `A_0,B_0`
with `A_0^2=B_0^3=1` give a representation of the positive fiber by
`u |-> A_0`, `v |-> B_0`, and `z |-> 1`. Thus there are no relations
besides the orders two and three, and

```text
e_+A isomorphic to C*(C2*C3).                            (MCP2)
```

In the negative fiber put

```text
a_-=i e_-u,      b_-=-e_-v.
```

Since `e_-z=-e_-`,

```text
a_-^2=e_-,       b_-^3=e_-.
```

Conversely, from `A_0^2=B_0^3=1` define `U=-i A_0` and `V=-B_0`.
Then `U^2=V^3=-1`, `U^4=V^6=1`, so this is a representation of the
negative fiber. Hence

```text
e_-A isomorphic to C*(C2*C3).                            (MCP3)
```

This also proves the identifications at the algebraic group-ring level,
not only after C-star completion.

## The extent bound survives the split

Choose coset transversals for the common `C2` in `C4` and `C6`. Every
group element has a unique amalgamated normal form

```text
z^epsilon x_1 ... x_k,
```

where adjacent `x_j` come from different vertex factors and each `x_j`
is a nonidentity transversal representative. Define amalgamated syllable
extent to be `k`; the leading common factor `z^epsilon` costs no syllable.
In either central fiber, each `x_j` becomes a scalar multiple of a
nonidentity element in the corresponding `C2` or `C3` factor. Reduced
words remain reduced. Thus the corner maps do not increase extent.

Let `E` be separable and let

```text
p in B(E) tensor C[Lambda]
```

have amalgamated syllable extent `d` and be positive in every unitary
representation of `Lambda`. Centrality gives

```text
p=p_+ + p_-,       p_epsilon=e_epsilon p=e_epsilon p e_epsilon,
```

and each `p_epsilon` is positive in every representation of its corner.
Under (MCP2)--(MCP3), each is therefore a positive operator-valued
trigonometric polynomial on `C2*C3`, of extent at most `d`.

Theorem B of Jindal--Klep--McCullough,
[arXiv:2604.27062](https://arxiv.org/abs/2604.27062), now gives

```text
p_epsilon=sum_j (q_(epsilon,j))* q_(epsilon,j),
extent(q_(epsilon,j)) <= floor(d/2)+1.                  (MCP4)
```

Pulling the two factorizations back through (MCP2)--(MCP3) and taking
their union proves (MCF1)--(MCF2). Orthogonality of the central corners
creates no cross term.

There is also an explicit positive lift through the scalar free product.
Let

```text
rho:C4*C6 -> Lambda
```

be the quotient imposing `u^2=v^3`. Lift each normal-form monomial in a
`q_(epsilon,j)` termwise. If its first syllable is in the `C4` factor,
represent a leading `z` by `u^2`; if its first syllable is in the `C6`
factor, represent it by `v^3`. For the empty word use `u^2`. Multiplication
by that leading power stays inside the first syllable, so this linear
section sends extent `k` to ordinary free-product extent at most
`max(1,k)`. Since the bound in (MCP4) is at least one, the lifts
`q~_(epsilon,j)` obey the same displayed bound. Therefore

```text
P=sum_(epsilon,j) (q~_(epsilon,j))* q~_(epsilon,j) >= 0
```

is a positive algebraic polynomial on `C4*C6`, has the controlled
factorization, and satisfies `rho(P)=p`. This is the strongest direct
way in which the 2026 theorem lifts and descends through the central
`C2` amalgam.

## Why this does not reach the Iwahori translated rows

The Iwahori compatibility problem uses two modular vertices and then
identifies the infinite edge by `b |-> sigma(b)`. At a finite authenticated
level, the relative induced selector fixes the whole BS core and asks for
one additional coefficient. Its bounded dual is a support inequality for
the constrained ucp matrix range. It is not merely positivity of a
polynomial in either modular vertex.

The distinction persists under any attempt to regard the dual certificate
as a polynomial modulo the edge relations. Let `q:W->H` be a group
quotient, let `r` be a nontrivial word of `W` killed by `q`, and write
`u_r` for its group-ring unitary. Then

```text
p_r=-(u_r-1)^*(u_r-1),
q(p_r)=0.                                               (MCP5)
```

The image is positive in `C*(H)`, while `p_r` is negative and nonzero in
`C*(W)`: the left regular representation of `W` detects
`u_r-1 != 0`. Consequently quotient positivity does not imply the
upstream all-representations positivity required by Theorem B for the
same algebraic representative.

There is no contradiction with abstract C-star lifting. A positive element
of a C-star quotient has a positive lift, for example by lifting its square
root and taking a square. That construction need not be algebraic and gives
no word-extent control. Theorem B supplies neither a controlled correction
by the relation ideal nor a relative Positivstellensatz for the quotient.

For the Iwahori quotient, the relation ideal is generated normally by all

```text
i_+(b) i_-(sigma(b))^(-1)-1.
```

The Toeplitz matrix for a positive-definite window sees their translated
conjugacy rows, not just the defining face. As the finite level moves, a
useful certificate would need relation-ideal corrections whose extent and
matrix norm are uniform in that level. The central split above controls
only the fixed relation `u^2=v^3` internal to one modular vertex.

Thus the new Fejer--Riesz theorem closes the finite central-amalgam
subproblem and gives a controlled positive lift to `C4*C6`; it does not
bound `Delta_(N,beta)(X)` or construct the missing full translated
positive-definite kernel. The nonhyperlinear-group root remains open.
