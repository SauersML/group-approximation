---
rg: 2
id: stw81-semiprojective-local-af-model-proof
title: Lift finite-dimensional fibre models over neighborhoods and colour the supports
kind: route
target: stw81-continuous-simple-af-fields-have-base-bound
requires: []
artifacts:
  - research/artifacts/stw81-continuous-af-field-audit-2026-08-30.md
---

# Lift finite-dimensional fibre models over neighborhoods and colour the supports

Put `n=dim(X)`. Fix a finite self-adjoint set `F` in `A` and
`epsilon>0`.

## 1. The fibre ideal as a neighborhood limit

Fix `x in X`. Choose a decreasing neighborhood basis `(U_k)` at `x` such
that each closure `K_k=closure(U_k)` is compact, `K_(k+1)` is contained in
`U_k`, and `intersection_k K_k={x}`. Define

```text
J_k = C_0(X minus K_k) A.
```

The `J_k` form an increasing sequence inside the fibre ideal

```text
I_x = C_0(X minus {x}) A = ker(A -> A_x).
```

Their union is dense in `I_x`. Indeed, if `a_x=0`, continuity of
`y -> ||a_y||` makes `a` uniformly small on a neighborhood of `x`. Choose
an index `l` so that `K_l` lies in that neighborhood, and a scalar cutoff
which is zero on `K_l`, is one off the small neighborhood, and changes value
only where `a` is small. Its product with `a` belongs to `J_l` and
approximates `a` in norm. Hence

```text
A_x = A/I_x = A/closure(union_k J_k).
```

## 2. Semiprojective neighborhood models

Because `A_x` is unital AF, choose a unital finite-dimensional subalgebra
`E_x` of `A_x` and a u.c.p. retraction

```text
P_x: A_x -> E_x
```

such that, for every `a in F`,

```text
||a_x-P_x(a_x)|| < delta.                                (1)
```

To obtain `P_x`, first approximate the finite set by a unital
finite-dimensional subalgebra and then extend the identity of that algebra
to `A_x`, using injectivity of finite-dimensional C-star algebras.

Let `eta_x:E_x->A_x` be the inclusion. Finite-dimensional C-star algebras
are semiprojective. Applied to the increasing ideals `J_k`, semiprojectivity
gives some `k=k(x)` and a star-homomorphism

```text
sigma_x: E_x -> A/J_k
```

whose composition with `A/J_k -> A/I_x=A_x` is `eta_x`.

The quotient `A/J_k` is the restriction of the continuous field to `K_k`.
For every `a in F`, the section

```text
y -> sigma_x(P_x(a_x))_y-a_y
```

has norm less than `delta` at `x`, by (1), and has continuous norm on
`K_k`. After shrinking, there is an open neighborhood `W_x` of `x`, with
closure contained in `U_k`, such that

```text
||sigma_x(P_x(a_x))_y-a_y|| < 2 delta                   (2)
```

for `a in F` and `y in W_x`.

## 3. Compact localization and coloured refinement

Choose `h in C_c(X)_+`, `0<=h<=1`, such that

```text
||a-ha|| < epsilon/3                                    (3)
```

for `a in F`, and put `K=supp(h)`. Finitely many of the neighborhoods
`W_x` cover `K`. By the standard `(n+1)`-decomposable refinement lemma for
covering dimension (equivalently, apply a barycentric refinement to an
order-`n+1` refinement), refine this finite cover into `n+1` families

```text
V^(0),...,V^(n),
```

with members pairwise disjoint within each family and with every refined
set lying in one of the chosen `W_x`. Choose a subordinate finite partition
of unity `(f_i)` on a neighborhood of `K`, and put `g_i=hf_i`. Then

```text
sum_i g_i=h,
```

and equal-coloured supports are disjoint. For each `i`, retain the anchor
`x(i)`, finite-dimensional algebra `E_i=E_x(i)`, retraction `P_i`, and
neighborhood homomorphism `sigma_i` attached to the containing `W_x(i)`.

## 4. Localizing a quotient homomorphism

Suppose `sigma_i` takes values in `A/J_k`, with
`supp(g_i)` contained in `U_k`. Multiplication by `g_i` canonically gives a
c.p. map

```text
L_(g_i):A/J_k -> A,             L_(g_i)(q_k(a))=g_i a.
```

Indeed, if `q_k(a)=q_k(b)`, then `a-b` lies in `J_k`, and
`g_i(a-b)=0` because `J_k` is supported off `K_k` while `g_i` is supported
inside `U_k`. Matrix-level positivity follows from
`g_i a=g_i^(1/2)a g_i^(1/2)` and centrality.

Define

```text
psi_i(a) = P_i(a_x(i)),
phi_i(c) = L_(g_i)(sigma_i(c)).
```

Thus `psi=(psi_i)_i:A->direct-sum_i E_i` is c.p.c. Each `phi_i` is c.p.c.
and order zero. More explicitly, if `c,d` are orthogonal positive elements,
the product of representatives of `sigma_i(c)` and `sigma_i(d)` lies in
`J_k`; multiplying by `g_i^2` kills it, so
`phi_i(c)phi_i(d)=0`. Summing within one colour preserves order zero because
the supports are disjoint. The total return map is contractive since,
fibrewise, writing `p_i=sigma_i(1_E_i)`,

```text
sum_i phi_i(1_E_i) = sum_i L_(g_i)(p_i)
                   <= sum_i g_i 1 = h1 <= 1.
```

For `y` in the support of `g_i`, estimate (2) applies. Hence

```text
||ha-sum_i phi_i psi_i(a)|| < 2 delta                   (4)
```

for `a in F`. Taking `2 delta<2 epsilon/3` and combining (3)--(4) gives the
required `(n+1)`-coloured approximation. Therefore

```text
dim_nuc(A) <= n.
```

## 5. The shadow statement for simple non-elementary fibres

Assume now that all fibres are simple and non-elementary. The structure map

```text
Prim(A) -> X
```

is a bijection: every primitive representation has a central character
`x`, then factors through the simple fibre `A_x`, whose only primitive ideal
is zero. It is a homeomorphism because the image of the basic open set
`{P:a notin P}` is

```text
{x: a_x != 0},
```

which is open by continuity of the norm function. Thus ideals correspond to
open subsets of `X`, and their quotients are restrictions of the continuous
field to closed subsets.

If a quotient `B` contained a nonzero commutative hereditary subalgebra
`C`, choose `0!=c in C_+` and a point `x` with `c_x!=0`. Then

```text
closure(cBc)_x = closure(c_x A_x c_x)
```

is a nonzero commutative hereditary subalgebra of the simple fibre `A_x`.
It is full, so `A_x` is Morita equivalent to a commutative algebra. Simplicity
then forces `A_x` to be elementary, a contradiction. Hence every such `C`
is zero.
