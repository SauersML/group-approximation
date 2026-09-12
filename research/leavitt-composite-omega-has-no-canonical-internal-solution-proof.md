---
rg: 2
id: leavitt-composite-omega-has-no-canonical-internal-solution-proof
kind: route
title: Evaluate the revised degree-four word on the faithful Leavitt infinite-word module
target: leavitt-composite-omega-has-no-canonical-internal-solution
requires:
  - degree-four-kl-source-face-retraction
  - leavitt-omega-has-an-explicit-distorted-target
---

Use the standard faithful action of `L_(F_2)(1,2)` on the vector space with
basis the infinite binary words, and hence the faithful action of
`EL_20(L_(F_2)(1,2))` on twenty copies of that basis.  In this model `s_i`
prefixes `i`, `t_i` deletes an initial `i` and annihilates the other
cylinder, and an elementary transvection toggles the corresponding image in
characteristic two.

The artifact implements exactly

```text
a=x_12(s_0),                 e=x_12(t_1),
q=x_34(s_1)x_(11,12)(t_0),  p=(1 2 ... 20),
r=qp,                        c=x_13(s_0),
b=r^2 a r^(-2),              d=p^2 c p^(-2).          (IS1)
```

For every radius-one candidate

```text
t in {1,p,p^(-1),q,r,r^(-1),a,e,c,b,d},              (IS2)
```

it evaluates

```text
W'(t)=r t e t a t^(-1)c t^2 b t^(-1)d t p t          (IS3)
```

on basis vectors.  In fact the single source vector

```text
(coordinate 1, 001011001101001011010011010111...)
```

is moved for every entry of `(IS2)`.  The output records its exact finite
prefix image in each case.  Because all deletion tests occur in the displayed
finite prefix and the remaining infinite tail is kept as one opaque common
symbol, every mismatch is an exact witness in the faithful module, not a
finite-ring or finite-dimensional approximation.

This closes only the canonical packet-word screen.  An arbitrary solution
`t in G`, or an embedding of the coefficient copy into a larger solution
group, is not excluded.

## Exact radius-four extension

The second artifact works directly in Bergman normal form.  A ring element is
an XOR-set of monomials `s_u t_v`, with the terminating rewrite

```text
s_(u1)t_(v1) = s_u t_v + s_(u0)t_(v0).               (IS4)
```

It uses the standard twenty-leaf prefix chart to identify `M_20(L)` with
`L`.  Consequently equality of the resulting units is exact.  The script
enumerates every freely reduced word of length at most four over

```text
{p,p^(-1),q,r,r^(-1),a,e,c,b,d}.                     (IS5)
```

Inverse pairs are suppressed during generation.  The exact counts by radius
are

```text
1, 10, 90, 810, 7290,
```

for `8,201` words in total.  For each word it constructs `(IS3)` in the
20-leaf chart and compares its Bergman normal form with the identity.  There
are zero solutions.  The run was performed through the MSI wrapper; only the
lightweight syntax check and the radius-one witness audit ran locally.
