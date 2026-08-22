---
rg: 2
id: leavitt-length-six-three-gate-weight-survivor-proof
kind: route
title: Pack two Leavitt roots into one coefficient and force three incompatible square weights
target: leavitt-length-six-three-gate-weight-survivor
requires:
  - leavitt-paired-quotient-passes-relative-weight-test
  - leavitt-gl-equals-el-and-perfect-unit-group
---

## Four coefficients still generate the whole group

Conjugation by powers of `p` gives every cyclic translate of `a` and `e`.
The two factors of

```text
q=x_34(s_1)x_(11,12)(t_0)
```

commute.  The second factor is the only one which interacts with
`x_(12,13)(s_0)`, so the Steinberg relation and `t_0s_0=1` give

```text
[q,x_(12,13)(s_0)]=x_(11,13)(1).                   (L6G.2)
```

Conjugating `(L6G.2)` by `p` and taking Steinberg commutators generates
`x_ij(1)` whenever `i,j` have the same parity.  In particular
`x_13(1),x_42(1)` are available.  The far `t_0` factor commutes with
`x_13(1)`, hence

```text
[x_13(1),q]=x_14(s_1),
[x_14(s_1),x_42(1)]=x_12(s_1).                     (L6G.3)
```

Conjugating recovers `x_34(s_1)` and division in `(L6G.3)` recovers
`x_(11,12)(t_0)` from `q`.  Powers of `p` now give adjacent roots labelled by
all four Leavitt generators.  The standard Steinberg-commutator argument
therefore gives every elementary root.  Thus `{a,q,p,e}` generates `G`.

Both `a` and `e` are nontrivial involutions because elementary roots have
order two in characteristic two.

## The paired relators and the failed weight test

For coefficient slots `(A,B,C,D,E,F)=(a,1,q,p,e,1)`, Reidemeister--Schreier
rewriting gives

```text
R_0=a_0 z q_0p_1 z e_0 z^(-1),
R_1=a_1 z q_1 z p_0e_1 z^(-1).                    (L6G.4)
```

Thus the star-graph corner labels are

```text
h_0=a_0, h_1=q_0p_1, h_2=e_0,
k_0=a_1, k_1=q_1,    k_2=p_0e_1.
```

The loops labelled `h_0,h_2,k_0` each have order two, so their double
traversals are admissible reduced cycles.  Any aspherical weight function
must give each of those three edges weight at least one.

Write the weights of `h_i,k_i` as `H_i,K_i`.  The first relator condition is

```text
H_0+H_1+H_2 <= 1,
```

so `H_1<=-1`.  The two distinct parallel edges `h_1,k_1` form a cyclically
reduced closed path, and an aspherical weight function is nonnegative on every
such path; hence `H_1+K_1>=0` and `K_1>=1`.  The `k_2`-edge is itself a loop,
so `K_2>=0`.  But the second relator condition would require

```text
K_0+K_1+K_2 <= 1,
```

whose left side is at least two.  This contradiction proves that no
aspherical relative weight function exists.  In particular the successful
weight proof for the preceding candidate cannot be repaired by redistributing
weights.

## Elementary solution and retraction checks

At `t=1`, the word becomes `a q p e`, which is nonidentity; the artifact gives
an exact moved vector in the standard infinite-word module.

If either `G_0` or `G_1` is killed in `(L6G.4)`, one relator forces `z=p^(-1)`
in the surviving copy.  The other then leaves

```text
F=a p^(-1) q p^(-1) e p.                           (L6G.5)
```

The artifact evaluates `(L6G.5)` exactly and finds a basis vector whose
coordinate moves from `1` to `20`.  Therefore neither one-copy-killing map is
a retraction.

The artifact also checks the two natural diagonal families.  It identifies
`G_1` with `G_0` either by `Ad(p^j)`, or by `Ad(p^j)` after the prefix duality
`g |-> (g^*)^(-1)`, and tests `z=p^l`, for all `j,l mod 20`.  Exact
eventually-constant infinite-word witnesses reject both relators jointly in
every one of the 800 cases.  This finite check does not decide injectivity of
the paired quotient; it places `(L6G.4)` beyond the same elementary diagonal
screen used on the preceding candidate.
