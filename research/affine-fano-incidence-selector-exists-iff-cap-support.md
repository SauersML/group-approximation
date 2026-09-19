---
rg: 2
id: affine-fano-incidence-selector-exists-iff-cap-support
kind: claim
title: An affine dynamic Fano selector exists exactly on cap-supported output
distinct_from:
  dynamic-fano-cap-incidence-labels-are-a-reversible-dilation: that allows the nonlinear incidence relation and proves that a local quantum label can always be adjoined; this proves that expressing the label by binary linear equations restores exactly the original cap-support gate.
  rstar-cap-support-is-one-character-row: that uses one fixed scalar character on the old context; this permits an output-dependent selector and arbitrary affine auxiliary variables, but proves that they give no additional power.
  tracial-cap-menus-are-central-core-partitions: that classifies reducing tracial branch selectors in an operator model; this is the scalar affine-projection obstruction before any tracial postselection or global branch extraction.
---

**ESTABLISHED EXACT LOCAL FIREWALL.**  Put

```text
V=F_2^3,
T=V minus {0},
I={(t,a) in V times V : a dot t=1}.                    (AFI1)
```

The equation in `(AFI1)` already forces both `t` and `a` to be nonzero.  For
`S subseteq T`, the following are equivalent.

1. `S` is contained in a maximal Fano cap:

   ```text
   S subseteq C_lambda={t:lambda dot t=1}
   for some lambda!=0.                                 (AFI2)
   ```

2. There is an affine relation `A subseteq V times V` such that

   ```text
   S subseteq pr_t(A),             A subseteq I.        (AFI3)
   ```

3. There is a finite binary LCS gadget, with visible triples `t,a` and any
   finite number of auxiliary Boolean variables, such that every `t in S`
   has an exact scalar extension and every exact scalar solution satisfies

   ```text
   a dot t=1.                                           (AFI4)
   ```

Consequently, making the nonzero functional `a` a *dynamic* LCS output does
not bypass Fano-cap support.  A perfect operator model with local joint
support `S` extends through such a gadget only if the old support already
satisfies one fixed character row `(AFI2)`.

## Proof

The scalar solution set of a binary LCS, including its auxiliary variables,
is affine over `F_2`; its projection to `(t,a)` is affine.  Thus `3 => 2`.
The implication `1 => 3` uses the one-row gadget `a=lambda` together with
`lambda dot t=1`; equivalently take

```text
A={(t,lambda):t in Aff(S)}.                             (AFI5)
```

To prove `2 => 1`, let `B=pr_t(A)`.  It is an affine subset of `V`, contains
`S`, and does not contain zero because `A subseteq I`.  Write

```text
B=b+W,                 b notin W.                       (AFI6)
```

There is a linear functional `lambda` which vanishes on `W` and has
`lambda(b)=1`.  Hence `lambda(t)=1` on all of `B`, proving `(AFI2)`.

The same calculation gives the strongest universal obstruction.  The
affine hull of the full incidence relation is

```text
Aff(I)=V times V.                                       (AFI7)
```

Indeed, if an affine functional

```text
u dot t+v dot a+c                                       (AFI8)
```

vanishes on `I`, then for a fixed nonzero `t` the differences of the four
incident `a` values span `t^perp`.  Hence `v` lies in `span(t)` for every
nonzero `t`, forcing `v=0`.  Interchanging `t` and `a` forces `u=0`, and then
`c=0`.  Therefore an affine gadget accepting all twenty-eight incident
pairs accepts every pair after affine closure and cannot enforce incidence
at all.

## Operator interpretation

For a commuting context PVM `(p_t)_(t in S)`, suppose the proposed selector
and its affine auxiliary registers are **jointly classical with the old
context**, so every gadget observable commutes with every `p_t`.  Compressing
to a positive atom then gives a nonzero representation of the gadget's
finite abelian scalar algebra, hence a scalar witness over that `t`.
Conversely scalar witnesses may be installed by functional calculus on the
orthogonal atoms.  Thus the scalar projection argument applies exactly to
jointly classical/nondemolition local operator extensions.

No assertion is made for contextual LCS auxiliaries which fail to commute
with the visible context.  Allowing those is the full perfect-completeness
LCS compiler problem, not a classical selector construction.

The nonlinear incidence PVM of
`dynamic-fano-cap-incidence-labels-are-a-reversible-dilation` escapes this
lemma only because `(AFI4)` is bilinear rather than LCS-affine.  That escape
is semantically reversible and still does not provide a fixed profile.
