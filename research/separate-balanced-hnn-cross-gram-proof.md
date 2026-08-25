---
rg: 2
id: separate-balanced-hnn-cross-gram-proof
kind: route
title: Compute the HNN/Whitehead cross-Gram and realize the zero-overlap balanced model
target: separate-balanced-hnn-cross-gram-is-typed-overlap
requires:
  - primitive-clifford-balanced-atoms-have-hnn-obstruction
  - odd-selector-row-balances-or-kills-outer-action
---

From `h p_s h^*=p_t`, direct multiplication gives

```text
(p_s h^*Wp_s)^*(p_s h^*Wp_s)=p_sW^*p_tWp_s.
```

Taking trace and using `||Wp_s||_2^2=tau(p_s)` proves `(SHG4)`.  Replacing
`h p_s h^*` by `p_t` in the trace costs at most its normalized `2`-norm,
which proves `(SHG6)`.

For the sharp model, list the joint `(Z_1,tZ_2)` characters on the four
computational basis vectors.  In the positive controlled extension their
multiplicities are

```text
(++):1, (+-):1, (-+):2, (--):0,
```

and in the negative extension they are

```text
(++):1, (+-):1, (-+):0, (--):2.
```

Their balanced sum has multiplicity `2` for all four characters.  The
restriction to `<J,Z_1,Z_2>` also has multiplicity `2` for every `J=-1`
character.  The character-preserving subgroup isomorphism is therefore
unitarily implemented by some `h`.

Finally `p_s` is a two-dimensional subspace of the negative eigenspace of
`r`.  The negative eigenspace of `t=C tensor diag(1,-1)` contains the
three-dimensional subspace `(1-f)S tensor span(e_-)`, which is orthogonal to
`p_t=fS tensor C^2`.  Prescribe the image of `p_s` inside this subspace and
complete bases separately in the two sign eigenspaces.  The resulting `W`
satisfies the odd row and has `p_tWp_s=0`.  Explicitly the two four-cycles
in `(SHG9a)` send

```text
{4,5,6,7}=Eig_-(r)  onto {1,3,5,6}=Eig_-(t)
```

and send `{4,6}=Ran(p_s)` to `{1,3}`, outside
`{6,7}=Ran(p_t)`.  This also proves that `W` is an order-four signed
permutation, as used in the amalgamation argument.

For the literal-word strengthening, realize the typed relations `yx=e` and
`xy=f` by coordinate inclusion and projection over `F_p`.  The three
elementary factors then belong to a finite general linear group and their
product is the signed Whitehead block

```text
[[1-f,x],[-y,1-e]].
```

It is a quarter-turn on the exchanged blocks and the identity on their
complement, hence has order `4`.  Taking all four scalar character twists of
the balanced packet model makes its `C_4` restriction regular.  The
restriction of a finite group's left regular representation to a subgroup
is a multiple of that subgroup's regular representation.  The amplifications
in `(SHG12)--(SHG13)` consequently agree on the amalgamated `C_4`, so their
unitary representations glue.  Scalar twisting and amplification do not
alter `p_tWp_s=0`, completing the claimed native finite-chart model.
