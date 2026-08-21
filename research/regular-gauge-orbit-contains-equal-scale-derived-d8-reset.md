---
rg: 2
id: regular-gauge-orbit-contains-equal-scale-derived-d8-reset
kind: claim
title: A four-point gauge orbit contains an ordinary-word derived D8 reset at no extra spin scale
distinct_from:
  pauli-quarter-holonomy-is-balanced-derived-reset: that extracts a D8 from two Hecke projection reflections but leaves ordinary-word exposure open; this constructs the D8 by literal permutations of the already required gauge-covariant orbit.
  derived-lifted-gauge-reset-spin-bridge: that must still attach the old and next semantic Schur packets; this closes the local derivedness, word-exposure, and scale clauses for one reset direction.
---

Let `G=(C_2)^m`, `m>=2`, be the incidence-gauge group supplied by gauge
doubling, acting regularly on its orbit `Omega=G`.  Fix a nonzero reset
translation `s in G`, and choose `t` independent of `s`.  Partition `Omega`
into the four-point cosets of

```text
W=<s,t> ~= (C_2)^2.
```

On every coset choose the same identification with the four vertices of a
square so that translation by `s` is the half-turn.  Let `p,q` be the two
diagonal square reflections whose axes differ by one edge.  Then, as literal
permutations of the existing gauge orbit,

```text
p^2=q^2=s^2=1,
[p,q]=s,
[p,s]=[q,s]=1.                                      (GOD1)
```

Thus `<p,q>` is `D_8` and the reset translation is its central commutator.
No tensor factor, new orbit point, or representation-dimension enlargement is
introduced.

On `C[Omega]`, translation by `s` has equal `+1` and `-1` eigenspaces.  The
four-point square representation of `D_8` decomposes as two one-dimensional
representations with central sign `+1` and one two-dimensional spin
representation with central sign `-1`.  Consequently every four-point block
has

```text
dim H_(s=-1)=2,
H_(s=-1) = one D8 spin simple,                         (GOD2)
```

and the global `s=-1` sector is exactly
`2^(m-2)` copies of that spin simple.  The derived lift therefore preserves
the complete central-sign multiplicity ledger at equal scale.

For a gauge-covariant exact BCS representation

```text
Pi = direct_sum_(g in G) pi composed theta_g,
```

every logical product and the native Fanizza signal are fixed by all
`theta_g`.  They act identically on every gauge block.  Hence the literal
permutations `p,q` commute with the whole logical BCS algebra, even though
they need not preserve either private gauge share separately.  The lift is
therefore semantically invisible on the marked base while remaining oriented
on the private gauges.

If a packet needs at least two gauge directions and the source has only one,
one dummy doubled share supplies `t`; it contributes no logical generator or
constraint.

This closes the three local defects of the naive wreath lift:

1. `s` is an ordinary commutator word;
2. the word acts on the already present gauge orbit rather than on a tensor
   doubling; and
3. its negative sector is exactly the balanced two-dimensional Pauli spin.

The remaining part of `derived-lifted-gauge-reset-spin-bridge` is semantic
incidence: identify a codimension-one residual spin packet common to the old
derivative cell and every next selector-sector baseline, then attach the above
`D_8` as the replaced hyperbolic pair.  The local derived lift itself no
longer requires a Hecke reflection or an equal-scale search.

