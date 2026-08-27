---
rg: 2
id: fanizza-bad-atoms-have-symmetric-frames
kind: claim
title: All 26 Fanizza bad atoms share one source-fixed rank-three symmetric frame
artifacts:
  - experiments/fanizza_partial_center_frame_search.py
distinct_from:
  fanizza-bad-atoms-have-source-fixed-paired-frames: that restricts the baseline word to one coordinate and necessarily exports a rank-four center; this permits an arbitrary dual baseline pair and obtains rank three.
  support-packet-paired-word-frame-exposes-forbidden-rank: that uses the decomposable relation kernel span(e01,e13,e23); the Fanizza frames use the inequivalent symmetric kernel span(e01,e23,e03+e12).
---

Choose the OBDD Schur compilers of baseline ranks `5,6,11` for the three
nonlinear Fanizza predicate shapes.  The middle value deliberately spends one
extra pivot relative to the smallest C17 compiler: the variable orders
`(d,p,q)` and `(d,q,p)` cover its asymmetric bad atom, while both baseline-five
orders do not.

For every one of the `2+4+20=26` bad atoms `a`, atom-normalize the corresponding
Schur matrix to the identity while keeping its last coordinate equal to the
named relative pair.  There are baseline words `u,v`, each of weight at most
two, with

```text
u dot v = 1,                                             (SKF1)
```

such that the core-plus-relative commutator block

```text
B_(u,v)(x) = [[u^T M(x)v, u^T M(x)e_*],
              [e_*^T M(x)v, e_*^T M(x)e_*]]             (SKF2)
```

has affine span rank three.  Every chosen block has the same relation kernel
in `wedge^2(F_2^4)`:

```text
K_sym = span{e_01,e_23,e_03+e_12}.                       (SKF3)
```

Apply the coefficient shear

```text
p_0 -> p_0 p_1, p_1 -> p_1,
q_0 -> q_0 q_1, q_1 -> q_1.                             (SKF4)
```

The sheared and unsheared coefficient commutator maps have the identical
kernel `(SKF3)`, as do the combined source-coefficient maps.  Hence the edge
isomorphism fixes the entire source selector center.  At source atom `a`, the
unsheared coefficient character `a` cancels the source form.  A listed
coefficient character makes the sheared form rank two, and exactly the same
rank-two matrix occurs on the unsheared side at a listed target coefficient
character while the source character remains `a`.

The escape is uniform in two further senses.  The listed sheared and target
coefficient characters all lie in the `J=+1` sector, whereas the fixed source
atom lies in `J=-1`.  Moreover, the 26 rank-two escape forms are only

```text
e_02^*  or  e_13^*.                                    (SKF5)
```

Simultaneously swapping generators `0<->1` and `2<->3` preserves `(SKF3)`
and swaps the two forms in `(SKF5)`.  Thus every atom can be aligned to the
same hard root `e_02^*` without changing the finite edge group or the source
selector center.

Thus all actual nonlinear atoms admit one common **three-coordinate** finite
edge group, literal source-atom preservation, and one reverse Pauli bit.  The
finite search is exact and exhaustive over all dual words of weight at most
two and all coefficient characters.  It succeeds on `26/26` atoms in under
16 MB on one low-priority MSI core.  The search explicitly restricts both
reverse characters to `J=+1` and asserts the two-form classification `(SKF5)`.

The kernel `(SKF3)` is not in the `GL_4(F_2)` orbit of the older support-packet
kernel: it contains the nondecomposable wedge `e_03+e_12`.  Consequently the
old two-sided E5 clock cannot be imported by a word change; the compatible
one-sided clock is `fanizza-symmetric-kernel-has-two-root-e5-clock`.
