---
rg: 2
id: agent-free-compressor-reynolds-zero-has-affine-ghosts
kind: claim
title: Vanishing forbidden Reynolds atoms need not give a separating perfect kernel
distinct_from:
  forbidden-character-kernel-quotient-compiler: That proves local kernel separation is sufficient; this shows that zero forbidden Reynolds projections alone do not imply its hypothesis.
  agent-pk-affine-ghost-survives-quotient: That computes positive twisted-regular mass after the full projective quotient; this gives the elementary local obstruction directly in the shared BCS context group.
  central-sign-bcs-atoms-are-subgroup-reynolds-projections: That identifies each Boolean atom with a Reynolds projection; this distinguishes vanishing of that projection from character separation by the representation kernel.
---

Let `H` be one finite elementary-abelian BCS context group and let `theta`
be any tracial representation.  If `S` is the support of its character PVM,
then

```text
ker(theta) intersection H=intersection_(psi in S) ker(psi),
{chi:chi is trivial on ker(theta) intersection H}=span(S). (RAG1)
```

After fixing the `J=-1` affine slice, the second set is exactly the affine
hull of `S`.  Therefore a forbidden Reynolds atom `e_chi` may vanish in the
perfect model while `chi` remains trivial on the local kernel: this happens
precisely when

```text
chi in affineHull(S) minus S.                            (RAG2)
```

There is a three-bit exact example.  Take

```text
S={000,011,101}.
```

The character `110` is absent, so its Reynolds atom is zero, but

```text
110=000+011+101
```

in the affine slice.  Hence it is trivial on the common local kernel and
survives every quotient by that kernel.

Consequently the known shared non-CE BCS perfect trace does not automatically
instantiate `forbidden-character-kernel-quotient-compiler`, even after every
forbidden assignment is rewritten as a subgroup Reynolds projection.  The
needed assertion is exactly

```text
affineHull(S_c) subseteq Allowed_c
```

for every context.  By
`locally-affine-support-bcs-is-exactly-the-lcs-boundary`, obtaining this while
retaining non-CE is equivalent to producing a non-CE binary LCS and hence to
the target nonhyperlinear-group theorem itself.  Reynolds atom encoding does
not weaken that frontier.
