---
rg: 2
id: agent-pk-affine-ghost-survives-quotient
kind: claim
title: Every affine-hull ghost has positive twisted-regular mass in the full projective quotient
artifacts:
  - research/agent-pk-affine-ghost-survives-quotient-proof.md
distinct_from:
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that identifies the affine hull cut out by scalar stabilizers in the original context; this proves that every extra affine-hull character survives as a positive projection in the canonical twisted-regular trace of the full projective quotient.
  forbidden-character-kernel-quotient-compiler: that gives a positive nonhyperlinear quotient when the perfect-model kernel separates every forbidden character; this computes the exact failure when a forbidden character lies in the affine hull of the perfect support.
---

Let `theta:G->U(M)` be a tracial representation and let `D<=G` be a finite
abelian context subgroup.  Write the spectral support of `theta|D` as

```text
R={r in hat D : theta(e_r) != 0},
e_r=|D|^(-1) sum_(d in D) overline(r(d)) d.            (AAG1)
```

Let `K` be the full projective kernel of `theta`, with scalar character
`chi`, and put `K_D=K intersect D`.  Then

```text
{a in hat D:a|K_D=chi|K_D}=Aff(R).                    (AAG2)
```

Form the projective quotient of `G` by the graph of `(K,chi)`, equivalently
the twisted group algebra of `G/K` in the `chi` sector.  Its local context
algebra has precisely the character atoms indexed by `Aff(R)`.  In its
canonical twisted-regular trace `tau_reg^chi`, every such atom has equal
positive mass:

```text
tau_reg^chi(e_a)=1/|Aff(R)|,       a in Aff(R).        (AAG3)
```

In particular, if a forbidden assignment `a` lies in `Aff(R) minus R`, its
projection vanishes in the selected perfect representation but survives
with positive mass in the canonical trace of the full projective quotient.

For the fixed nonlinear BCS this rules out a direct source-ideal argument
for `agent-projective-kernel-one-player-monomial-face-gap`: whenever a
context has such an affine ghost, the canonical projective-quotient trace is
not a perfect BCS trace.  Proving that trace non-CE must use a new global
property of the projective quotient; it cannot follow by applying the known
non-CE perfect-BCS gap to that trace.
