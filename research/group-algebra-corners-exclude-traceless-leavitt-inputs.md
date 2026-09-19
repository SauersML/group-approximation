---
rg: 2
id: group-algebra-corners-exclude-traceless-leavitt-inputs
kind: claim
title: Complex group-algebra corners exclude every traceless Leavitt input
distinct_from:
  augmentation-blocks-unital-leavitt-family: that excludes a binary Leavitt family from integral group rings and their full finite matrix algebras by augmentation and rational rank; this treats every nonzero projection corner of every complex group algebra using the canonical group trace.
  fixed-group-algebra-polynomials-cannot-supply-atomic-return: that gives a quantitative three-row lower bound in the spectral corner of one involution; this proves the qualitative universal obstruction for any nonzero algebraic projection and any traceless input star algebra.
  properly-infinite-cstar-quotient-is-compatible-with-fp-mf-group: that shows a Cuntz algebra may occur as a quotient even for a finitely presented MF group; this proves that it can never occur unitally inside a nonzero algebraic group-ring corner, precisely separating the useless quotient bridge from the potentially useful hereditary bridge.
  nonhyperlinear-normal-augmentation-corner-kills-mf: that accepts a no-CE algebra which may have non-CE tracial states and turns its finite-normal corner map into non-MF; this proves that a traceless Cuntz/Leavitt algebra cannot supply that corner map at all.
artifacts:
  - research/group-algebra-corner-canonical-trace-proof.md
---

**ESTABLISHED TRACIAL CORNER FIREWALL.**  Let `G` be any group, let `n` be
finite, and let

```text
0!=p=p^*=p^2 in M_n(C[G]).                                  (GCT1)
```

Then the algebraic corner `pM_n(C[G])p`, with identity `p`, has a tracial
state obtained by normalizing the canonical coefficient trace.  Consequently
no unital star algebra with no tracial state admits a unit-preserving star
homomorphism into this corner.

In particular, neither the algebraic complex Cuntz algebra nor any complex
binary Leavitt star algebra satisfying

```text
s_i^*s_j=delta_(ij)1,         s_0s_0^*+s_1s_1^*=1           (GCT2)
```

maps unitally into a nonzero complex group-algebra corner.  The original
characteristic-two binary Leavitt algebra is excluded even earlier: a unital
map into a characteristic-zero corner would send `0=2*1` to `2p!=0`.

This closes the direct stable-finiteness bridge for the binary-Leavitt/unit
group route.  A Cuntz/Leavitt one-sided inverse may occur in a C-star
**quotient** of a full group C-star algebra, but
`properly-infinite-cstar-quotient-is-compatible-with-fp-mf-group` shows that
such a quotient does not obstruct MF.  Placing the inverse in an algebraic
subcorner would make stable finiteness load-bearing, but `(GCT1)--(GCT2)`
show that this placement is impossible for every group.

The finite-normal augmentation-corner criterion therefore cannot be
instantiated with the traceless Leavitt or Cuntz algebra.  Its input must
have at least one tracial state while having no Connes-embeddable tracial
state; finite BCS algebras from non-CE correlations have exactly that
different profile.  Replacing them by the binary Leavitt one-sided inverse
is not a shortcut.

No Property `(T)`, approximation theorem, literature theorem, or Lean input
is used.

DERIVATION
group-algebra-corner-canonical-trace-proof
