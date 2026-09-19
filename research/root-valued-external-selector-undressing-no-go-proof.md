---
rg: 2
id: root-valued-external-selector-undressing-no-go-proof
kind: route
title: Evaluate a root-transporter packet in its marked external-sign character
target: root-valued-overlap-does-not-undress-external-selector
requires:
  - root-valued-relative-transport-forces-cross-gram
---

The assignment `(RUD2)` respects every relation in `(RUD1)`: the two root
involutions commute, `h^2=1`, and both conjugation relations reduce to
`-1=-1`.  Hence it is an exact finite-dimensional representation with both
root-negative projections equal to the identity.

After taking the direct product of an arbitrary same-center packet with this
character, its packet operators and carrier are unchanged.  The operators
`S_1,S_2` commute with both `z,r` and `h` in the new tensor factor, so direct
conjugation gives `(RUD4)`.  Also

```text
N_1^*N_2N_2^*N_1
 =S_1^*hS_2S_2^*h^*S_1=F.                             (RUDP1)
```

The relative polar differs from the undressed relative polar only by the
central scalar `-1`, so its commutators with every source-Pauli operator are
identical.  Finally `N_2-S_2=-2S_2` on `F`; unitarity of `S_2|_F` gives

```text
||(N_2-S_2)P||_2^2
 =4||S_2P||_2^2=4tau(P),                              (RUDP2)
```

for every `P<=F`.  This proves the quantitative non-undressing statement.

The invocation of the established root-valued theorem is only to emphasize
that its promised overlap is present (indeed maximal) in this example.  The
countermodel does not dispute that theorem; it separates its conclusion
from native occurrence attachment.
