---
rg: 2
id: regular-mf-symmetric-doubles-are-regular-mf
kind: claim
title: Symmetric doubles preserve regular operator-MF realizations
distinct_from:
  symmetric-double-weak-mf: that records only the group-level MF conclusion for a residually finite base; this retains the regular character and allows any base already carrying a regular-MF realization.
  regular-mf-central-hnn-closure: that is the stable-letter analogue; this treats an amalgamated double over an arbitrary subgroup.
---

If `G` is regularly operator-MF realized and `H<=G`, then the symmetric double

```text
G *_H G
```

is regularly operator-MF realized.

Indeed, start with the MF C-star algebra `A` and regular trace realizing `G`,
and put `B=C*(H)<=A`.  Shulman's symmetric-amalgam theorem makes
`A *_B A` MF.  The regular trace maps this universal amalgam to the reduced
von Neumann amalgam

```text
L(G) *_(L(H)) L(G).
```

Its conditional expectation kills every group unitary outside `H`, so the
reduced amalgam normal form assigns trace zero to every nonidentity reduced
word.  Hence the abstract double embeds in the MF algebra and the pulled-back
trace is its regular character.
