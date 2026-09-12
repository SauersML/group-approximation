---
rg: 2
id: balanced-greendlinger-sign-separation-proof
kind: route
title: Peel pure equality cells and force three sign edges onto a two-sign boundary
target: balanced-greendlinger-separates-sign-cosets
requires: []
---

If `(BG3)` fails, choose among all freely reduced collision words

```text
u p_0 v p_1^-1,          u in F(D_X), v in F(D_Z),             (1)
```

and all reduced disk diagrams for them one of minimum area.  The two `p`
letters cannot freely cancel because the alphabets and the two sign sets are
disjoint.

The `C'(lambda)` Greendlinger lemma supplies a cell whose relator `r` has a
connected exterior interval of length strictly greater than

```text
(1-3 lambda)|r|.                                               (2)
```

This cell cannot be pure X.  Its exterior interval would lie wholly in the
X segment of `(1)`; removing the cell replaces that interval by another
X-word and produces a smaller-area diagram for another word of form `(1)`.
That contradicts the choice of the diagram.  The same argument excludes a
pure Z cell.

Hence the Greendlinger cell is mixed.  Its exterior interval lies on the
outer boundary `(1)`, so it contains at most the two outer `P` letters.
Condition `(BG2)` bounds its length by `beta|r|`, contradicting `(BG1)` and
`(2)`.  Thus no collision diagram exists.

This also explains why the proof is insensitive to arbitrary pure-cloud
relations: they only change the representatives `u` and `v` and are peeled
before any mixed cell is considered.

