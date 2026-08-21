---
rg: 2
id: relative-c-sixth-sign-separation-proof
kind: route
title: Apply the free-product Greendlinger lemma to a four-syllable collision word
target: relative-c-sixth-protects-sign-double-cosets
requires: []
---

The free-product `C'(1/6)` Greendlinger lemma says that a nonempty freely
reduced word trivial in `(RC6-3)` contains a consecutive segment longer
than half of some defining relator.  The usual minimal reduced diagram proof
also proves that every free factor embeds.

Suppose `(RC6-4)` fails.  Then for some `h_X in H_X`, `h_Z in H_Z`,
`p_0 in P_0`, and `p_1 in P_1`,

```text
h_X p_0 h_Z = p_1.                                             (1)
```

After free reduction, the word

```text
h_X p_0 h_Z p_1^-1                                             (2)
```

is nonempty: the two `p` letters are distinct free generators and lie in a
factor different from `H_X,H_Z`.  Its free-product syllable length is at
most four.  If `(2)` were trivial in `G`, Greendlinger and `(RC6-2)` would
put at least five consecutive syllables of one relator on a word having at
most four syllables, impossible.  This proves `(RC6-4)`.

