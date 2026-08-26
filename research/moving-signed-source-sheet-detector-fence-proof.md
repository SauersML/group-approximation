---
rg: 2
id: moving-signed-source-sheet-detector-fence-proof
kind: route
title: Compress the literal sheet detectors to the paid moving source and expose the missing Gram row
target: moving-signed-source-does-not-localize-paid-sheet-detector
requires:
  - paid-cut-has-moving-hecke-source-or-detector
  - row2-source-factor-detects-paid-pauli-sheet
  - el20-order-seven-heads-force-zero-common-hecke-reducing-cut
  - paid-t00-reynolds-cut-is-whitehead-reducing
  - paid-pauli-menu-has-two-row2-indistinguishable-sheets
  - primitive-native-hecke-relators-have-no-odd-mixed-occurrence
  - odd-native-s-factor-return-diamond-has-gl7-model
  - support-return-gives-gauged-native-loop
---

In the source alternative, `paid-cut-has-moving-hecke-source-or-detector`
produces a projection `R_0<=Q`; no additional property of `R_0` relative to
the sheet roots is asserted.  Apply the exact model `(SFD9)` from
`row2-source-factor-detects-paid-pauli-sheet`.  There

```text
Q(K_Q-1)Q=0,
K_Q=[A_1,H],
A_1Q=QA_1,
z=VK_QV^(-1),
zQ=-Q.                                                  (1)
```

Because `R_0<=Q`, equation `(1)` immediately gives

```text
(K_Q-1)R_0=0.                                          (2)
```

Conjugating `(2)` by either exact Hecke word gives `(MSD4)`.  Thus the
source extraction and the common-tail detector may both be exact while the
detector has zero displacement on the entire extracted source.  Notice
that `(1)` already assumes zero `H` leakage from `Q`; estimating that
leakage more sharply cannot change the conclusion.

For `K=[S_57,H]`, the established cube identity is global.  Inserting
`R_0+(1-R_0)` at each occurrence of `S_57` shows that every compressed
version contains terms bounded by

```text
||(1-R_0)S_57R_0||_2                                   (3)
```

and its reverse boundary.  There is no established upper bound for `(3)`.
The global comparison `[P_z]<=4[P_K]` contains no product or overlap term
with `Q`; it therefore cannot remove `(3)`.  Equivalently, at the level of
the displayed finite occurrence table, take the direct sum of a signed
character block (on which `Q` is nonzero and `K` is trivial) and an exact
regular block of the factor cube (on which `K` is nontrivial and `Q=0`).
Every displayed relation and global nontriviality statement survives, but
`Q(K-1)Q=0`.  A full-group proof must rule this segregation out by a new
mixed occurrence, not by repeating normal generation.

Finally `(PMH7)` is a lower bound for a sum of off-corner boundaries.  A
lower bound cannot be used as the vanishing source/range loss required by
a partial-isometry Gram authentication.  The word-conjugate range makes
the loss zero only tautologically and changes the reservoir frame.  This
proves the stated fence and isolates `(MSD7)` as the exact missing
relation-controlled transition.
