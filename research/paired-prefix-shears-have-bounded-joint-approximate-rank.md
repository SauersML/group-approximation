---
rg: 2
id: paired-prefix-shears-have-bounded-joint-approximate-rank
kind: claim
title: Finitely many paired prefix shears still have dimension-independent joint approximate rank
distinct_from:
  bounded-prefix-decision-cost-forces-bounded-approximate-rank: that treats one Boolean phase table; this treats a finite tuple read from one prefix transcript and bounds their joint row space.
  leavitt-prefix-boundaries-do-not-split-additive-character-mass: that gives one exact additive character detecting all levels; this gives an approximate-rank escape even after finitely many paired root coordinates are used.
  paired-same-reservoir-boundary-lemma: that asks for a Gram/range or support-selector payment in matrix coordinates; this proves why replacing that payment by finitely many prefix-computable commutator phases cannot work.
---

Let

```text
K_n=(K_n^1,...,K_n^b):{0,1}^n x {0,1}^n -> F_2^b       (PPR1)
```

be read by one deterministic synchronous prefix procedure with stopping
time `L_n`.  If

```text
sup_n E L_n <= C,                                       (PPR2)
```

then, for every `epsilon>0`, there are tables `K_n'^j` which differ from
all the `K_n^j` only on one set of at most `epsilon 2^(2n)` input pairs and
whose horizontal concatenation satisfies

```text
rank_F2 [K_n'^1 | ... | K_n'^b]
   <= 2^ceil(C/epsilon).                                (PPR3)
```

In particular

```text
sum_j rank_F2(K_n'^j) <= b 2^ceil(C/epsilon).           (PPR4)
```

The second-moment version replaces `C/epsilon` by
`sqrt(C_2/epsilon)`, exactly as in the one-table theorem.

Consequently a fixed finite packet of paired Steinberg shear **phase
tables**, if its outputs are determined by one bounded-average classical
prefix transcript, still has bounded robust symplectic rank.  Applying
`low-rank-weyl-tables-have-polynomial-models` to the single concatenated
table preserves one common separated central mark and the canonical
one-letter/two-letter moments while making the mean shear defect arbitrarily
small in dimension polynomial in the label count (for fixed target error
and fixed `b`).  Formally, pad the `D by bD` concatenation by zero row blocks
to a `bD by bD` square table, apply the theorem once, and restrict back to
the original row family.

Thus pairing finitely many root coordinates does not charge the rare deep
prefix cells merely by turning their outcomes into several commutator
phases.  A live affine-Leavitt boundary proof must instead use genuinely
non-phase matrix-coordinate data--the same-reservoir Gram/support selector
of `paired-same-reservoir-boundary-lemma`--or explicitly overweight the
deep cells with depth-dependent constants.  This does not refute the weaker
canonical target `affine-leavitt-boundary-shear-payment`, whose constants
and finite windows may grow arbitrarily with depth; it rules out a uniform
bounded-average paired-phase proof of that target.
