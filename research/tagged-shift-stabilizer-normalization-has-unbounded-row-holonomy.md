---
rg: 2
id: tagged-shift-stabilizer-normalization-has-unbounded-row-holonomy
kind: claim
title: A stabilizer-normalized tagged shift cannot make both canonical row occurrences bounded-area pair charts
distinct_from:
  binary-leavitt-tagged-shift-table-has-centralizer-collisions: that exact table evades the fixed-column and injective-fibre fences; this rules out only the proposed repair by a private-tag pair transporter which fixes one row and normalizes the other.
  two-transitive-occurrence-sections-have-unbounded-pair-holonomy: that proves the two endpoint holonomies cannot both range over finite sets; this uses finite-mark commutator-area properness to show that bounded row-chart comparisons would force exactly that forbidden finiteness.
artifacts:
  - research/binary-leavitt-bounded-area-chromatic-code.md
---

**ESTABLISHED STABILIZER-CHART NO-GO.**  Let `Gamma=<S|R>` be finitely
presented and let `beta_0,beta_1` represent nontrivial finite-order elements.
Suppose finite address packets `X` have directed pair sets
`P subset {(x,y):x!=y}` of unbounded out-degree, canonical row words `c_x`,
two role sections `sigma_(ell,x)`, and simultaneous pair transporters
`g_(x,y)`.  Assume the elements represented by the `c_x` are pairwise
distinct and one constant `B` gives the two canonical role names

```text
Area_R(c_x (sigma_(ell,x) beta_ell sigma_(ell,x)^(-1))^(-1))<=B,
                                                               (TSH1)

g_(x,y) beta_0 g_(x,y)^(-1)=c_x,
g_(x,y) beta_1 g_(x,y)^(-1)=c_y                         ((x,y) in P) (TSH2)
```

There is no constant `A` for which both pair-chart comparisons

```text
Area_R(c_x (g_(x,y) beta_0 g_(x,y)^(-1))^(-1))<=A,
Area_R(c_y (g_(x,y) beta_1 g_(x,y)^(-1))^(-1))<=A        (TSH3)
```

hold for every `(x,y) in P` in all the packets.  In particular, the two
canonical row occurrences cannot both be literal free-word conjugates of
two fixed pair-cell rows; literal equality would give `(TSH3)` with zero
area.

This applies to the proposed stabilizer repair of the third-address tagged
binary-Leavitt shift table.  The elementary rows over `F_2` are nontrivial
involutions.  A transporter can be chosen to fix the source row, normalize
the target row, and--after choosing the private tag--normalize
`H_(ij)=B_i+D_(ij)` as group elements.  But fixing the source merely makes
the first comparison in `(TSH3)` free.  The target comparison is necessarily
unbounded over the growing shift packets.  The private tag changes only
the column coefficient, so it cannot change this row-holonomy obstruction.

The conclusion does **not** refute the exact tagged commutator table and does
not prove that its edge filling areas diverge by every possible diagram.  It
rules out precisely the attractive finite-prototype compiler in which one
pair-dependent stabilizer transporter is supposed to turn both the diagonal
and edge discrepancies into literal conjugates without paying a
pair-to-canonical row comparison.

No Property `(T)`, Kazhdan input, matrix approximation, trace, or literature
theorem is used.

DERIVATION
tagged-shift-stabilizer-holonomy-proof
