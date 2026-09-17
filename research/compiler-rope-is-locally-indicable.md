---
rg: 2
id: compiler-rope-is-locally-indicable
kind: claim
title: The compiler's positive rope R_e is locally indicable, hence left-orderable with unique products
distinct_from:
  mf-compiler-positive-branch-is-torsion-free: that proves torsion-freeness of the same groups from the torsion theorems for amalgams and HNN extensions; this proves the strictly stronger local indicability through a retraction whose kernel is a free product of subgroups of F_2 x F_2, which gives left-orderability and unique products as well.
  the-mikhailova-rope-object-card: that records the rope's presentation and known properties; this is a new structural theorem about the rope, and it moves the orderable cells of the atlas through the Rice criterion.
  twisted-rope-sofic-once-first-rope-sofic: that is the open soficity question for R_e; this is an orderability property of the same group, proved unconditionally.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `compiler-rope-is-locally-indicable-proof`.

Let `e in INF` and let

```text
Gamma_e = < K_e, v | [v, L_e] = 1 > = K_e *_(L_e) (L_e x Z),
R_e     = < Gamma_e x H, u | u(s,1)u^-1 = (s, tau_e(s)), s in S_e >,
```

be the first and twisted ropes of [[mf-safe-finite-presentation-compiler]], with `K_e` a finite product of
finitely generated free groups, `S_e = F *_(N_e) F^v`, and `H = B3(1)` the kernel of the exponent-difference
character of `F_2 x F_2`.  Then `Gamma_e` and `R_e` are **locally indicable**.

**Consequences.**  By Burns--Hale, `R_e` is left-orderable, and it has unique products.  So it is torsion-free,
and `K[R_e]` is a domain for every field `K`.  None of this depends on the seed, since on `INF` the output is
seed-independent.

**Why it matters for the atlas.**
- *The orderable cells.*  `R_e` is the one group whose soficity decides the sofic cell of
  [[finite-presentation-rice-criterion-via-the-fixed-positive-rope]].  So the finite-presentation completeness
  question for soficity and the left-orderable, locally indicable and unique-product nonsofic cells now meet in
  one explicit group: see `sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group`.
- *Hardness corollary* (proposed, not checked against the literature).  Apply the Rice criterion with
  `P` equal to left-orderable, locally indicable, unique product, or "`K[G]` is a domain", and with (C2) witnessed
  by `D = Z/2`.  Each of these is subgroup-hereditary, so each `P_fp` is `Pi^0_2`-hard on finite presentations.
- *Upper bound* (hand sketch).  Each failure has a `Sigma^0_2` witness: finitely many words that are nontrivial
  (a `Pi^0_1` condition) together with finitely many equalities (a `Sigma^0_1` condition).
  - Not left-orderable: by the Conrad--Ohnishi criterion, every sign choice puts `1` in the positive semigroup.
  - Not locally indicable: each generator of `A = <g_1..g_n>` has a power in `[A,A]`.
  - Not unique product: there are sets `A`, `B` of pairwise distinct words in which every product occurs twice.

  With the hardness corollary this would make left-orderability, local indicability and unique products
  `Pi^0_2`-complete on finite presentations.
- *Relation to the literature.*  The literature sweep in [[arithmetical-complexity-table-of-group-properties]]
  covers orderability only on recursive presentations (Bilanovic--Chubb--Roven).  It lists Lempp's
  torsion-freeness theorem and the MF theorem as the only finite-presentation cells.  So these would be further
  finite-presentation cells; this has not been re-checked against newer literature.
