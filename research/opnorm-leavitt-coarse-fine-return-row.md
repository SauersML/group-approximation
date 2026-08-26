---
rg: 2
id: opnorm-leavitt-coarse-fine-return-row
kind: claim
title: Recover one operator-norm coarse-to-fine return row on a common Leavitt prefix carrier
distinct_from:
  paired-same-reservoir-boundary-lemma: that is the normalized-HS boundary ledger over the first N binary branch steps, on positive-density paired sectors, with a leakage alternative; this is ONE operator-norm row at ONE cell, with no density, no depth parameter and no alternative -- a strictly stronger estimate over a strictly smaller scope, and by opnorm-return-row-cannot-come-from-an-hs-ledger the two cannot be substituted for each other.
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that is the established rank consequence once such a row is in hand, together with the exact Leavitt construction of the return word; this asks for the row itself, from the presentation, in the operator norm.
  coherent-heisenberg-multiplicity-decoder: that asks a positive-density normalized-HS microstate to carry a coherent Leavitt multiplicity module and feeds the tracial Hilbert-hotel endpoint; this asks for no module, no coherence across depths and no density, only that two adjacent packets share one carrier.
  corona-coefficient-module-decoder: that assembles finite root multiplicity germs into a finitely generated projective corona module over the coefficient ring; this reconstructs no part of the coefficient ring and stays inside one finite coordinate.
  self-copy-kadison-kastler-checksum: that asks for a Kadison-Kastler-type proximity between the parent and child generated algebras; this asks only that two matrix-unit packets have approximately the same identity, which is an additive statement about two operators rather than a proximity of algebras.
  binary-leavitt-atomic-morita-return: that bypasses exact M2/M4 packet ranks and asks for four coefficient operators satisfying two inverse rows plus completeness on the prescribed root atom; this asks for two exact packets on one carrier and one vanishing support row.
---

**OPEN.**  Work in the binary-Leavitt Steinberg presentation `<S|R>` of
`St_20(R)`, with the distinguished root `z=x_13(q)`, `q=s_1t_1`.  Fix, once
and for all:

* the depth-one prefix matrix units `e_ij=s_it_j` (`r=2`) and the depth-two
  prefix matrix units `f_(u,v)=s_ut_v` (`s=4`) of `(CFI5)`;
* the crossed prefix coefficients `x=s_(00)t_0`, `y=s_0t_(00)` and the fixed
  three-elementary partial-swap word `J_x` of `(CFI8)`/`(CFI9)`.

Produce a modulus `omega(t) -> 0`, **independent of matrix dimension**, such
that every finite-dimensional operator-norm microstate `U` with
`Def_R(U)<=t` and `||z(U)-I||_op` bounded below admits a **nonzero**
projection `P` carrying exact depth-one and depth-two prefix matrix-unit
systems with the **same** identity `P`, coarse minimal corner `e_00` and its
designated fine descendant `f_(00,00)`, such that

```text
||(1-f_(00,00)) J_x(U) e_00||_op <= omega(t).              (OPLR)
```

Establishing this closes the goal `property-t-free-leavitt-full-mf-radical`
through `property-t-free-leavitt-via-opnorm-return-row`, with no property
`(T)`, no trace, no density and no stability hypothesis anywhere.

## What is already supplied, so that the residue is visible

* The **exact chart**: `iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart`
  gives the full `2^n by 2^n` active-corner isomorphism, not merely a
  one-sided self-embedding.
* The **exact bridge and its word**:
  `one-coarse-to-fine-prefix-isometry-closes-the-reservoir` gives
  `yx=e_(0,0)`, `xy=f_(00,00)` and the fixed three-elementary `J_x`, together
  with `J_x e^ J_x^* = f^` on the stabilized selectors `(PSR7)`.
* **Exactification and the common rotation**:
  `opnorm-packet-exactification-is-dimension-free`.
* The **endpoint**: `rank-deficient-return-row-has-operator-norm-one` and
  `authenticated-coarse-fine-return-forces-mf-collapse`.
* **Normal generation**: `full-leavitt-idempotent-defect-saturation` puts one
  complete root subgroup, hence all of `St_20(R)`, in `<<x_13(q)>>`.

The residue is therefore exactly one thing: **the two packets must be shown
to sit on one carrier.**

## Attempts

* **The exact model says nothing, by construction.**  Once both packets are
  exact on a common nonzero `P`, `rank-deficient-return-row-has-operator-norm-one`
  gives `||(1-f)Je||_op=1` for *every* unitary `J`, `J_x` included.  So there
  is no model realizing `(OPLR)`, no near-miss to measure, and no numerical
  evidence to gather.  The claim is provable only as a derivation from the
  relators, and its antecedent is empty once proved.  Any reported "progress"
  that consists of exhibiting better carriers is not progress.
* **Exactification is not the obstacle, and was mistaken for one.**  The
  audit that proposed this target listed operator-norm exactification of the
  fixed packet as a hypothesis.  It is free:
  `opnorm-packet-exactification-is-dimension-free` supplies it with a modulus
  depending only on the packet sizes, and supplies the common carrier too --
  *given* that the two approximate packet identities are already close.
* **The obstacle is additive, and the presentation cannot state it.**  In the
  Leavitt ring both packets sum to the active identity `A`.  In a
  Steinberg/root presentation, coefficient addition is encoded as
  multiplication inside a root subgroup and never as an operator sum, so no
  relator asserts `sum_i e_ii = sum_(u,v) f_(u,u)`.  This is the firewall
  already recorded by `factoriality-does-not-finitize-leavitt-root-data`,
  `finite-root-algebra-forces-steinberg-triviality` and
  `complex-hyperlinear-leavitt-idempotent-mismatch`, and `rectangular-escape`
  is precisely the model in which the two identities differ by trading label
  dimension against spectator multiplicity.  Every previous attack on this
  seam -- typed Steinberg triangles, Clifford covariance, the controlled fine
  reflection -- dies at the same place, as `paired-same-reservoir-boundary-lemma`
  records at length.
* **The entire normalized-HS ledger is unavailable as an input.**
  `opnorm-return-row-cannot-come-from-an-hs-ledger` shows that a
  trace/Reynolds/superrank/energy estimate bounds `||.||_2` and is therefore
  *forced* to be consistent with `||.||_op=1` on a low-density carrier.  So
  the balanced-Whitehead checksum, the quarter-trace floor, the superrank
  orientation law and the cyclic row spread cannot be reused here, however
  they are recombined.  This kills the tempting reading of the proposing
  audit, which described this target as a smaller version of the HS one; it
  is smaller in scope and strictly stronger in norm.
* **The selector cannot be a group-algebra projection.**  The regular
  representation of `St_20(R)` carries a faithful finite trace and sees the
  marked root, so any functorial group-algebra construction of the carrier
  would prove too much.  The carrier must be selected *inside* the finite
  matrix coordinate -- from the multiplicity algebra of an exactified packet
  -- which is what makes the target operator-norm-native rather than a
  corollary of the existing tracial calculus.
* **Adaptive prefix atoms plus Thompson simplicity do not supply the row.**
  `adaptive-prefix-atom-rank-return-does-not-close-opnorm-row` separates the
  three tempting steps.  Operator distance below one preserves rank but does
  not identify projections.  A growing atom orbit may be an exact orthogonal
  path whose first return grows with matrix dimension.  And absence of finite
  actor actions applies only after one has produced a total action on one
  finite invariant PVM; pointwise covariance on every fixed atom does not
  control the coordinate-dependent frontier.  Producing that invariant PVM
  with uniform covariance is the missing global exactification statement,
  not a consequence of simplicity.  Freezing a finite invariant packet
  instead lands in the Morita-neutral model of
  `binary-leavitt-finite-actor-minimal-atom-dichotomy`.
* **Remaining live probe.**  The adaptive-atom attack above does not address
  additive-identity recovery in the operator norm.  The nearest live
  operator-norm machinery is `conjugacy-addressed-opnorm-challenges-are-lossless`
  (literal conjugates of root discrepancies are address-lossless in operator
  norm) and `opnorm-coordinatewise-capacity-diagonal` (a frozen coordinate is
  defeated by a sufficiently large challenge).  A first concrete probe: use
  the off-diagonal corners of the `2 by 2` chart `(PSR1)` to build closed
  loops through both packets and ask whether the loop defect controls
  `||sum_i e_ii - sum_a f_aa||_op`, which is the one quantity `(EXA3)` needs.

* **The authenticated support-return odd loops do not supply the row.**
  `support-return-odd-loops-do-not-imply-atomic-return` keeps the two literal
  `J_i=W_i(Z_iH_iZ_i)W_i` occurrences, their full transported-chart
  covariance, their exact two-pair intersection and the native braid in a
  finite marked model.  If those rows implied a common depth-one/depth-two
  carrier and vanishing leakage, the exact norm-one rank floor would fail in
  that model.  Hence a new coefficient-completeness-to-mark relation is
  required; support-return recombination alone cannot recover the missing
  additive packet identity.
* **A nonzero adaptive cut inside the free prefix orbit still has unit
  leakage.**  `free-s3-atom-has-unit-opnorm-leakage` puts the mark at `-1`
  on the full six-dimensional active carrier and shows that every
  nonidentity authenticated prefix normalizer moves the chosen character
  atom orthogonally.  Every nonzero coordinate-dependent subprojection has
  return leakage exactly one.  A proof of `(OPLR)` must use a relation
  outside this finite normalizer menu which forces identity action on the
  selected type or rules the type out.
* **Literal fine-idempotent biaction still does not wordize its support.**
  `fine-idempotent-biaction-return-has-gl10-model` starts from the actual
  row-two factors `a_2=s_1t_00`, `b_2=s_00t_1`, exposes their reverse product
  `e_00=s_00t_00` as one literal root commutator, and then authenticates both
  absorption identities `e_00s_00=s_00` and `t_00e_00=t_00` on the same
  named Morita occurrences.  The entire table, together with both prefix
  actors, order-seven heads and the marked-center return, still has an exact
  marked `GL_10(F_2)` model.  Thus the next mixed row must attach this
  coefficient occurrence to a spectral support incidence (or use full
  completeness to exclude that type); another multiplication/action return
  for the fine idempotent cannot imply `(OPLR)`.
