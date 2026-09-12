---
rg: 2
id: jnvwy-exact-low-individual-degree-atom-decoding-proof
kind: route
title: Glue perfect line answers into polynomial-table atoms and decode each PCP bundle
target: jnvwy-perfect-answer-reduction-exactly-reflects-source-atoms
requires: []
---

Work first with the typed verifier in Figure 14.  Every question has a
positive self-loop carrying the equality test.  A perfect tensor strategy
therefore has the standard synchronous tracial representation; quotient by
the trace-zero ideal and restrict to the support to make the trace faithful.
The same reduction is standard for a synchronous commuting strategy, and a
faithful tracial model already has this form.  Detyping only adds the exact
type-consistency wrapper, so the argument applies before or after detyping.

Fix one of the six low-degree copies and, where relevant, fix its source
question data.  Write `P_u^a` for its point PVM and `R_ell^h` for a line
PVM.  If `u` lies on `ell`, perfect line--point acceptance and faithfulness
give

```text
P_u^a = sum_{h:h(u)=a} R_ell^h.                         (ED1)
```

Indeed both mismatch sums have trace zero; traciality turns them into the
squared `2`-norms of the two differences, and faithfulness makes the
coarse-graining identity exact.

The diagonal-line sampler of Section 7.1 chooses an index
`i in {1,...,m}`.  At `i=1`, `pi_(i-1)(v)=v`, so its support contains every
affine line (choose direction `v=y-x`) and every incidence on that line.
Thus any two point PVMs are coarse-grainings of one line PVM and commute.
All finitely many point PVMs consequently have the joint refinement

```text
E_f = product_u P_u^(f(u)),   f:F_q^r -> F_q.           (ED2)
```

On a nonzero atom `E_f`, `(ED1)` says that the restriction of `f` to every
axis-parallel line is represented by a univariate polynomial of degree at
most `d`.  Interpolate `f` uniquely by the reduced polynomial having degree
less than `q` in each variable.  Since `q>d`, uniqueness on every axis line
sets every coefficient of degree greater than `d` in each variable to zero.
Hence `f` is an individual-degree-`d` polynomial.  The inequality `q>d`
is immediate from Definition 10.22 (indeed its stronger condition
`(2+5d)m'/q<1/2` is used in Theorem 10.25).  The diagonal-line labels have
degree at most `rd`, as required for restrictions of an individual-degree
`d` polynomial.  Their only irrelevant residual freedom is on a
zero-direction singleton.

Apply `(ED2)` to the simultaneous sixth copy, with
`r=m'` and `m'+6` field values at every point.  Its nonzero atoms are exact
tuples of individual-degree-`d` polynomials

```text
(f_1,...,f_5,c_0,...,c_m').                             (ED3)
```

For `i=3,4,5`, the `POINT_i--POINT_6` check identifies the `f_i` evaluation
PVM with the corresponding individual `g_i` evaluation PVM at every point.
For `i=1,2`, the input-consistency check does the same between `POINT_6`
over an oracle question-pair and the individual input-table test over its
`i`-th source question.  Since the global polynomial PVM is the joint
refinement of its point evaluations, these equalities glue atomwise and
force

```text
f_i(x_1,...,x_5,o,w)=g_i(x_i),   i=1,...,5.             (ED4)
```

Equality here is equality as functions.  The reduced individual-degree
bounds are below `q`, so it is also polynomial identity; no alternate
finite-field representative survives.  Equations `(ED3)` and `(ED4)` are
exactly the proof format of Definition 10.23.

Now fix a source oracle question-pair and one nonzero global-table atom
`E_Pi`.  For each `z`, the `POINT_6` answer is the evaluation
`eval_z(Pi)`.  If `M_AR` rejected that view, `E_Pi` would lie under the
rejected-answer projection for the game check at `z`.  Perfect acceptance
makes that projection trace zero, so faithfulness would give `E_Pi=0`, a
contradiction.  Therefore the atom passes at every point, proving `(EAR2)`.

Since its PCP acceptance probability is `1>p_sound=1/2`, Theorem 10.25
applies atomwise and returns accepted padded source answers
`Delta(g_1),Delta(g_2)`.  Sum table atoms with the same decoded pair.  These
sums form the oracle joint-answer PVM.  Applying the same decoding
coarse-graining to the individual polynomial PVMs and using `(ED4)` gives
its exact marginals.  Every nonzero joint atom is accepted by the source
decider, so this is a perfect strategy for the oracularized source verifier;
forgetting the joint refinement gives a perfect strategy for the source
verifier.  All operations are coarse-grainings inside the original
measurement algebra, so tensor, commuting, and faithful-tracial model type
is preserved.

Nothing in this argument identifies two polynomial atoms with the same
decoded word, relates proof choices at different source atoms, or makes the
proof coordinates affine in that word.  The explicit off-Boolean-cube
modification `(EAR5)` shows that such uniqueness would be false.
