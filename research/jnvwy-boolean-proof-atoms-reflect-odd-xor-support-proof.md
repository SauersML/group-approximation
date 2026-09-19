---
rg: 2
id: jnvwy-boolean-proof-atoms-reflect-odd-xor-support-proof
kind: route
title: Add positive proof tables and decode their Boolean source cubes linearly
target: jnvwy-perfect-answer-reduction-reflects-affine-safety
requires:
  - jnvwy-perfect-answer-reduction-exactly-reflects-source-atoms
  - jnvwy-positive-perfect-proof-atoms-have-boolean-input-cubes
---

Suppose every positive support of a perfect answer-reduced model is
affine-safe, and form the exact decoded source model of
`jnvwy-perfect-answer-reduction-exactly-reflects-source-atoms`.  If one of
its source supports were affine-unsafe, there would be an odd list of
positive decoded source atoms

```text
(a^(1),b^(1)),...,(a^(2r+1),b^(2r+1))                 (BPR1)
```

which the source decider accepts while their componentwise xor `(a*,b*)`
is rejected.  Each decoded projection is a finite sum of global proof-table
atoms.  Choose a nonzero atom

```text
Pi^(j)=(g_1^(j),...,g_5^(j),c_0^(j),...,c_m'^(j))     (BPR2)
```

under each projection in `(BPR1)`.

Fix any `POINT_6` game-check point `z`.  The evaluation outcome
`eval_z(Pi^(j))` is a positive `POINT_6` marginal: its point projection
dominates the nonzero global atom.  For every `j`, choose a partner answer
on the fixed game-check edge whose joint projection with this marginal has
positive trace; one exists because the partner PVM sums to one.  Affine
safety of that joint output support says that the odd sum

```text
sum_j eval_z(Pi^(j)) = eval_z(sum_j Pi^(j))            (BPR3)
```

is also accepted together with the xor of the chosen partner answers.  The
oracle-side game check evaluates the PCP predicate on the `POINT_6` view and
therefore forces the view in `(BPR3)` itself to pass, independently of the
partner payload.  (All field elements are serialized in the verifier's fixed
`F_2` basis, so answer xor is exactly addition in the characteristic-two
field.)  This holds for every `z`, so

```text
Pi*=sum_j Pi^(j)                                       (BPR4)
```

is an everywhere-accepted literal low-degree PCP proof.

By `jnvwy-positive-perfect-proof-atoms-have-boolean-input-cubes`, every
`g_i^(j)` for `i=1,2` is Boolean on the Boolean cube.  Restriction is linear
and the field has characteristic two, hence

```text
Dec(g_i*)=xor_j Dec(g_i^(j)),  i=1,2.                  (BPR5)
```

The right side is the rejected source pair `(a*,b*)`.  On the other hand,
JNVWY Theorem 10.25 applies to the everywhere-accepted proof `Pi*` and says
that its decoded first two tables are accepted by the source decider.  This
contradiction proves `(PAR1)`.  The argument uses only finite sums and
coarse-grainings inside the original measurement algebra, so it preserves
the tensor, commuting, and faithful-tracial model class.
