---
rg: 2
id: agent-aggregate-escape-atomwise-seed-flip-saturates
kind: claim
title: The Pauli seed flip saturates the marked sector after one aggregate escape
distinct_from:
  index-two-reynolds-atoms-have-orthogonal-hnn-transports: that moves assignment Reynolds differences to orthogonal character atoms; this uses the existing Pauli seed flip on the whole aggregate and proves that the ensuing shared-variable hull destroys renewal.
  central-sign-reynolds-first-hit-compiler: that seeks persistent active carriers and summable exits; this rules out taking the whole opposite Pauli seed half as the first-hit destination module.
  finite-depth-role-packed-aggregate-escape: that allows arbitrary non-equivariant words along the reached chain; this rules out the natural contextwise equivariant realization of its first row.
---

**ESTABLISHED NO-GO FOR THE NATURAL ROOT COMPILER.**  Keep the corrected
Pauli seed involutions `B,C`, put

```text
Q_+=(1-J)(1+B)/4,             Q_-seed=(1-J)(1-B)/4,    (ASF1)
```

and enumerate the role-packed forbidden summands as `R_iP_i`.  The seed
relations and its commutation with the shared BCS and role tuples give

```text
CBC^*=BJ,       [C,R_i]=[C,P_i]=1.                    (ASF2)
```

Let

```text
e_i=Q_+ R_iP_i,                 e_i'=Q_-seed R_iP_i.   (ASF3)
```

Consequently the one existing group word `C` simultaneously transports
every summand:

```text
C e_i C^*=e_i'.                                        (ASF4)
```

The `e_i'` are pairwise orthogonal, lie in the opposite seed half, and

```text
D=sum_i e_i'=Q_-seed B_f.                              (ASF5)
```

Thus the original finite Pauli packet already gives a genuine first escape:
`D` is orthogonal to `Q_+` and has trace `tau(Q_+B_f)`.

Nevertheless its reducing hull is fatal.  By
`agent-aggregate-escape-forbidden-support-saturation`, the reducing hull of
`D` under the shared BCS and full role tuple is all of `Q_-seed`.  Hence the
next carrier prescribed by `reducing-hull-carry-forward-after-aggregate-escape`
is exactly

```text
Hull_Y(Q_+ join D)=Q_+ + Q_-seed=(1-J)/2.              (ASF6)
```

The approximate statement is dimension independent.  After fixed-packet
exactification, the transported aggregate is within
`delta=O(sqrt(E))` of `Q_-seed B_f`.  Therefore

```text
tau(Q_-seed-Hull_Y(D))=O(sqrt(E)).                     (ASF7)
```

For the resulting carrier `Q_1`, every projection `D_1<=(1-J)/2` with
`tau(D_1)=tau(Q_1B_f)+O(sqrt(E))` satisfies

```text
tau(Q_1D_1)
 >=tau(D_1)-tau((1-J)/2-Q_1)
 =tau(Q_1B_f)-O(sqrt(E)).                              (ASF8)
```

Since the robust gap makes `tau(Q_1B_f)` bounded below by a fixed positive
multiple of `tau(Q_1)`, `(ASF8)` contradicts any second-row estimate

```text
tau(Q_1D_1)<=(1-eta)tau(Q_1B_f)+C sqrt(E)              (ASF9)
```

with fixed `eta>0` along sufficiently accurate marked canonical
microstates.

Therefore atom naming, one-word Pauli transport, and a perfect first escape
do not suffice.  Renewal must transport the forbidden payload into a module
whose shared-algebra central support is proper, or must avoid closing under
the whole shared BCS/role algebra at that stage.  Merely adding fresh seed
signs repeats the same saturation after paying seed dilution.

DERIVATION
agent-aggregate-escape-atomwise-seed-flip-saturates via agent-aggregate-escape-atomwise-seed-flip-saturates-proof
