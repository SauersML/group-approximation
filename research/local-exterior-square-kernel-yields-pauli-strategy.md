---
rg: 2
id: local-exterior-square-kernel-yields-pauli-strategy
kind: claim
title: A locally rank-one pair of code sections yields an exact Pauli strategy
distinct_from:
  two-copy-overlap-consistency-has-pauli-cycle-countermodel: that is the concrete bounded-degree expander instance; this identifies the general algebraic obstruction.
---

ESTABLISHED.  Let a binary linear code be presented by local views
`C_j <= F_2^{S_j}`, with global section space

```text
C = {u in F_2^E : u|S_j in C_j for every j}.
```

Suppose `u,v in C` are globally independent but

```text
rank{u|S_j,v|S_j} <= 1                                      (LES1)
```

for every local view.  Then there is an exact two-dimensional reflection
strategy satisfying every local codeword test and every overlap-consistency
test, although some two global coordinate reflections anticommute.

Consequently, a same-Hilbert operator decoder requires injectivity of the
local restriction map on decomposable exterior squares:

```text
u wedge v |-> ((u|S_j) wedge (v|S_j))_j.                    (LES2)
```

Uniform robust decoding requires the quantitative strengthening

```text
Pr_(e,e')[u_e v_e' + v_e u_e' = 1]
  <= omega(Pr_j[rank{u|S_j,v|S_j}=2]),                      (LES3)
```

with the sampling measures induced by the bounded template and with
`omega(t)->0` independent of the code length.  Thus `(LES3)` is a necessary
classical shadow of the missing quantum agreement theorem.  It is stronger
than ordinary syndrome or agreement expansion and detects exactly the first
Pauli/noncontextuality obstruction.

