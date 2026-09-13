---
rg: 2
id: clocked-search-machine-halts-universally-exactly-on-inf
kind: claim
title: A uniform clocked Minsky search machine halts from every configuration iff its index has infinite domain
distinct_from:
  pumped-halting-clocked-minsky-group-is-residually-finite: that turns universal halting into residual finiteness; this is the computability switch that makes universal halting track INF.
---

ESTABLISHED (unreviewed).  There is a computable map `e |-> M_e` to simple,
deterministic, clocked Minsky machines such that

```text
e in INF  ==>  every forward computation of M_e, from every configuration, is finite;
e in FIN  ==>  some configuration of M_e has an infinite forward computation.
```

`M_e` compiles the loop

```text
L0: E := e; Z := CHECK(E, S, N)
L1: if Z > 0 stop; else S := S + 1; goto L0
```

where `CHECK` is a LOOP program (Meyer--Ritchie) for the primitive recursive
predicate `|W_(e,S)| > N`.  It restores `E, S, N` and initializes its work
registers.

- Every compiled LOOP construct terminates from any register contents: its
  loop counters are fresh and only decremented.
- On `INF`, after the current construct finishes, the rounds test
  `|W_(e, S_0 + t)| > N_0` for `t = 0, 1, ...`, and some round succeeds.
  Rewriting `E` each round makes garbage harmless.
- On `FIN`, the configuration at `L0` with `N = |W_e|` and all else zero
  diverges.

DERIVATION
[[clocked-search-machine-halts-universally-exactly-on-inf-proof]]
