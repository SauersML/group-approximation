---
rg: 2
id: checkpointed-syndrome-recursion-kills-depth-loss
kind: claim
title: A backward syndrome recursion with constant-horizon checkpoints loses no factor in the depth
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

**ESTABLISHED.**  Let `b_t >= 0` be bad syndrome weight at layer `t` and
`e_t >= 0` the nearby parent-Hamiltonian energy, and suppose the backward
estimate

```text
b_t <= L ( e_t + b_(t+1) ),        L >= 1.                      (BSR)
```

Suppose checkpoints are placed so that consecutive checkpoints are at
distance at most `r`, and at every checkpoint `c`

```text
b_c <= A e_c.                                                   (CKP)
```

Then for any `t` whose next checkpoint is `c`,

```text
b_t <= L^r ( sum_(s=t)^(c-1) e_s + A e_c ).                     (CK1)
```

In particular, when `r`, `A`, `L` are all `O(1)` the energy-to-syndrome loss
is **independent of the total circuit depth**: iterating (BSR) from a
terminal boundary through depth `D` costs `L^D`, and checkpointing replaces
that by `L^(O(1))`.

**The conclusion is already a local charge.**  (CK1) says
`b_t <= L' sum_(s in N(t)) e_s` with `L' = L^r max(1,A)` and
`N(t) = [t, c]` of width at most `r+1`.  That is exactly the hypothesis
consumed by `bounded-overlap-syndrome-energy-accounting`, whose overlap
constant is then `r+1`.  So checkpointing and the incidence lemma compose
with no intermediate step.

This lemma **does not produce the checkpoints**; supplying them is
`bounded-horizon-syndrome-anchor-exists`.  It also does not assert (BSR) for
any particular construction; that is
`backward-syndrome-recursion-holds-for-the-amplifier`.
