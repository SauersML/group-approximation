---
rg: 2
id: kt-majorana-wall-certifies-macroscopic-actor-instability
kind: claim
title: A full-packet Majorana wall quantitatively certifies macroscopic Laurent-actor instability
distinct_from:
  kt-local-actor-correction-pays-majorana-return: that gives the lower bound on the returned anticommutator after a genuine actor correction is supplied; this solves that inequality for the correction distance and records the same-dimensional and bounded-amplification instability consequences.
  kt-kh-laurent-interface-is-locally-hs-unstable: that gives actor-only bad microstates abstractly from local HS instability; this says any microstate carrying the full Majorana wall is itself a uniformly far, positive-density bad actor microstate.
---

Fix the `q=2`, `r=d=3` Laurent elementary actor `E`, the finite Kazhdan
packet `K` for `Gamma`, the mixed return `h`, and its Kazhdan constant
`kappa_K`.  For matrices `u_s`, `s in K`, `u_h`, and a self-adjoint
involution `c`, put

```text
delta=max_(s in K)||[c,u_s]||_2,
d=u_h c u_h^*,
a=||cd+dc||_2,
C_K=8/kappa_K+4.                                      (MWI1)
```

Let

```text
Delta_(K,h)(u)=inf_rho max_(g in K union {h})||u_g-rho(g)||_2, (MWI2)
```

where `rho:E->U(D)` ranges over genuine representations in the same matrix
dimension.  Then

```text
Delta_(K,h)(u)
 >= [2-a-(4/kappa_K)delta]_+/C_K.                      (MWI3)
```

Thus an asymptotic full-packet Majorana wall (`delta->0`, `a->0`) is not
merely a qualitative failure of actor correction: its restriction to the
fixed window `K union {h}` stays at normalized-HS distance at least
`2/C_K` from every genuine Laurent-actor representation.

The conclusion survives every bounded amplification.  Pad the tuple and
`c` by identities from dimension `d` to `D`, put `q=d/D`, and let `rho:E->U(D)`
be genuine.  If its `K union {h}` distance from the padded tuple is
`epsilon`, then

```text
epsilon >= [2-2sqrt(1-q)-sqrt(q)a
                 -(4/kappa_K)sqrt(q)delta]_+/C_K.      (MWI4)
```

Consequently, if `delta,a->0` and `D/d<=A<infinity`, every such correction
has asymptotic distance at least

```text
[2-2sqrt(1-1/A)]/C_K > 0.                              (MWI5)
```

In particular, `o(d)` padding leaves the lower bound `2/C_K`.  A putative
Majorana countermodel therefore cannot hide its actor instability in a
microscopic summand or remove it by ordinary flexible HS stabilization.  To
evade `(MWI5)`, an exactification must use an amplification factor tending to
infinity.  This is only a necessary condition on a countermodel; it neither
constructs one nor proves the missing actor-defect modulus.

DERIVATION
kt-majorana-wall-macroscopic-instability-proof
