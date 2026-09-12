---
rg: 2
id: kt-deleted-line-majorana-collapse-proof
kind: route
title: Restore the deleted line and apply the flexible genuine-actor return inequality
target: kt-deleted-line-instability-cannot-carry-majorana-wall
requires:
  - kt-local-actor-correction-pays-majorana-return
  - kun-thom-nonsofic-wreath
---

Becker--Lubotzky, Proposition 2.3 of *Group stability and Property (T)*
(JFA 2020, arXiv:1809.00632), gives the deleted-line maps and, for every
fixed generator `s`,

```text
||sigma_n(s)iota_n-iota_n tau_n(s)||_(2,k_n)->0.          (DLI5)
```

This is also Lemma 6.3 in Fournier-Facio--Gerasimova--Spaas, *Local
Hilbert--Schmidt stability* (J. Algebra 2025, arXiv:2307.13155), where it is
the input to the property-`(T)` local-instability proof.

Write `sigma_n(s)` in blocks for
`C^k_n=iota_n(C^(k_n-1)) direct_sum C`.  Equation `(DLI5)` says that its
upper-left block is close to `tau_n(s)` and its lower-left block is small.
Unitarity makes the upper-right block have the same Frobenius norm.  If
`alpha_(n,s)` is the scalar lower-right block, choose a phase
`lambda_(n,s)` closest to it.  Since

```text
1-|alpha_(n,s)|^2=||upper-right block||_F^2,
```

the scalar error is small as well.  Hence, on the fixed window
`K union {h}`,

```text
epsilon_n=max_g ||sigma_n(g)
                  -(tau_n(g) direct_sum lambda_(n,g))||_(2,k_n)->0. (DLI6)
```

The phases need not form a representation.  They are used only to compare
the padded matrices with the genuine representation `sigma_n`; because the
padded lamp is `c_n direct_sum 1`, every phase commutes with the added lamp
line.  Therefore the proof of flexible inequality `(LAC4)` applies verbatim
with these phases in place of identity padding.  The padded packet defect is
`sqrt(q_n)delta_n`, and the padded returned anticommutator is

```text
(c_n d_n+d_n c_n) direct_sum 2.
```

Substitution in `(LAC4)`, using `sqrt(1-q_n)=1/sqrt(k_n)`, proves `(DLI4)`.
Now `q_n->1`, `epsilon_n->0`, and `delta_n->0`, which gives `(DLI3)`.

For the explicit full actor, genuine representations `sigma_n` with
unbounded dimensions are available: `G` is infinite and residually finite
by Kun--Thom Theorem E, while property `(T)` gives only finitely many
irreducible representations in each fixed dimension.  Taking irreducible
constituents which separate successively new finite quotients yields
`k_n->infinity`, exactly as in the local-instability construction.
