---
rg: 2
id: long-cyclic-return-holonomy-annihilates-every-carrier
kind: claim
title: Haar-like cyclic return holonomy annihilates every model-dependent fixed carrier
distinct_from:
  verifier-controlled-two-cycle-is-existentially-loss-blind: that constructs arbitrary return holonomy and defeats fixed localized moment tests; this proves that long cyclic choices defeat every possible model-dependent return carrier, not only carriers named by the controller.
  one-holonomy-word-controllers-are-free-or-torsion: that classifies common-orientation finite relators; this analyzes the free branch without assuming any algebraic or spectral form for the proposed holonomy-dependent carrier.
  unnamed-positive-density-fixed-space-is-terminal: that turns a positive unnamed fixed carrier into a nonhyperlinearity contradiction; this is the complementary finite-model theorem showing that Haar-like holonomy permits no such carrier.
  recursive-gauge-verifier-has-product-density-escape: that loses common density by tensoring independent verifier levels; this already kills a carrier inside one positive-density level whenever its return holonomy is asymptotically Haar.
---

**ESTABLISHED.**  Let `(M_n,tau_n)` be finite tracial matrix algebras, let
`E_n` be projections with

```text
liminf_n tau_n(E_n)=beta>0,                              (LCH1)
```

and let `A_n` be unitaries reducing `E_n`.  Normalize the corner trace by
`tau_(E_n)=tau_n/tau_n(E_n)`.  Assume the return holonomy is asymptotically
Haar on that corner:

```text
tau_(E_n)(A_n^k)->0                 for every fixed k!=0. (LCH2)
```

Then for **every** sequence of contractions `X_n=E_nX_n`, with no
measurability, spectral, word, or functorial hypothesis,

```text
||(A_n-1)X_n||_(2,n)->0
       implies
||X_n||_(2,n)->0.                                      (LCH3)
```

In particular, take `A_n` to be regular cyclic shifts of orders tending to
infinity.  Thus any verifier/two-cycle controller which admits arbitrarily
long cyclic return-holonomy completions cannot be repaired by choosing an
`A`-dependent positive-density carrier after seeing the matrix model.

For the Fanizza two-cycle, `w^2|_(E_n)=A_n`.  Hence the only surviving
non-tensorial controller must eliminate these long cyclic completions with a
dimension-independent relator cost tied to the BCS payload.  Merely making
the carrier nonlinear in `A`, or choosing it adaptively from the complete
matrix tuple, does not escape.

