---
rg: 2
id: hilbert-embeddable-amplification
kind: claim
title: Separation is free in the Hilbert embeddable class, and Glebsky's cap is replaceable
distinct_from:
  hilbert-embeddable-length-hyperlinearity: that converts a Hilbert embeddable witness into unitary microstates; this manipulates lengths inside the class before any conversion, and is what makes the separation constant a non-issue there.
  hilbert-embeddable-witness-for-kun-thom-wreath: that asks whether the wreath has such a witness; this removes two of the constraints that question was thought to carry.
  glebsky-manufactured-invariant-length: that records what Glebsky's Lemma 3 constructs; this says which parts of that construction are load bearing for embeddability and which are not.
---

Let `ell` be a Hilbert embeddable invariant length on a finite group,
`0 <= ell <= 1`, and for an integer `r>=1` put

```text
ell_r = 1 - exp(-r ell).
```

1. **Amplification.**  `ell_r` is again a Hilbert embeddable invariant length
   bounded by `1`, with `ell_r <= r ell` everywhere and
   `ell_r >= 1 - exp(-rc)` wherever `ell >= c`.  So a witness with defect
   `<= delta` and separation `>= c` becomes, on replacing `ell` by `ell_r`
   with `r = ceil(delta^(-1/2))`, a witness with defect `<= sqrt(delta)` and
   separation `>= 1 - exp(-c delta^(-1/2))`.  **Any fixed positive separation
   amplifies to `1 - o(1)`**, so the separation constant in the definition of
   weak soficity carries no content for Hilbert embeddable witnesses; only
   `ell != 0` on the elements to be separated does.
2. **This is exactly Glebsky's Lemma 11, transported.**  If `exp(-ell) = tr rho`
   for a unitary representation `rho`, then `exp(-r ell) = tr(rho^(tensor r))`,
   so `ell_r` is the length of the `r`-th tensor power of the realizing
   representation.  Glebsky's amplification for the sofic case is the same
   identity for the permutation representation: `1 - ||h||_Hamming` is the
   normalized trace of the permutation matrix, and the product action on
   `[m]^r` multiplies it.  The trace here is real and positive by Schoenberg,
   so the phase collapse that defeats naive tensor amplification in the
   unitary group — equal powers for `1` and `i*1` — cannot occur.
3. **The cap is replaceable.**  Glebsky's manufactured length
   `min{d(1,h)/n, 1}` may be replaced throughout by

   ```text
   1 - exp(-d(1,h)/n),
   ```

   which is bounded by `1`, equals `1-exp(-1/n) ~ 1/n` on the error set, and
   is at least `1-exp(-1) > 0.63` on the `n`-separated set — comfortably
   above the `1/2` the definition asks for.  Unlike `min{.,1}`, which is not
   a Bernstein function, `t |-> 1-exp(-t)` is one, so this replacement
   **preserves conditional negative definiteness** from the underlying word
   metric.
4. **Consequent reduction.**  Glebsky's construction yields a Hilbert
   embeddable witness whenever the conjugation-invariant word metric
   `d_(Gamma(H,X^H))` is itself conditionally negative definite.  Neither the
   cap nor the separation constant obstructs; the whole question is the
   uncapped word metric.

The cap is therefore not load bearing for separation and not load bearing for
the diameter bound — only for the fact that it is not Bernstein.  What cannot
be done is to *delete* it, leaving an unbounded length; what can be done is to
replace it by a Bernstein cap with the same profile.
