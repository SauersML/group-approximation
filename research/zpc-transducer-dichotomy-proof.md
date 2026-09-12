---
rg: 2
id: zpc-transducer-dichotomy-proof
kind: route
title: Evaluate the gluing energy in canonical microstates of the marked solution group
target: zpc-transducer-is-exact-gluing-identity-or-nonhyperlinear
requires: []
---

Assume `J != 1` in `Gamma_L` and that `Gamma_L` is hyperlinear.  We prove (a)
of `(TGD1)`.

**1. Canonical microstates.**  Hyperlinearity gives unitary tuples `sigma_n`
on the LCS variables with defining-relator defect tending to zero and

```text
tr(sigma_n(g)) -> tau_Gamma(g)          for every fixed word g,
```

where `tau_Gamma` is the canonical trace.  This is the evaluation used in
`finite-subgroup-type-exclusion-is-already-nonhyperlinearity`.

**2. Pass to the marked corner.**
- Since `J != 1`, `tau_Gamma(J) = 0`.  So `sigma_n(J)` is an approximate
  central involution whose trace tends to `0`, and its spectral projection
  `p_n` near `-1` has normalized trace tending to `1/2` and almost commutes
  with every variable in normalized HS.
- Compress to `p_n`, replace `J` by `-I`, and exactify each variable to a
  nearby involution and each equation context to a commuting tuple.  Finite
  abelian groups are HS-stable, so the losses are dimension-free `o(1)`.
- By the solution-group correspondence recorded in
  `perfect-lcs-gap-implies-nonhyperlinear` (Slofstra--Vidick), this gives
  finite-dimensional strategies `S_n` of `L` with loss `epsilon_n -> 0`.
- Every fixed-word moment of `S_n` differs from the compressed microstate
  moment by `o(1)`.  Those converge to the canonical trace on
  `C[Gamma_L](1-J)/2`, normalized by `tau_Gamma((1-J)/2) = 1/2`.

**3. Evaluate the gluing energy.**  `D_glue` is a fixed finite sum of words,
so

```text
D_glue(S_n) -> 2 sum_(c,d,q) w_(c,d,q)
               tau_Gamma( (U_(c,q)-U_(d,q))^* (U_(c,q)-U_(d,q)) (1-J)/2 ).
```

`(CTX')` gives `D_glue(S_n) <= C epsilon_n -> 0`.  The weights are positive
and the canonical trace is faithful on `C[Gamma_L]`, so every summand
vanishes, that is `(U_(c,q)-U_(d,q))(1-J) = 0` in `C[Gamma_L]`.  This is (a).
The contrapositive gives (b) whenever (a) fails.  QED.

**Converse for type (a).**  If `y = (U_(c,q)-U_(d,q))(1-J)` vanishes in
`C[Gamma_L]`, then its lift to the free group algebra is a finite sum
`sum_i alpha_i u_i (r_i - 1) v_i` with relator words `r_i` and fixed words
`u_i, v_i`.  Evaluate on unitaries whose relators have squared normalized-HS
defect at most `delta`. The triangle inequality and unitary invariance of the
2-norm give

```text
||y||_2^2 <= (sum_i |alpha_i|)^2 delta.
```

For LCS strategies of loss `epsilon`, the standard correspondence gives
`delta = O(epsilon)`.  So type (a) transducers get the gluing term of
`(CTX')` with a constant fixed by the derivation, and only the parity and
predicated terms remain.
