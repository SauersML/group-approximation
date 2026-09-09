---
rg: 2
id: root-kernel-invariance-is-not-pointwise-obtainable
kind: claim
title: Root-kernel invariance fails maximally at every coordinate even when every fixed test is eventually exact
distinct_from:
  corona-defect-is-not-uniform: that records the general principle that corona representations have pointwise but not uniform MULTIPLICATIVITY defect, which is what kills Ulam-type stability routes; this exhibits explicit models in which every multiplicativity test in sight is satisfied EXACTLY and a different hypothesis, invariance of a root kernel under two left multiplications, still fails at the maximal distance at every coordinate.
  uniform-root-kernel-invariance-kills-one-sided-defect: that is the positive lemma whose hypotheses are quantified at one coordinate over all coefficients; this proves those hypotheses are not obtainable from pointwise corona data, so the two together close a route rather than open one.
  bare-self-copy-mf-calibration: that is a group-level calibration, one torsion-free finitely presented MF group with a finite-dimensionally invisible mark; this is a coefficient-level calibration about the quantifier order in a ring-theoretic hypothesis, and asserts nothing about any group being MF.
artifacts:
  - research/artifacts/root-kernel-uniformity-gap-2026-09-08.md
---

**ESTABLISHED.**  Let `J = F_2<s,t | ts = 1>` and `q = 1 + st`.  For every
`N >= 1` there are a finite-dimensional Hilbert space `H_N` and maps

```text
X_N, Y_N, U_N : (J,+) -> U(H_N),        C_N in U(H_N)
```

such that, for every `N`:

1. `X_N`, `Y_N`, `U_N` are **genuine** additive-group homomorphisms;
2. `C_N X_N(a) C_N* = Y_N(a)` for every `a in J`, **exactly**;
3. for each fixed `a in J` there is `N_0(a)` such that for all `N >= N_0(a)`
   and **all** `b in J`, `[U_N(b), X_N(a)] = Y_N(ba)` exactly;
4. the constant Weyl relations `C_N^2 = 1` and `(C_N U_N(1))^3 = 1` hold
   exactly;
5. every fixed nonzero coefficient is eventually separated maximally,
   `|| X_N(a) - 1 || = || Y_N(a) - 1 || = 2`, and the marked coefficient is
   separated at every `N`: `|| X_N(q) - 1 || = 2` for all `N >= 1`;

and yet, with `a_N = s^N`,

```text
X_N(a_N) = 1,     [U_N(t), X_N(a_N)] = 1,     || Y_N(t a_N) - 1 || = 2.  (PG1)
```

So the kernel of `X_N` is **not** invariant under left multiplication by `t`,
and the failure is by the largest distance two unitaries can be apart, at
**every** coordinate `N`.

**What this closes.**  The hypotheses `(RK2)`--`(RK3)` of
`uniform-root-kernel-invariance-kills-one-sided-defect` are quantified *at one
coordinate, for every coefficient*; a norm-corona representation supplies *for
every fixed coefficient, at late coordinates*.  `(PG1)` shows the exchange is
not available even under conditions far stronger than MF demands: exact
additivity of all three root maps, exact conjugation transport, exact Weyl
relations, and eventual **exactness** -- not mere smallness -- of every fixed
commutator test.  So the (T)-free route that runs the uniform lemma against a
corona representation is blocked, and `property-t-free-jacobson-head-collapse`
gains a recorded dead approach rather than a proof.

**Scope.**  The models realise only the root relations at the positions
`(2,3)`, `(1,3)`, `(1,2)`.  No image is specified for the root groups into the
third coordinate and no other Steinberg relation is checked, so they are **not**
an approximate representation of `E_3(J)` or `E_4(J)` and are **not** a
counterexample to the ring theorem
`finite-additive-order-one-sided-defects-are-mf-invisible`, which is
established.  Additional relations could exclude these models; that exclusion
is not proved here and would be the way to revive the route.
