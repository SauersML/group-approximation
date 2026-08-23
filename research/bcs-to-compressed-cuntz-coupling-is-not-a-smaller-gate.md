---
rg: 2
id: bcs-to-compressed-cuntz-coupling-is-not-a-smaller-gate
kind: claim
title: Bounding compressed Cuntz source error by BCS energy is not a smaller groupification gate
distinct_from:
  orthogonal-compressed-word-branches-have-cuntz-rank-floor: that proves the finite rank endpoint and its regular-factor firewall; this compares that endpoint with the fixed non-CE BCS gap and identifies the missing direction of control.
  non-ce-bcs-has-robust-approximate-energy-gap: that supplies a lower bound for the BCS residual energy; this proves that coupling a second lower-bounded defect to it yields no presentation payment.
  common-partial-isometry-swap-game-compiler: that asks for the full ordinary-word construction; this proves the direct BCS-to-Cuntz proposal is either redundant or exactly CPS12.
  affine-leavitt-decoder-interface-is-mark-collapse-equivalent: that detects a vacuous existential carrier in one Steinberg decoder; this is a quantitative two-lower-bounds audit for a prescribed marked carrier and prescribed compressed branches.
---

Work on one fixed exact marked packet corner of normalized mass `q`.  Let
`B` be the complete fixed non-CE BCS energy on that corner and let

```text
D=sum_i ||(Q_iU_iE)^*(Q_iU_iE)-E||_2^2              (BCC1)
```

be the source-Gram defect of `k>=2` orthogonal compressed branches.  After
fixed packet exactification, the two established finite-dimensional bounds
are

```text
B>=beta_B q,                 D>=(k-1)q.               (BCC2)
```

Consequently an estimate of the proposed direct form

```text
D<=C B                                                  (BCC3)
```

does not pay either quantity by presentation defect.  It merely compares
two quantities already bounded below.  Combining `(BCC2)--(BCC3)` gives
another lower bound on `B`; it gives no upper bound on `B`, `D`, or `q`.
This remains true if the rows are replicated or reweighted: those operations
only change `C` and `beta_B`.

There are exactly three ways to make the coupling terminal.

1. If group-word defect `delta` implies

   ```text
   B<=A delta,                                           (BCC4)
   ```

   then the BCS gap alone gives `beta_B q<=A delta`; the Cuntz packet is
   redundant.  This is the existing positive-mass BCS energy decoder.
2. If instead

   ```text
   D<=A delta,                                           (BCC5)
   ```

   then the Cuntz floor alone gives `(k-1)q<=A delta`; the non-CE BCS is
   redundant.  Proving `(BCC5)` is precisely the finite-matrix source-Gram
   decoder left open by the compressed Cuntz theorem.
3. If the Cuntz source is activated only on the uncovered forbidden column,
   let `L=L_forb` and let `W=C_forb+E_cons` be the already wordized energy.
   Suppose the activation genuinely represents that column in the required
   quantitative sense: there are fixed constants `a,b>0` with

   ```text
   a L<=D<=b L+O(W).                                    (BCC6)
   ```

   Then `D<=A W` implies `L<=A/a W`, which is `(CPS12)`; conversely
   `(CPS12)` and the upper half of `(BCC6)` imply `D<=A'W`.  Thus the
   localized compressed-Cuntz decoder is quantitatively equivalent to the
   original forbidden-weighted carrier gate, up to constants.

The exact infinite perfect model causes no conflict: there `B=D=0` and the
stabilized proper-corner branches exist.  The obstruction is finite
soundness, not completeness.

There is also a regular-factor fence on a purported fixed first-order
shortcut.  If `(BCC5)` is a tracially functorial consequence of fixed
group-algebra identities, apply it at `delta=0` in `M_n(L(Gamma))`.  The
von Neumann dimension version of the compressed Cuntz floor forces `q=0`,
collapsing the embedded marked packet.  Hence a fixed algebraic or
all-tracial decoder cannot preserve the
exact mark.  A decoder restricted genuinely to finite matrix coordinates is
allowed, but proving it is the same matrix-only groupification gate isolated
above; model-theoretic packaging does not make it smaller.

Therefore the most direct finite D8/Hecke plus Cuntz coupling yields no new
intermediate theorem.  Useful future work must construct the finite-only
source-Gram decoder itself, not bound its output by the full BCS energy.
