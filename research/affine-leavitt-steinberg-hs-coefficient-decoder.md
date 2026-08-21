---
rg: 2
id: affine-leavitt-steinberg-hs-coefficient-decoder
kind: claim
title: Decode the affine active Leavitt cell from normalized-HS Steinberg microstates
distinct_from:
  finite-window-decoder: that asks for three multiplicative products on a fixed-density Pauli corner extracted from an outer-character atlas; this asks for the named affine active idempotent and one relative binary Leavitt cell inside the fixed group St_5(L_A(k[C_aff])).
  hs-steinberg-root-kernel-is-linear-sofic: that promotes the whole quotient by the common root kernel to a rank-metric matrix ultraproduct; this needs only one active coefficient and four named Leavitt operators, together with comparison to one root word.
  approximate-relative-leavitt-cell-kills-active-trace: that proves the terminal trace inequality after coefficient operators have been decoded; this is precisely the missing root-to-coefficient extraction.
---

OPEN. Fix the finite presentation of

```text
Gamma_A=St_5(L_A(k[C_aff]))
```

and the word `w_A=x_12(A)` from
`affine-leavitt-steinberg-mark-is-fd-invisible`. Prove that there are a
constant `C`, a threshold `delta_0>0`, and a modulus
`omega(delta)->0` such that every normalized-HS `delta`-representation
`U` of this presentation, for `delta<delta_0`, produces an orthogonal
projection `P` and contractions `S_0,S_1,T_0,T_1` in the same matrix algebra
with

```text
||T_i S_i-P||_2 <= omega(delta),                 i=0,1,
||S_0 T_0+S_1 T_1-P||_2 <= omega(delta),          (ALD1)
```

and

```text
||w_A(U)-I||_2^2 <= C tr(P)+omega(delta).          (ALD2)
```

Only these three coefficient relations are required. No off-diagonal
Leavitt relation, full coefficient-algebra representation, rank control on
every small error, or correction of the whole almost representation is part
of the claim.

Together with `approximate-relative-leavitt-cell-kills-active-trace`, `(ALD1)`
gives `tr(P)<=3omega(delta)`. Then `(ALD2)` collapses the marked root with a
dimension-free modulus. This is the exact remaining analytic interface for
the affine active Leavitt construction.

## Attempts

- **Exact finite-dimensional decoding is closed.** Root subgroups have finite
  image, their common kernel generates a finite coefficient quotient, and
  the relative Leavitt relation kills `A`; this is the proof of
  `affine-leavitt-steinberg-mark-is-fd-invisible`.
- **A common carrier is insufficient.** `carrier-not-decoder` shows that a
  finite root table can retain the relevant carrier while failing to recover
  multiplicative coefficient data. The proof must use paired Steinberg root
  triangles, not only a joint spectral projection.
- **HS error is not rank error.** An arbitrarily small full-rank perturbation
  has normalized rank one, so the exact common-kernel argument cannot be
  transferred by deleting the support of every small error.
- **The requested window is now minimal.** The trace endpoint consumes only
  `T_0S_0`, `T_1S_1`, and `S_0T_0+S_1T_1`. A promising attack is therefore a
  finite root-character orbit for the active central idempotent, coupled to
  three paired root triangles, with a conditional expectation used only to
  recover those products.
- **The exact one-to-two word is now explicit.** After passing to the
  coefficient-central envelope, `affine-active-doubling-is-elementary-matrix-conjugacy`
  writes the active branch as one Whitehead elementary word.  However,
  `single-affine-leavitt-branch-chart-is-stationary` proves that this
  conjugacy and the finite head alone form a virtually-free chart with exact
  finite marked countermodels.  The decoder must therefore use the paired
  Steinberg multiplication triangles in addition to the conjugator.
- **No regular-trace contradiction is asserted.** The decoder is a
  finite-matrix stability statement. It need not extend to the left regular
  representation or any arbitrary tracial representation of `Gamma_A`.
