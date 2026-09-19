---
rg: 2
id: h-mix-halves-are-lef-by-column-windows
kind: claim
title: Both halves W x| <x_34(1)> and W x| <x_43(S)> of H_mix are LEF by column-window models, H_mix is their amalgam over the non-residually-finite core W, and column windows die on H_mix because ab has no finite-dimensional invariant subspace
distinct_from:
  jacobson-t-oriented-double-parabolic-is-lef: that builds models from the fixed window Win_d and needs the right Levi factor inside EL_2(F[T]), which lowers degree; this allows any finite-dimensional invariant window, which covers the S-oriented half x_43(S) through the offset window Win_d (+) Win_(d+1), and shows that for Levi factors inside GL_2(F_2[S]) the method works exactly when the factor is locally finite.
  p22-double-parabolic-is-not-lef: that proves P_{2,2}(J), and with it H_mix, is not LEF by a conjugation pigeonhole; this shows each of the two index-two halves of H_mix is LEF, so non-LEF appears only in the amalgam, and it names the geometric reason, the hyperbolic element ab.
  jacobson-el2-core-escapes-amenable-tree-extensions: that asks for an MF theorem for N-normal amalgams of LEF groups; this checks that H_mix really is such an amalgam, with LEF factors and a core that is LEF but not residually finite.
artifacts:
  - experiments/h-mix-column-windows-2026-09-17/check_windows.py
---

**ESTABLISHED** (route `h-mix-halves-are-lef-by-column-windows-proof`). No
property (T) is used. `experiments/h-mix-column-windows-2026-09-17/check_windows.py`
exits 0.

## Setting

- `J = F_2<S,T | TS = 1>`, `Q = 1 - ST`, and `V_+ = F_2^((N))` with
  `S e_j = e_(j+1)`, `T e_j = e_(j-1)`, `T e_0 = 0`.
- The column space is `U = V_+ (+) V_+`. A matrix `B in M_2(J)` acts on it by
  `B_+ (v_1, v_2)^t = B (v_1, v_2)^t`.
- `Win_d = span{e_0, ..., e_(d-1)}`.
- In `GL_4(J)`, write `(g, X, B) = [[g, X], [0, B]]`. Then
  `P_R = M_2(J) x| (EL_2(J) x R)` for any `R <= GL_2(J)`.
- `a = x_34(1)` is `(1, 0, [[1,1],[0,1]])` and `b = x_43(S)` is `(1, 0, [[1,0],[S,1]])`.
  `D = <a, b>`, `W = M_2(J) x| EL_2(J)`, and `H_mix = P_D`.
- The head is `x_13(Q) = (1, Q E_11, 1)`.

## Theorem 1 (column-window criterion)

Suppose that for every finitely generated `R_0 <= R` and every `d`, some
finite-dimensional `R_0`-invariant subspace `Omega ⊂ U` contains
`Win_d (+) Win_d`. Then `P_R` is LEF, and the head has nontrivial image in
every model of the construction.

The model on a ball is

```text
Psi(g, X, B) = [[ Phi_M(g), X_+|Omega ], [ 0, B_+|Omega ]],
```

where `Phi_M` is the imported rank-two model. It is exact on the ball because
`(X B)_+|Omega = X_+|Omega ∘ B_+|Omega` when `B_+ Omega = Omega`.

## Theorem 2 (the two halves)

- `G_1 = W x| <a>` is LEF, with `Omega = Win_d (+) Win_d`.
- `G_2 = W x| <b>` is LEF, with the offset window `Omega = Win_d (+) Win_(d+1)`.
- `a` and `b` are involutions, and `c = ab = [[1+S, 1], [S, 1]]` has infinite
  order. So `D ≅ D_inf`, and

```text
H_mix = G_1 *_W G_2,      W normal of index two in each factor.
```

`W` is LEF (it is `P_1`) but not residually finite: every finite quotient of
`W` kills the head. So `G_1`, `G_2` and `H_mix` are not residually finite
either, and `H_mix` is not LEF (`p22-double-parabolic-is-not-lef`: the five
certificate elements lie in `H_mix`). Non-LEF therefore appears only in the
amalgam.

## Theorem 3 (window dichotomy and the death step on H_mix)

1. Let `R <= GL_2(F_2[S])`. The hypothesis of Theorem 1 holds if and only if
   `R` is locally finite.
2. `c = ab` preserves no nonzero finite-dimensional subspace of `U`. Its
   characteristic polynomial is `x^2 + S x + 1`, and no root of it is
   algebraic over `F_2`.
3. **Class kill.** Consider exact column-restriction models of `H_mix`: a
   finite-dimensional `Omega ⊂ U`, an upper-left block `phi(g)`, the upper-right
   block `X_+|Omega`, some lower block `rho(B)`, `Psi(1) = 1`, and exact
   multiplicativity on a ball containing `x_13(1)`,
   `x_24(1)`, `a` and `b`. Every such model has `Omega = 0`, so it kills all
   of `M_2(J)` and in particular the head.
   - **Death step.** `E_11 + E_22 = 1` turns exactness at
     `(x_13(1), a), (x_24(1), a), (x_13(1), b), (x_24(1), b)` into
     `rho(B) = B_+|Omega` with `B_+ Omega ⊂ Omega`. So `Omega` is `c`-invariant,
     which contradicts item 2.
   - **Window form of the same obstruction.** `Win_(d_1) (+) Win_(d_2)` is
     `a`-invariant iff `d_2 <= d_1`, and `b`-invariant iff `d_2 >= d_1 + 1`.
   - **Tree reading.** The symbol of `c` has trace `z`, so it is hyperbolic at
     the place `infinity`. The Levi factors of Theorem 1 fix a vertex there.

## Caution: head survival is not faithfulness

`N_0 = {(1, [0 | v], 1) : v in (JQ)^2}` is a nonzero normal subgroup of `H_mix`
that does not contain the head. Here `JQ = span{S^i Q}` is a left ideal, and
the right action of `D` fixes `[0 | v]`, because `JQ S = 0` and `D ≡ <a> mod S`.

So "`H_mix` is MF" implies that the head survives in some MF model, but not
conversely. A head-keeping MF model of any quotient `H_mix/N` with
`x_13(Q) ∉ N`, such as `N = N_0`, would equally kill the `H_mix` lane of HC.

DERIVATION
h-mix-halves-are-lef-by-column-windows-proof
