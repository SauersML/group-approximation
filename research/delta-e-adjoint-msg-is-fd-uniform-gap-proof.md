---
rg: 2
id: delta-e-adjoint-msg-is-fd-uniform-gap-proof
kind: route
title: Adjoin V tensor U to a delta_e model to make U an exact reducing corner of the adjoint corona, then stack finite-dimensional representations with eigenvalues creeping to 1
target: delta-e-adjoint-msg-is-fd-uniform-gap
requires:
  - model-spectral-gap-quantifier-ladder
artifacts:
  - experiments/delta-e-tensor-saturation-2026-09-17/check_tensor_block.py
---

Notation is that of the target.  From the required claim we use only
the elementary corner fact of its item 4: for self-adjoint `y` in a unital
C-star algebra `B` that commutes with a projection `p`,
`sp_(pBp)(pyp) subset sp_B(y)`.  Models take values in unitaries.

## Theorem A, direction =>

Assume `(MSG)` holds for `sigma~_V` for every `delta_e`-profile model.  If
`G` has no such model, there is nothing to prove.  So fix one, `V_n` of
size `a_n`, and fix any model `U_n` of size `b_n`.

*`M` is a `delta_e` model.*  Put `M_n=V_n (+) (V_n tensor U_n)`, of size
`a_n(1+b_n)`.  For unitaries,

```text
||(V tensor U)(gh) - (V tensor U)(g)(V tensor U)(h)||
     <= ||V(gh)-V(g)V(h)|| + ||U(gh)-U(g)U(h)||,
```

so `M` is a model.  Its normalized trace is
`(tr V_n(g) + b_n tr V_n(g) tr U_n(g))/(1+b_n)`.  In absolute value this
is at most `|tr V_n(g)|`, since `|tr U_n(g)|<=1`, and it tends to
`delta_e(g)`.

*The exact block.*  For `xi in C^(b_n)`, let `X_xi` in
`Hom(C^(a_n), C^(a_n) tensor C^(b_n))` be `eta -> eta tensor xi`.  View
it as an off-diagonal element of `M_(a_n(1+b_n))`.  Then
`Ad M_n(g) X = (V_n tensor U_n)(g) X V_n(g)^*` on that block, and

```text
(V_n(g) tensor U_n(g)) X_xi V_n(g)^* eta = (V_n(g)V_n(g)^* eta) tensor U_n(g) xi = X_(U_n(g) xi) eta.
```

This identity holds exactly for every `g`, not only asymptotically.
- The span `K_n={X_xi}` is invariant under every `Ad M_n(g)`.
- `Ad M_n(g)` is unitary for the Hilbert--Schmidt inner product, so
  `K_n^perp` is invariant too. The orthogonal projection `p_n` onto `K_n`
  therefore commutes with every `Ad M_n(g)`.
- `||X_xi||_2 = sqrt(a_n) |xi|`, unnormalized. Under the normalized
  trace the constant changes, but in either case `xi -> X_xi/(const)` is
  an isometry `C^(b_n) -> K_n` intertwining `U_n(g)` with
  `Ad M_n(g)|K_n`.

*Corner.*  Put `p=[p_n]` in `B_M = prod B(M_(a_n(1+b_n)),||.||_2)/(+)`.
Then `pB_Mp = prod B(K_n)/(+)`, which is isomorphic to
`prod M_(b_n)/(+)`.  Under this isomorphism
`p sigma~_M(g) p = [U_n(g)]`.  The operator `y=sigma~_M(h_S)` commutes
with `p`, and it is self-adjoint because `S=S^(-1)` and
`[Ad M_n(s^(-1))]=[Ad M_n(s)]^*` in the corona.  Hence

```text
sp([U_n(h_S)]) = sp_(pBp)(pyp) subset sp_(B_M)(y).
```

`(MSG)` for `sigma~_M` therefore gives `(MSG)` for `[U_n]`.  As `U` was
arbitrary, `T_MF(G,L)` holds.

## Theorem A, direction <=

If there is no `delta_e` model, the left side is vacuous.  If `T_MF(G,L)`
holds and `V` is a `delta_e` model, then `Ad V_n`, acting on
`(M_(a_n),||.||_2)`, which is isometric to `C^(a_n^2)`, is a model:
`||Ad V(gh)-Ad V(g)Ad V(h)|| <= 2||V(gh)-V(g)V(h)||`.  Its corona
homomorphism is `sigma~_V`, because
`B_V = prod B(C^(a_n^2))/(+) = prod M_(a_n^2)/(+)`.  So `T_MF` applies to
it.  QED

## Theorem B

Suppose that no `c>0` works.  Choose finite-dimensional representations
`pi_j` and eigenvalues `lambda_j` of the self-adjoint operator
`pi_j(h_S)` with `max(lambda_(j-1), 1-1/j) < lambda_j < 1`.  Put
`U_n = pi_1 (+) ... (+) pi_n`.  It is an exact homomorphism, hence a
model.

Fix `j`.  For `n>=j`, the operator `U_n(h_S)-lambda_j` kills a unit
vector `v_n`.  If `[U_n(h_S)]-lambda_j` had an inverse `[y_n]` in the
corona, then `||y_n(U_n(h_S)-lambda_j) - I|| -> 0`.  But this norm is at
least `||(y_n(U_n(h_S)-lambda_j) - I)v_n|| = 1`.  So
`lambda_j in sp([U_n(h_S)])` for every `j`.  Since `lambda_j -> 1` with
`lambda_j != 1`, the point `1` is an accumulation point, and `T_MF`
fails.  QED

*The `(tau)` reading.*  Let `N` be normal of finite index, and let `pi` be
`l^2(G/N)`.  Because `e in S` and `h_S` is an average of unitaries, strict
convexity gives `pi(h_S)v=v` if and only if `v` is `L`-fixed.  So on the
orthocomplement of the `L`-fixed vectors, `sp(pi(h_S)) subset [-1,1-c]`.
Restricted to `L`, the space `l^2(G/N)` is a sum of copies of
`l^2(LN/N)`, so the Cayley graphs of `LN/N` with respect to `S` have
spectral gap at least `c` uniformly in `N`.

*Amenable `L`.*  If `L` is amenable and `|LN_k/N_k| -> infinity`, then
`LN_k/N_k = L/(L cap N_k)` is an infinite family of finite quotients of
the amenable group `L`.  By the Lubotzky--Weiss theorem, an amenable group
has property `(tau)` with respect to no infinite family of finite-index
normal subgroups.  So their Cayley graphs are not expanders, and
(FD-gap) fails.

## Corollary C and the Jacobson instance

Theorem A turns any proof of the left side of Theorem A into a proof of
`(exists delta_e model) => T_MF(G,L)`.  Theorem B then gives (FD-gap).
For `G=EL_5(J)`, the symbol `pi_+` maps `G` onto `SL_5(F_2[z^(+-1)])` by
(MQ1) of `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`.
Congruence quotients of that group are therefore finite quotients of
`G`, and the `(tau)` reading applies to the image of `L`.

## Numerical sanity check

`experiments/delta-e-tensor-saturation-2026-09-17/check_tensor_block.py`
builds random unitaries `V` and `U` and verifies the exact intertwining
`Ad M(g) X_xi = X_(U(g) xi)`.  It also checks that the projection onto
`K` commutes with `Ad M(g)`, and that the spectrum of `U(h)` lies inside
the spectrum of `Ad M(h)` for a random symmetric average `h`.
