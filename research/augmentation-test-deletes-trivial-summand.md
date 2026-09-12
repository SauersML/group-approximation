---
rg: 2
id: augmentation-test-deletes-trivial-summand
kind: route
title: Test on the liftable scalar map, positivize one face, and remove the invisible quotient summand
target: global-triangle-separator-survives-mod-augmentation
requires:
  - three-face-quotient-separators-are-not-one-face-local
  - tree-face-separator-signedness-is-removable-modulo-the-unit
  - positive-tree-separator-has-fd-low-ideal-moment-packets
---

The augmentation restricted to `S_Delta` is a state.  Composing it with the
scalar inclusions into `A` and `Q` gives ucp maps `Phi_epsilon` and
`E_epsilon`, with `q Phi_epsilon=E_epsilon`.  Substitution in `(SQS2)` proves
`(MAS2)`.  Since `E_epsilon` is an idempotent ucp projection,

```text
P_epsilon(D_epsilon)=E_epsilon o(id-E_epsilon)=0.
```

The norm bound `||id-E_epsilon||<=2` proves `(MAS3)`.

Decompose `ell` by the fixed maps `R_ij` from `(SQS7)`.  The three face
evaluations sum to `ell(D_epsilon)>=delta`, so at least one is at least
`delta/3`, proving `(MAS4)`.  Apply
`tree-face-separator-signedness-is-removable-modulo-the-unit` (whose order
lemma applies to every finite face algebra, not only a tree face) to this
component.  It agrees with the original component on `D_epsilon`, because
`D_epsilon(1)=0`.  The norm estimate `(PCU3)`, the normalized separator, and
the fixed precomposition norm of `R_H` give a uniform upper bound on the
positive functional.  Normalizing it therefore gives `(MAS5)` with a fixed
`c>0`.

Every entry of the Choi matrix `X_H` belongs to `ker epsilon`, since

```text
epsilon(D_epsilon(x))=epsilon(x)-epsilon(x)=0.             (1)
```

Choose a self-adjoint lift `X_H_tilde` in the corresponding amplification of
`A`.  Its entries also have zero augmentation because the augmentation of
`A` factors through `q`.

Pull `omega_H` back along the amplified quotient and use the RFD state-density
argument from `pull-back-the-positive-choi-state-and-use-rfd-state-density`.
Choose the approximation accurately enough that a finite-dimensional vector
state `rho,xi` has

```text
<rho(X_H_tilde)xi,xi> >= (c delta)/2                       (2)
```

and arbitrarily small prescribed ideal moments.

Let `p` be the projection onto the largest subrepresentation on which the
represented ideal vanishes.  It is invariant and factors through `Lambda`;
because every finite-dimensional representation of `Lambda` is trivial,
`p` is exactly the trivial `G_0` summand.  Write

```text
xi=xi_0+xi_1,       xi_0=p xi.
```

Equation `(1)` makes `rho(X_H_tilde)` zero on the amplified trivial summand,
so the left side of `(2)` is

```text
<rho(X_H_tilde)xi_1,xi_1>.
```

If `M=||X_H_tilde||`, then `(2)` implies

```text
||xi_1||^2 >= (c delta)/(2M).                              (3)
```

Restrict `rho` to `(pH)^perp` and normalize `xi_1`.  The restricted
representation has ideal support `z_rho=1`.  Every ideal element kills
`xi_0`, so its moment on `xi_1` before normalization is the same as on `xi`;
by `(3)`, normalization costs at most the fixed factor
`2M/(c delta)`.  Starting with correspondingly smaller RFD approximation
errors yields any prescribed final `eta` in `(MAS6)`.  The normalized defect
value is at least the unnormalized value in `(2)`, completing the proof.
