---
rg: 2
id: wep-host-kazhdan-tests-cannot-refute-odd-maslov-llp-proof
kind: route
title: A successful max-side invariant state becomes, through the weak expectation, an invariant hypertrace of the host lift that sees z squared as conj(lambda) squared
target: wep-host-kazhdan-tests-cannot-refute-odd-maslov-llp
requires:
  - universal-cover-lattice-hypertraces-kill-z-squared
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
---

Notation of the target; `C` is unital (it must be, for `U(C)` to make
sense).  `Gamma` and `Gamma~` are Kazhdan groups
(`deligne-universal-cover-lattice-is-non-rf-kazhdan`, item 3, and its
quotient `Gamma`), so each has a Kazhdan projection in its full group
C-star algebra.  That projection acts, in every unitary representation, as
the orthogonal projection onto the invariant vectors (Akemann--Walter,
Valette).

## Step 0. `P_max != 0` iff an invariant state exists

Suppose `P_max != 0`.  Pick a state `psi` of `A (x)_max D` with
`psi(P_max) = ||P_max|| = 1`, and form its GNS triple `(pi, K, xi)`.  Then
`||xi - pi(P_max) xi||^2 = 1 - psi(P_max) = 0`, and `pi(P_max)` projects
onto the `pi o U`-invariant vectors.  So `xi` is invariant and
`psi(U_g) = <pi(U_g) xi, xi> = 1` for all `g`.

Conversely, if such a `psi` exists, its GNS vector is invariant, so
`pi(P_max) xi = xi != 0`.

## Step 1. Min side (part (i))

Represent `A (x)_min C` spatially on `H_A (x) H_C` through faithful
representations `pi_A`, `pi_C`.  Suppose `xi != 0` is invariant under
`g -> pi_A(u_g) (x) pi_C(W_g)`.

Identify `H_A (x) H_C` with the Hilbert--Schmidt operators
`conj(H_C) -> H_A`.  Then `xi` becomes a nonzero Hilbert--Schmidt `T` with
`pi_A(u_g) T = T conj(pi_C(W_g))`.  So `T T^*` is a nonzero compact positive
operator commuting with `pi_A(u(Gamma~))`.  A spectral projection of `T T^*`
for a nonzero eigenvalue is finite-rank and invariant, and it carries a
finite-dimensional representation `sigma` of `Gamma~` with
`sigma(z) = lambda I`.

Step 4 of `universal-cover-lattice-hypertraces-kill-z-squared-proof` gives
`sigma(z^2) = I`.  That step combines Deligne's finite residual in every
finite cover with Mal'cev, and it is part of the established required node.
So `lambda^2 = 1`, contradicting `(KT0)`.  Hence the Kazhdan projection of
`Gamma~` acts as `0` in a faithful representation, so it is `0` in
`A (x)_min C`.

## Step 2. The invariant state on `D` and on `C` (part (ii))

Suppose `psi(U_g) = 1` for all `g`.

For every `X`, Cauchy--Schwarz gives
`|psi(X(U_g - 1))|^2 <= psi(X X^*) (2 - 2 Re psi(U_g)) = 0`, and similarly
on the other side.  Hence `psi(U_g X U_g^*) = psi(X)`.

Put `phi_D(d) = psi(1 (x) d)`.  Since `U_g (1 (x) d) U_g^* = 1 (x) v_g d v_g^*`,
the state `phi_D` is `Ad v`-invariant, and `phi_D(v_z) = conj(lambda)`.

Put `phi_C = phi_D o q`.  Then `phi_C(W_g c W_g^*) = phi_C(c)` for all
`c in C`, and `phi_C(W_z) = conj(lambda)`, because
`W_z - conj(lambda) 1 in J = ker q`.

## Step 3. The weak expectation turns it into a hypertrace

Lance's weak expectation property is the definition used here. Take the
universal representation `C <= B(H)`, so `C^** = C''`. Then there is a ucp
map `E : B(H) -> C^**` with `E(c) = c` for `c in C`.

Because `E|_C` is a star-homomorphism, `C` lies in the multiplicative
domain of `E` (Choi).  So `E(W_g T W_g^*) = W_g E(T) W_g^*`.

Let `phi_C^**` be the normal extension of `phi_C` to `C^**`. The maps
`y -> phi_C^**(W_g y W_g^*)` and `phi_C^**` are both normal and agree on
the weak-star dense subalgebra `C`, so they agree on `C^**`.

Hence `Phi := phi_C^** o E` is a state on `B(H)` with

```text
Phi(W_g T W_g^*) = Phi(T)      for all g, T,
```

for the unitary representation `W : Gamma~ -> U(C) <= U(H)`, which is
`(HT1)`.  Also, since `E(W_z^2) = W_z^2`,
`Phi(W_z^2) = phi_C(W_z^2) = phi_D(v_z^2) = conj(lambda)^2`.

## Step 4. Contradiction

`universal-cover-lattice-hypertraces-kill-z-squared` gives
`Phi(W_z^2) = 1`, so `lambda^2 = 1`, contradicting `(KT0)`.  So no such
`psi` exists, and Step 0 gives `P_max = 0`.  This is part (ii).

**Hypotheses actually used.**
- WEP is used only in Step 3. It is the same hypothesis that makes the test
  sound, so the class is exactly the sound Kazhdan-projection tests.
- The genuine lift `W` is used in Steps 1 and 3.
- `A` enters only through `u_z = lambda 1`, in Steps 1 and 2.

Nothing about the host dimension or its finite-dimensional quotients is used.
