---
rg: 2
id: finite-traced-kazhdan-transport-proof
kind: route
title: Kazhdan projection in the conjugation algebra of the tracial ultraproduct
target: finite-traced-kazhdan-transport
requires: [faithfully-traced-unital-coordinates]
artifacts:
  - non_mf_groups_exist.tex
  - notes/NO_ONE_SIDED_GROWTH.md
  - GroupApproximation/Sofic/KazhdanAsymptoticCommutant.lean
---

## Why sufficient

Fix a free ultrafilter `omega` and let `M` be the tracial ultraproduct of
`(A_k,tau_k)`; by item 4 of `faithfully-traced-unital-coordinates` it is a
finite von Neumann algebra with trace `tau_omega`, and `M or JMJ` acting on
`L^2(M,tau_omega)` is finite.  (Only item 4 is used here, and its proof does
not use faithfulness of the `tau_k`.)

**Step 1: an honest homomorphism.**  Asymptotic multiplicativity in either
norm kills the defect in `M`, so `g |-> u(g) = [U_k(g)]` is a group
homomorphism `H -> U(M)`.  Uniform boundedness makes `x=[x_k]` an element of
`M`, and the hypothesis says exactly `[x,u(iota gamma)]=0` for all `gamma`.

**Step 2: the fixed-space projection lies in the algebra.**  `Gamma` acts on
`L^2(M,tau_omega)` by the unitaries `Ad(u(iota gamma)) = u JuJ`, which lie in
`M or JMJ`.  Property `(T)` gives a Kazhdan projection `p` in `C^*_max(Gamma)`
whose image in every unitary representation is the projection onto the fixed
vectors.  Hence

```text
P = projection onto Fix(Ad(u(iota Gamma))) in C^*(Ad(u(iota Gamma)))
                                           <= M or JMJ.        (K1)
```

This is the only use of `(T)`: without it the fixed-space projection is only
known to lie in `B(L^2)`, which is not finite, and Step 4 collapses.

**Step 3: one-sided compression.**  Put `W=u(s) in U(M)`, so
`Ad(W) in M or JMJ`.  For any `xi`,

```text
Ad(W) xi is Ad(u(iota gamma))-fixed  <=>  xi is
Ad(u(s^(-1) iota(gamma) s))-fixed,
```

so `Ad(W) P Ad(W)^*` is the fixed-space projection of the subgroup
`s iota(Gamma) s^(-1)` (a `(T)` group, being a homomorphic image of `Gamma`).
A subgroup has a larger fixed space, and by hypothesis
`s iota(Gamma) s^(-1) <= iota(Gamma)`, hence

```text
Ad(W) P Ad(W)^* >= P.                                          (K2)
```

**Step 4: finiteness closes it.**  `(K2)` exhibits `P` and its unitary
conjugate, which are Murray--von Neumann equivalent inside `M or JMJ`, in a
one-sided inclusion.  In a finite von Neumann algebra `Q ~ P <= Q` forces
`P=Q`, so

```text
Ad(W) P Ad(W)^* = P.                                           (K3)
```

**Step 5: transport and desultrafiltration.**  `Px=x` by Step 1, so by `(K3)`
`Ad(W)x` is again fixed, i.e. `[WxW^*, u(iota gamma)]=0` in `M`, i.e.

```text
lim_omega ||[U_k(s)x_kU_k(s)^*, U_k(iota gamma)]||_(2,tau_k) = 0.
```

The sequence is bounded, and the conclusion holds for every free
ultrafilter, so its ordinary limit is `0`: otherwise some subsequence stays
above `epsilon>0` and any ultrafilter containing it would contradict the
above.  End proof.

## What this does and does not generalize

Steps 3 and 4 are the corona formulation the corpus already uses
(`notes/NO_ONE_SIDED_GROWTH.md`: `P <= VPV^*`, `P ~ VPV^*`, finiteness gives
equality, "a one-sided group-theoretic compression therefore becomes a
two-sided symmetry of the entire bounded asymptotic commutant"); what is new
here is that the ambient may be any traced coordinates and that the hypothesis
may be taken in `||.||_2`.

The matrix proof in `KazhdanAsymptoticCommutant.lean` is a finite-stage
substitute for this argument, deliberately avoiding ultrafilters: it replaces
`(K1)` by the spectral projection of the Hermitian Kazhdan average above the
threshold `theta = (1 + (1 - kappa^2/(4|S|)))/2` and `(K3)` by the equal-rank
projection flip (`||(1-q)p|| <= eps < 1` with `rank p = rank q` gives
`||(1-p)q|| <= eps/sqrt(1-eps^2)`), and thereby obtains uniform quantitative
bounds.  Reproducing *that* in general
coordinates would additionally need spectral projections at an arbitrary
threshold (real rank zero) and a uniform comparison modulus.  The
ultraproduct form above needs neither, at the cost of giving no modulus.
