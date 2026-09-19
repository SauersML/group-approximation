---
rg: 2
id: soft-block-mass-yields-fractional-branch
kind: claim
title: A lower bound on one block's Hilbert-Schmidt mass produces an exact partial isometry of guaranteed source density
artifacts:
  - notes/TRUE_TRACE_FLAT_BLOCK_SPECTRAL_FLOOR.md
  - research/artifacts/fractional-branch-pressure-2026-08-19.md
distinct_from:
  atlas-wedderburn-soft-transport-certificate: that asks for a positive-dual transport cost over the whole chart-to-chart block table; this is the one-block spectral conversion that turns a single block mass into a branch, and asserts nothing about any dual value.
  partial-isometry-leakage-is-range-defect: that rewrites the leakage of a branch that already exists as a range defect; this manufactures the branch from block mass and shows its leakage is exactly zero.
  atlas-spectral-shrunk-intertwiner-certificate: that asks for a subspace whose image under a low-energy operator space shrinks; this produces an isometric branch out of a large block and never uses a dimension deficit.
---

Let `(M,tau)` be a finite tracial von Neumann algebra with normalized trace and
normalized Hilbert--Schmidt norm.  Let `P,Q` be projections, let `W in M` with
`||W||_op <= 1`, and put

```text
X = Q W P,     x = tau(P).
```

Fix `0<t<1` and let

```text
E_t = 1_[t,1](|X|)
```

be the spectral projection of `|X|=(X^*X)^(1/2)`.  Then `E_t <= P` and:

**(SBM1) Guaranteed source density.**

```text
tau(E_t) >= (||X||_2^2 - t^2 x)/(1-t^2).
```

**(SBM2) Chebyshev ceiling.**

```text
tau(E_t) <= ||X||_2^2/t^2.
```

**(SBM3) The branch is exact.**  Let `X=V|X|` be the polar decomposition and
put `T = V E_t`.  Then

```text
T^* T = E_t,     T T^* <= Q,     ||(1-Q)T||_2 = 0.
```

So `T` is a partial isometry whose source is a subprojection of `P` of density
at least `(SBM1)` and whose leakage out of the target `Q` vanishes identically.

**(SBM4) Gram transfer.**  If `T_e,T_f` are two such branches, built from
`X_e=Q W_e P_e` and `X_f=Q W_f P_f` at thresholds `t`, then

```text
||T_e^* T_f||_2 <= t^(-2) ||X_e^* X_f||_2.
```

Hence both costs of the branching-capacity interface are controlled by ordinary
block moments: the leakage is zero, and the ordered-pair Gram energy is
controlled by the cross-block moment `||X_e^*X_f||_2` at the fixed price
`t^(-2)`.

## Why this is the usable form

Every existing branch target in the atlas lane
(`atlas-pauli-range-packing-recurrence`, `atlas-pauli-branch-recurrence-automaton`)
demands partial isometries whose source is *exactly* a state projection, i.e. a
hard containment `w P_i w^* <= P_j` up to defect.  `(SBM1)`--`(SBM3)` remove
that demand: an ordinary Fourier-block moment lower bound already delivers a
branch, at the cost of covering only the fraction

```text
c(t) = [ (||X||_2^2/x - t^2)/(1-t^2) ]_+
```

of the source state.  `fractional-source-branch-pressure` is the capacity
theorem that consumes such fractional branches.

The already-proved `(SFF2)` of `TRUE_TRACE_FLAT_BLOCK_SPECTRAL_FLOOR.md` is the
special case `P=F`, `Q=G`, `W=1`, `t=1/4`, `tau(F)=tau(G)=1/8`,
`||GF||_2^2=1/64`, where `(SBM1)` returns `tau(E_t) >= 1/120` exactly.
