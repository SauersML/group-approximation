---
rg: 2
id: universal-cover-lattice-hypertraces-kill-z-squared
kind: claim
title: An invariant hypertrace for any unitary representation of the universal-cover lattice of Sp4(Z) sees the square of the central generator as one
distinct_from:
  odd-maslov-twisted-fibres-have-no-amenable-trace: that excludes amenable traces on the twisted fibres A_theta themselves; this is about an arbitrary representation of the universal-cover lattice, whose central generator need not act by a scalar and whose C-star algebra may have finite-dimensional quotients, and it needs no descent of amenability to any quotient.
  kazhdan-groups-without-fd-reps-avoid-qd-unitary-groups: that excludes images of a Kazhdan group without finite-dimensional representations in quasidiagonal algebras; this group has many finite-dimensional representations, and the statement locates an invariant hypertrace on the part where they live.
  stw10-kazhdan-full-group-traces-are-qd: that is the Kirchberg--Brown trace rigidity used here as input; this applies it to Ad-invariant states on all of B(H) and combines it with Deligne's finite residual.
---

**ESTABLISHED** by route `universal-cover-lattice-hypertraces-kill-z-squared-proof`.

Let `Gamma~` be the preimage of `Sp_4(Z)` in the universal cover of
`Sp_4(R)`, with central generator `z` of the covering kernel `Z`.  Let
`W : Gamma~ -> U(H)` be **any** unitary representation on **any** Hilbert
space, and let `Phi` be a state on `B(H)` with

```text
Phi(W_g T W_g^*) = Phi(T)        for all g in Gamma~, T in B(H).     (HT1)
```

Then

```text
Phi(W_z^2) = 1,   hence   Phi(T W_z^2) = Phi(T) for all T,   and   Phi(W_z) in [-1,1].   (HT2)
```

In words: an Ad-invariant hypertrace cannot see a central character of the
covering generator other than `+1` or `-1`.  This is Deligne's theorem
(finite quotients kill `z^2`) upgraded from finite-dimensional
representations to *amenable* ones, i.e. to everything visible to an
invariant mean on `B(H)`.

**Use.**  It is the step at which every Kazhdan-projection max/min
refutation of the local lifting property of an odd Maslov fibre over a
WEP host dies: `wep-host-kazhdan-tests-cannot-refute-odd-maslov-llp`.

**Sharpness.**  The conclusion cannot be improved to `Phi(W_z) = 1`.  The
metaplectic double cover `E_2 = Gamma~/<z^2>` is residually finite (the
input of `metaplectic-half-parameter-is-ce`), so some finite quotient of
`Gamma~` is nontrivial on `z`, and the normalized trace on the `z = -1`
eigenspace of its regular representation is a state `Phi` with `(HT1)` and
`Phi(W_z) = -1`.  Nor can
`(HT1)` be weakened to invariance on a C-star subalgebra only (every trace
is invariant on its own algebra, and the twisted fibres have traces): the
state must live on all of `B(H)`, which is exactly where amenability enters.
