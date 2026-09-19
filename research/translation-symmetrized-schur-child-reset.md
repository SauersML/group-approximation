---
rg: 2
id: translation-symmetrized-schur-child-reset
kind: claim
title: A finite translation-symmetrized overgroup balances every Schur child type
distinct_from:
  schur-child-center-sign-flip-is-group-automorphism: that pairs the two corrected branches while fixing the selector character; this also balances all selector characters.
  branch-controlled-pauli-selector-reset: that tries to use raw branch spectral controls inside one packet and balances the wrong decomposition; this uses translated packet copies and acts on genuine child types.
  finite-selector-gadget-induction-barrier: that says no finite overgroup can delete an unwanted selector character; this keeps every character and forces them to occur with equal multiplicity.
---

Fix a Schur compiler block

```text
U_f(x)=(c_ij+sum_l a_(ij,l)x_l)_(i,j=1)^N
```

which is invertible for every `x in X=F_2^k`, and let `C_f=B_f^Q` be its
`Q` child. There is an explicit finite class-two `2`-group `N_f` containing
copies `C_f^(a)` indexed by `a in X`, all sharing the same central
involutions `J,z_1,...,z_k`, such that copy `a` has commutator pencil
`U_f(x+a)` on selector sector `x`. Generators belonging to distinct copies
commute modulo the shared center.

For every `b in X`, the formulas

```text
tau_b(J)=J,
tau_b(z_l)=J^(b_l) z_l,
tau_b(p_i^(a))=p_i^(a+b),
tau_b(q_j^(a))=q_j^(a+b),
tau_b(q_*^(a))=q_*^(a+b)                              (TSR1)
```

define commuting involutive automorphisms of `N_f`. For every `a`, there is
also an involutive branch automorphism

```text
eta_a(q_*^(a))=Jq_*^(a)                                (TSR2)
```

fixing every other named generator. The translations permute these branch
flips. Hence they form a finite automorphism group `W_f`, and

```text
R_f=N_f semidirect W_f                                  (TSR3)
```

is a finite ordinary group containing the original child `C_f^(0)`.

Let `D=2^N`. In every exact finite-dimensional representation of `R_f` on
which `J=-1`, the restriction to `C_f^(0)` has the same multiplicity for
every genuine child-simple type `(x,+/-)`. Equivalently, if `m_(x,+/-)` are
the multiplicities labelled by the selector character and corrected child
center, then

```text
m_(x,+)=m_(x,-)=dim(H)/(2^(k+1)D)                    (TSR4)
```

for every `x`. Thus the entire child type vector is balanced, although no
nonlinear corrected center is named as a group element.

For approximate representations of any finite amalgam containing `(TSR3)`,
fixed-table flexible exactification and common-subgroup polar alignment bound
the normalized weighted `L1` distance from the balanced vector in `(TSR4)`
by `C sqrt(E)`. Amalgamating `R_f` to a marked base over `C_f^(0)` preserves
the base and its nonidentity marked word by normal form.

This is a local reset, not a global multiplicity amplifier. A finite graph of
these reset groups still admits stationary regular type flow. The next step
must use the reset only inside a Toeplitz/compressor recurrence or another
non-one-dimensional holonomy mechanism.

The remaining flow is now computed exactly by
`symmetrized-reset-collapses-schur-flow-to-one-ray`: compatibility with the
full packet leaves only one scalar ray and charges every transverse type
direction. The compressor does not need to control an arbitrary finite
representation-ring polytope.
