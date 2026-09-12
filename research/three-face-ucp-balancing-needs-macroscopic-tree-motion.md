---
rg: 2
id: three-face-ucp-balancing-needs-macroscopic-tree-motion
kind: claim
title: Every simultaneous triangular ucp balance moves one canonical tree-face letter by a fixed amount
distinct_from:
  kernel-relator-forces-two-edge-ucp-section-gap: that treats a ucp section of the finite closing-face quotient with range in the edge amalgam; this applies to every ucp map on the operator system containing all three finite face algebras, requires no right-inverse condition, and locates the forced correction on one of the two tree faces.
  triangle-relator-extension-admits-local-ucp-sections: that asks for local ucp right inverses and permits macroscopic ideal corrections; this proves such corrections cannot be perturbative around the canonical tree-face lift, but does not exclude a noncanonical simultaneous balance.
  operator-system-face-colimit-need-not-have-concrete-group-order: that separates universal and concrete orders in an abstract two-axis cross; this gives an explicit positive matrix in the concrete triangle face system whose ucp lifts force a quantitative tree-face displacement.
---

**ESTABLISHED.**  Use the triangle notation

```text
A=C^*(G_0),                    Q=C^*(Lambda),
S_Delta=C^*(P_12)+C^*(P_23)+C^*(P_13) subset Q,
E=P_1 *_(P_0) P_3 subset G_0, q_E:E->>P_13.
```

Let

```text
n=a_1 ... a_L in ker(q_E)\{1},       a_j in P_1 union P_3
```

be reduced, and put

```text
v_j=u_(q_E(a_j)) in C^*(P_13) subset S_Delta,
w_j=u_(a_j) in A.                                      (TFB1)
```

Every ucp map `Phi:S_Delta->A` -- with no lifting or right-inverse
hypothesis -- satisfies

```text
max_(1<=j<=L) ||Phi(v_j)-w_j|| >= 2/L^2.                (TFB2)
```

Indeed, restrict `Phi` to the unital C-star subalgebra `C^*(P_13)` of
`S_Delta`.  The Stinespring multiplicative-domain calculation in
`kernel-relator-forces-two-edge-ucp-section-gap` uses only that this
restriction is ucp and that `v_1...v_L=1`; it never uses that its range lies
in `C^*(E)` or that it is a section.  If
`epsilon=max_j ||Phi(v_j)-w_j||`, that calculation gives

```text
2=||1-u_n||
 <= (L-1) sqrt(2 epsilon)+L epsilon.                    (TFB3)
```

The right side equals `2` at `epsilon=2/L^2` and is increasing, proving
`(TFB2)`.  Here `||1-u_n||=2` because `E` embeds in the virtually free
tree group `G_0`, its free kernel is torsion-free, and nontrivial `n` has
infinite order.

This is an explicit finite matrix-order obstruction.  Set

```text
g_0=1,       g_k=q_E(a_1...a_k) in P_13,       g_L=1.
```

Then

```text
G_n=[u_(g_i^(-1)g_j)]_(0<=i,j<=L) >=0
       in M_(L+1)(C^*(P_13)) subset M_(L+1)(S_Delta).    (TFB4)
```

For every ucp `Phi`, positivity of `Phi^(L+1)(G_n)` is exactly the Gram
positivity behind `(TFB3)`.  The successive edge entries of `(TFB4)` are the
`v_j` (up to adjoint), while the repeated endpoint is `1`.  Thus the raw
canonical path lift, whose successive entries are `w_j` and whose path
holonomy is the nontrivial `u_n`, lies at least `2/L^2` from the ucp cone.

In particular, if `t:S_Delta->A` is any unital self-adjoint linear lift that
is canonical on both tree faces, then `t(v_j)=w_j` for every `j` and

```text
dist_cb(t,UCP(S_Delta,A)) >= 2/L^2.                      (TFB5)
```

Since a letter from `P_1` also belongs to the `P_12` face and a letter from
`P_3` also belongs to the `P_23` face, the displaced entry in `(TFB2)` is
literally a tree-face entry.  Consequently simultaneous three-face balancing
cannot be obtained by a small completely-positive correction of the two
canonical tree-face orders.  A positive LLP construction must make an
`O_L(1)` ideal-valued move on at least one tree face and store the cycle
holonomy in genuinely noncanonical, nonorthogonal data.

**Exact scope.**  This does not refute local ucp splitting.  The finite face
system may still admit a ucp right inverse whose tree-face values make the
macroscopic movement required by `(TFB2)`, and a local section is under no
obligation to be close to the canonical lift.  The theorem closes only the
perturbative simultaneous-balancing strategy.

DERIVATION
kernel-cycle-gram-forces-three-face-correction-floor
