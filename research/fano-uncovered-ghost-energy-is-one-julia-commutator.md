---
rg: 2
id: fano-uncovered-ghost-energy-is-one-julia-commutator
kind: claim
title: All uncovered Fano ghost energy is one Julia commutator
distinct_from:
  ghost-completed-fano-naimark-wordizes-one-local-predicate: that exactly wordizes the ghost projection in one chosen context representation; this stacks the still-uncovered ghost columns of every context on the one common game source.
  free-julia-grading-carries-one-gram-at-canonical-quarter-mass: that reads one arbitrary off-diagonal Gram contraction from two literal reflections; this identifies the particular contraction whose squared norm is exactly the remaining forbidden-weighted carrier leakage.
  common-partial-isometry-swap-game-compiler: that asks for an ordinary finite-packet promotion of all game rows; this is only the exact state-dependent operator colligation and does not authenticate it in arbitrary group representations.
---

**ESTABLISHED OPERATOR REDUCTION; AUTHENTICATION REMAINS OPEN.**  Let
`H` be finite dimensional, let `S` be a contraction on `H`, and let the
finitely many `R_*` contexts have weights `mu_c>=0` with

```text
sum_c mu_c=1.
```

For context `c`, let `F_c` be its unique ghost projection and let `P_c` be
the selected local carrier.  Assume only

```text
P_c=P_c^*=P_c^2,       F_c=F_c^*=F_c^2,       [P_c,F_c]=0.
```

Put

```text
A_c=(1-P_c)F_cS,
T:H -> direct-sum_c H,
T xi=(sqrt(mu_c) A_c xi)_c.                           (FGJ1)
```

Then `T` is a contraction and its normalized Hilbert--Schmidt mass is
exactly the uncovered forbidden-weighted carrier energy:

```text
tau_H(T^*T)
 =sum_c mu_c ||(1-P_c)F_cS||_(2,H)^2
 =L_forb.                                             (FGJ2)
```

Indeed, commutation makes
`F_c(1-P_c)F_c=(1-P_c)F_c` a projection.  Therefore

```text
T^*T=S^*(sum_c mu_c (1-P_c)F_c)S <= S^*S <= 1,
```

and taking the normalized trace gives `(FGJ2)`.

Let `K=direct-sum_c H`, let

```text
D_T=(1-T^*T)^(1/2),          D_(T^*)=(1-TT^*)^(1/2),
j_T=[[D_T,       T^*],
     [T,    -D_(T^*)]],
z=diag(1_H,-1_K).                                     (FGJ3)
```

The standard defect-operator identity

```text
T D_T=D_(T^*) T
```

shows that `j_T` is a self-adjoint unitary.  For the one ordinary
commutator word

```text
w_T=z j_T z j_T                                      (FGJ4)
```

and normalized trace on `H direct-sum K`, one has the exact identity

```text
||w_T-1||_(2,H direct-sum K)^2
       =8/(m+1) L_forb,                               (FGJ5)
```

where `m` is the number of contexts.  Indeed the positive-to-negative
off-diagonal block of `j_T` is `T^*`, so the general two-reflection identity
gives `8||T||_(2,H direct-sum K)^2`; normalization changes
`Tr_H(T^*T)/dim(H)` by the factor `1/(m+1)`.

This is an exact state-dependent nonlinear transducer for the entire
residual left side of `(CPS12)`, not merely for one context.  If the perfect
model has `L_forb=0`, then `T=0`, `j_T=z`, and `(FGJ4)` is exactly one.  No
rounding, cap-profile choice, or dimension-dependent constant occurs.

## The strictly smaller constructive target

The local nonlinear predicate is therefore not the remaining Fano compiler
problem: `ghost-completed-fano-naimark-wordizes-one-local-predicate` already
wordizes each `F_c`, and `(FGJ1)--(FGJ5)` package all leakage left after
those local rows into one reflection word.  The smallest unsupplied cell is
an **aggregate Julia colligation authenticator**:

> On one fixed `(m+1)`-role register, authenticate a literal grading `z`
> and a literal reflection `j` so that, in canonical finite-matrix models,
> the off-diagonal block of `j` is `o(1)`-close to the row contraction `T`
> in `(FGJ1)`, while every exact perfect model extends using `j_T`.

Once that one correlation is authenticated, imposing `zjzj=1` forces
`L_forb=o(1)` by `(FGJ5)`, which is stronger than the remaining return
inequality `(CPS12)`.  Existing predicate and consistency rows then feed the
one-Gram game gap.

This target is strictly smaller than perfect-completeness LCS itself: the
operator `j_T` always exists for arbitrary input data, and the theorem makes
no soundness claim about a group presentation.  The missing statement is
only that ordinary finite syntax can force one representation-specific
off-diagonal correlation.  A finite router table cannot do this:
`ghost-finite-router-induced-sector-or-perfect-corner` supplies its induced
ghost countersector.  Scalar marked selector sectors cannot do it either:
`tensor-affine-selector-pattern-barrier` closes their realized patterns
under odd tensor products and therefore restores the affine ghost.  Thus a
successful authenticator must be genuinely non-scalar and cross-context;
adding another local truth table is provably the wrong level.

## Special-structure reduction beyond the aggregate colligation

`uncovered-ghost-reflections-directly-pay-the-fano-row` shows that the
aggregate Julia authenticator is not minimal. Put

```text
Q_c=(1-P_c)F_c,
r_c=diag(1-2Q_c,1)
```

in the existing common D8 grading. Then

```text
4||Q_cS||_(2,H)^2<=||r_cjr_cj-1||_2^2,
L_forb<=(1/4)sum_c mu_c||r_cjr_cj-1||_2^2.
```

No block encoding of `T`, coherent context amplitudes, controller
orientation, or corner return is required. The remaining syntax is only to
wordize the positive-block reflection `1-2(1-P_c)F_c`.

That reflection is `-1` on exactly the joint sign sector
`P_c=0,F_c=1`, so it is nonaffine and cannot be a word in commuting
selector and central signs. A finite nonabelian router realizes it in one
chosen type but retains the induced uncovered sector in another exact
representation. Thus the colligation problem reduces to the established
nonlinear hybrid-reflection authentication gate; a central-sign finite
register does not evade it.

That remaining literal-word target has a sharp infinite-actor firewall.
`fano-hybrid-reflection-has-a-universal-regular-hs-gap` expands

```text
1-2(1-P_c)F_c=(1/2)(1+f_c-p_c+p_cf_c)
```

in the marked regular Fourier corner and proves squared normalized-HS
distance at least `1` from every ordinary group word, even after arbitrary
HNN, solution-group, or self-similar enlargement. Its odd-tensor argument
also produces the wrong forbidden output whenever the three honest scalar
sectors are separately realizable. Hence no further exact reflection-product
identity can authenticate it. Any surviving use of the direct payment must
replace literal wordization by a genuinely matrix-only, sector-entangled
rank/type inference unavailable in the regular factor.
