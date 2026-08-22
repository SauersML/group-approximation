---
rg: 2
id: intrinsic-finite-green-commutator-step-has-the-correct-tangent
kind: claim
title: An intrinsic finite-Green commutator step realizes the strict tangent contraction
distinct_from:
  tangent-commutator-covariance-bypasses-code-riesz-endpoint: that constructs the finite-time inverse in exact tangent coordinates; this writes it using only the current reflection tuple and group-word residuals.
  random-code-anchor-pinchings-contract-exact-transverse-energy: that randomly pinches by coordinate anchors; this uses the deterministic CP Green polynomial and a simultaneous tangent conjugation step.
  balanced-overlay-diffuse-square-function-newton: that asks for a global nonlinear basin theorem; this proves the intrinsic map and its exact derivative but isolates the still-missing pre-basin coercivity and sparse-layer estimate.
---

ESTABLISHED INTRINSIC LINEARIZATION.  For a reflection tuple
`Q=(Q_1,...,Q_L)`, define

```text
 beta_ij(Q)=(I-(Q_iQ_j)^2)/2,
 c_i(Q)=(1/L)sum_j beta_ij(Q),                          (IFG1)

 A_Q(T)=(1/L)sum_j (T+Q_jTQ_j)/2,
 G_(Q,K)=sum_(t=0)^(K-1) A_Q^t.                        (IFG2)
```

Put `g_i=G_(Q,K)c_i`, take the skew tangent generator

```text
 k_i=(g_i-g_i^*)/4,                                    (IFG3)
```

and set

```text
 F_K(Q)_i=exp(k_i)Q_i exp(-k_i).                        (IFG4)
```

This map is defined before choosing characters or a nearby exact tuple and
preserves the reflection equations exactly.  Its building blocks have
dimension-free operator-space bounds: `A_Q` is ucp, `G_(Q,K)` has cb norm
at most `K`, and the normalized average in `(IFG1)` is row/column
contractive on the endpoint-odd commutator range.

Let `S` be any exact commuting code tuple and differentiate along reflection
curves `Q_i(epsilon)=S_i+epsilon h_i+O(epsilon^2)`.  Since the commutator
vanishes at `S`,

```text
 d beta_ij|_S(h)=-(1/2)S_iS_j
     ([h_i,S_j]+[S_i,h_j]),                            (IFG5)
```

which is exactly the tangent trivialization `(TCB1)`.  Therefore
`dF_K|_S` acts on the transverse tangent quotient as the finite CP-Green
error operator.  For a code of relative distance `delta`,

```text
 ||dF_K|_S||_(2,transverse) <=(1-delta)^K.              (IFG6)
```

The simultaneous-conjugation tangent is fixed, as it must be.

For fixed `K`, expanding `(IFG4)` by Duhamel gives a dense-layer remainder
which is quadratic in the correction row/column square function, with a
constant depending only on `K`.  The estimate uses only normalized
averages and the cb quadratic complete-pair bound, so it is independent of
`L` and matrix dimension.  For selfadjoint contractions, `(TCB7)` adds an
`O(epsilon_inv^(1/2))` forcing term and the terminal sign ledger returns to
reflections.

This does not yet prove a global strict energy decrease from the diffuse
square-function hypothesis.  Equation `(IFG6)` is a derivative statement
at the exact code locus.  Away from that locus the missing terms are now
precise:

1. a Polyak--Lojasiewicz/coercivity estimate on the retained low-`K_a`
   sector comparing the intrinsic correction row `g` with complete-pair
   energy without first naming code characters;
2. control of the first-order damage caused by the coordinate-dependent
   conjugators `k_i` in the sparse parity and equality layers.

The complete-pair nonlinear remainder itself and the involution forcing are
not additional gates.

The low-`K_a` qualification is necessary:
`clifford-packets-are-stationary-for-intrinsic-green-step` shows that a
pairwise anticommuting Clifford packet has maximal pair energy but zero
intrinsic correction.  Its anchor square function is instead
`(1-1/L)I`, so the regularized aggregate cut removes it completely.
