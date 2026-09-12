---
rg: 2
id: two-pauli-anchors-localize-arbitrary-normalizer-twists
kind: claim
title: Two coordinate Pauli anchors localize normalizers with unrelated multiplicity twists
distinct_from:
  kazhdan-transitive-pauli-actor-localizes-one-mixed-word: that averages an actual actor representation; this uses only a classical gap on Weyl labels and allows the multiplicity unitaries to satisfy no actor relations.
  toeplitz-transitive-pauli-actor-repairs-relative-cell: that exactifies a whole finite actor table and uses four orbit prototypes; this needs only individual normalizer covariance and two coordinate Pauli anchors once the old Pauli factor is exact.
  all-representation-expansion-keeps-macroscopic-multiplicity-swap: that refutes localization from normalizer commutators alone; the two physical Pauli anchors here control the invariant obstruction.
---

Let `n>=3`, `d=2^n`, `r>=1`, and use normalized Hilbert--Schmidt norms.
Set `V=F_2^n` and `Omega=(V direct-sum V*)\{0}`.  Let `S` be a symmetric
generating multiset of `GL_n(2)` whose action

```text
s.(v,phi)=(sv,phi s^(-1))
```

satisfies the classical Poincare inequality

```text
avg_(s in S)||f-s.f||_(ell^2(Omega))^2
 >= kappa ||f-Pi f||_(ell^2(Omega))^2.                    (TAL1)
```

Here counting measure is unnormalized and `Pi` averages on each orbit.
The constant `kappa>0` can be chosen independent of `n`, with `|S|`
bounded, by the bounded Cayley expanders for `GL_n(2)`.

Let `C_s` be the natural permutation implementer on `ell^2(V)`, and let
`X_1,Z_1` be the first coordinate Pauli pair in the exact old factor
`M_d tensor I_r`.  Write `E` for conditional expectation onto `I_d tensor M_r`.
For any matrix `T` and arbitrary unitaries `B_s in U(r)`, put

```text
D_s=C_s tensor B_s,
A=||[T,X_1 tensor I]||_2^2+||[T,Z_1 tensor I]||_2^2,
e^2=avg_(s in S)||[T,D_s]||_2^2.
```

Then

```text
||T-E(T)||_2 <= sqrt(A/2)+(1+sqrt(2)) e/sqrt(kappa).       (TAL2)
```

The `B_s` need not extend to a representation, satisfy inverse relations,
or have any gap.  No multiplication table of the actor is required.

There is also a version requiring only approximate normalizer covariance.
Let `D_s in U(dr)` be arbitrary, let `T` be a contraction, and let `P_j`,
`1<=j<=2n`, list all coordinate Pauli generators.  Define `A,e` as above
using these actual `D_s`, and define

```text
b^2=avg_(s in S) sum_(j=1)^(2n)
 ||D_s(P_j tensor I)D_s^*-(C_s P_j C_s^* tensor I)||_2^2.  (TAL3)
```

Then

```text
||T-E(T)||_2
 <= sqrt(A/2)+(1+sqrt(2))(e+sqrt(2)b)/sqrt(kappa).          (TAL4)
```

The sum in `(TAL3)` is deliberately not divided by `2n`.  Bounding every
covariance row by `epsilon` gives `b<=sqrt(2n)epsilon`; this statement
does not claim a constant cost in the maximum single-row defect.

This is a relative matrix lemma, not a nonhyperlinear-group witness.
Its application still requires an exact old Pauli factor and derivations
of the indicated covariance and commutator checks from the chosen group
presentation, with the losses required by that route.

The exact presentation boundary is computed in
`anchored-pauli-extension-splits-off-its-payload`: an actor acting on one
finite Pauli frame, together with payload generators centralizing the actor
and the two anchors, presents `(P_n semidirect Q) times L`.  Its
hyperlinearity is exactly that of its actor and payload inputs.  Thus
localization alone, even with the correct anchors, does not impose a
one-sided multiplicity loss; that loss needs an additional mixed relation.

DERIVATION
two-pauli-anchor-norm-profile-proof
