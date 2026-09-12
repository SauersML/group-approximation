---
rg: 2
id: rank-models-of-el3-satisfy-the-two-root-identities
kind: claim
title: Every rank model of EL_3 over a simple algebra with no rank model satisfies N_12^2 = 0 and N_23 N_12 = 0
distinct_from:
  el3-rank-models-factor-through-ring-rank-models: that asserts every such model is trivial; this asserts two product identities among the six unit root unipotents. The two are equivalent through the routes two-root-identities-give-el3-ring-rigidity and el3-ring-rigidity-gives-the-two-root-identities, which form an intended cycle.
  el3-unit-root-matrix-units-iff-two-root-identities: that is the established equivalence between the identities and the matrix-unit hypothesis for any single model; this is the open assertion that every rank model over the gate's coefficient rings satisfies them.
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

**OPEN.** Let `p` be a prime and `R` a simple unital algebra over a field of characteristic
`p` with no unital ring homomorphism into any rank ultraproduct over a field of characteristic
`p`. Let `M` be such a rank ultraproduct and `sigma : EL_3(R) -> M^x` a homomorphism, and put
`N_ab = sigma(x_ab(1)) - 1`. Then

```text
N_12^2 = 0        and        N_23 N_12 = 0 .
```

In characteristic two the first identity is automatic. For `R = L_(F_2)(1,2)` this is the
single identity `(x_23(1) - 1)(x_12(1) - 1) = 0` in every characteristic-two rank model of the
Leavitt unit group. It is equivalent to `el3-rank-models-factor-through-ring-rank-models`, whose
payoff is `non-linear-sofic-group`.

## Attempts

- **Reduction: landed (gk-rk-unipotent, 2026-09-12).**
  - `el3-unit-root-matrix-units-iff-two-root-identities`: the identities are exactly the
    matrix-unit hypothesis.
  - `matrix-unit-rank-models-extract-ring-rank-models`: matrix-unit models extract a ring rank
    model, or are trivial.
  - So this claim and the gate claim are equivalent (artifact Section 3).
- **Group relations over finitely represented coefficients cannot prove it.**
  `fd-represented-coefficients-violate-two-root-identities` gives honest regular-representation
  models of `EL_3(S)` with `N_23 N_12 != 0` whenever `S` maps into some `M_n(F_p)`. That covers
  the Toeplitz subring `<s_0, t_0 | t_0 s_0 = 1>`. `gk-l-gate-pos`'s natural tensor dual model
  of `EL_3(F_2[t])` also violates the identity. A proof must use coefficients generating a
  subring with no finite-dimensional representation, such as a unital Leavitt family, or the
  no-rank-model hypothesis beyond relations.
- **Five-term expansion: dies.** `N_13 = XY + YX + XYX + YXY + XYXY` with `X = N_12`,
  `Y = N_23` (characteristic two). No Steinberg relation among the unit root elements isolates
  `YX`.
- **Self-similar displacement counting: dies.** On `SL_3(F_2)` the model is the diagonal
  restriction of the commuting pair `(sigma iota_0, sigma iota_1)`. Equal displacement of
  `(x,1)`, `(1,x)` and `(x,x)` forces free-type or trivial behavior on outer tensor components,
  and free-type components violate the identity. Modules that are not outer tensor products
  escape, so uniform displacement does not force the identity (artifact Section 5).
- **Same-row and same-column identities first: dies.** From the squares, `N_12 N_13 = 0` and
  `N_12 N_32 = 0` leave the residual `N_12 N_21 N_32 (1 + N_21)`, which they do not force.
- **Isometry commutator relations: new handle, not yet connected (gk-ri-nofd, 2026-09-12).**
  `leavitt-isometry-commutators-constrain-el3-rank-models` records, from `t_i s_j = delta_ij`,
  the reversed identities on `A_i = n_12(t_i)`, `B_j = n_23(s_j)`:
  `i != j` gives `A_iB_j + B_jA_i + A_iB_jA_i + B_jA_iB_j + A_iB_jA_iB_j = 0`, and `i = j` gives
  the same expression equal to `n_13(1)`. These use coefficients with no finite-dimensional
  representation, the input required by `fd-represented-coefficients-violate-two-root-identities`,
  and were unused by the dead attempts. Open bridge: the target `N_23 N_12` carries coefficient
  `1`; `1 = e_0 + e_1` with `e_i = s_i t_i` gives
  `1 + N_12 = (1+n_12(e_0))(1+n_12(e_1))`, but `1` is not an additive combination of the `t_i`
  and `x_12` of a product is not a commutator, so no group-relational bridge is known.
- **Extraction is a corner Leavitt family; single-corner route circular (gk-ri-nofd).** A unital
  `R -> eMe` is an order-two Leavitt family in the corner `eMe`; by [TR] Theorem D that corner is
  a rank ultraproduct, so `leavitt-algebra-has-no-unital-rank-model` already forbids it
  (impossibility half established). Telescoping the four partial isometries in one Peirce corner
  needs the block form, i.e. `N_23 N_12 = 0`, so that route assumes its conclusion. A
  non-circular assembly of the four partial isometries from a model with `N_23 N_12 != 0` is the
  open content. Artifact `research/artifacts/leavitt-isometry-commutator-relations-2026-09-12.md`.
