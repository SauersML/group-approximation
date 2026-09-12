# Rank-four plan, check (ii): completeness, and how the Leavitt relation reaches root data

Lane `w4-r4-complete` (family R4), 2026-09-12.

Plan 1 of `research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md` (node
`rank-four-isometry-relations-give-corner-cuntz-family`) listed check (ii): the completeness relation
`S_0 T_0 + S_1 T_1 = e` for a corner Leavitt family in a rank ultraproduct `M`.

This artifact covers four things:
1. why check (ii) drops out;
2. the exact form in which `s_0 t_0 + s_1 t_1 = 1` reaches root data;
3. the open question of whether completeness has to enter the construction at all;
4. a scope note on reading `EL_3` models as `EL_4` models.

## 1. Completeness is not needed (credited)

Three lanes found this independently, and each landed before this lane's c22ebb8e32. Their nodes
are canonical:

* `toeplitz-isometry-defects-have-total-rank-at-least-one` (w4-r4-approx, b7b0e9d38). For any
  Sylvester matrix rank function, an idempotent `e`, and `S_j, T_i in eAe`:
  `rk(e) <= rk(e - T_0 S_0) + rk(e - T_1 S_1) + rk(T_1 S_0)`.
* `nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple` (w4-r4-corner, 5d14c96d8).
* Lead integration, Sections L1 and L2 of the plan artifact (322f1b031).

**The retired variant.** c22ebb8e32 landed a four-relation variant:
`rk(x) <= sum_ij rk(delta_ij x - T_i S_j)` for `S_j in xM` with `x` arbitrary and `T_i`
unconstrained. The proof counts rank through the row `[S_0 S_1] = x [y_0 y_1]`. That landing also
carried a relaxed open target and a route. All of it duplicated L1–L2, and it is retired in the
following landing. The variant follows from the toeplitz node:
1. Replace `x` by its left projection `e`. `M` is von Neumann regular, `eM = xM` and `rk(e) = rk(x)`.
2. Replace `S_j` by `S_j e` and `T_i` by `e T_i e`.
3. None of the defect ranks increases.

**What check (ii) can still mean.** In a rank ultraproduct, nothing. Every construction is a proof
by contradiction, and no family with `rk(e) > 0` exists on which completeness could be tested.
Completeness still has content only in test rings without a faithful rank function, such as
`End_F(V)` for infinite-dimensional `V`, or group algebras. Section 2 is about those.

## 2. How completeness reaches the root data (characteristic two)

**Setting.**
- `K` has characteristic two, `R = L_K(1,2)` and `e_i = s_i t_i`.
- `M` is any unital `K`-algebra.
- `sigma : EL_n(R) -> M^x` is a homomorphism, `n >= 3`, and `n_ab(r) = sigma(x_ab(r)) - 1`.
- For distinct `a, b, c`: `A_i = n_ab(s_i)`, `B_i = n_bc(t_i)`, `E_i = n_ac(e_i)`, `N = n_ac(1)`.

**Proposition 3.**

```text
(a)  N = E_0 + E_1 + E_0 E_1,   E_0 E_1 = E_1 E_0,   N^2 = E_i^2 = 0 ;
(b)  E_i = A_i B_i + B_i A_i + A_i B_i A_i + B_i A_i B_i + A_i B_i A_i B_i ;
(c)  A_0 B_0 + A_1 B_1 = N + E_0 E_1 + rho_0 + rho_1,
     rho_i = B_i A_i + A_i B_i A_i + B_i A_i B_i + A_i B_i A_i B_i .
```

*Proof.*
- **(a)** `e_0 + e_1 = 1`, and the root subgroup is additive, so
  `x_ac(1) = x_ac(e_0) x_ac(e_1)`, the two factors commute, and `1 + N = (1 + E_0)(1 + E_1)`. In
  characteristic two `x_ab(r)^2 = 1`, so `n_ab(r)^2 = sigma(x_ab(r))^2 - 1 = 0`.
- **(b)** Use the Steinberg relation `[x_ab(s_i), x_bc(t_i)] = x_ac(s_i t_i)`. With `X = 1 + A`,
  `Y = 1 + B`, `X^(-1) = X`, `Y^(-1) = Y` and `A^2 = B^2 = 0`, we get `XY = 1 + A + B + AB`.
  Squaring modulo two gives `XYXY - 1 = AB + BA + ABA + BAB + ABAB`.
- **(c)** Sum (b) over `i` and substitute (a). QED

**Reading.**
1. **Natural models.** Take `n_ab(r) = rho(r) E_ab` for a unital ring homomorphism `rho : R -> P`.
   Every reversed product contains `E_bc E_ab = 0` or `E_ac E_ab = 0`, and `E_0 E_1` contains
   `E_ac E_ac = 0`. So (c) reads `sum rho(s_i) rho(t_i) = 1` at position `(a, c)`. These models have
   `D = 0`.
2. **General models.** The root-level completeness defect is exactly `E_0 E_1 + rho_0 + rho_1`. The
   term `E_0 E_1 = N - E_0 - E_1` is the failure of the root map to be additive on the two halves
   of `1`, and `rho_0 + rho_1` are the reversed-order terms. Among the Steinberg relations, the ring
   enters only through additivity of each root map and the commutator formula. Relations of `EL_n(R)`
   beyond Steinberg are not analyzed here.
3. **Return operators.** `N` is square-zero, so no root-level completeness sum is a nonzero
   idempotent. In a regular ring, take `W` with `N W N = N`. Then `e = N W` is idempotent, and for the
   placement `S_i = A_i`, `T_i = B_i W` the completeness defect is exactly
   `(E_0 E_1 + rho_0 + rho_1) W`. This is an illustration of the mechanism only; check (i) for this
   placement sits in a different corner. The lead's baseline candidate (L3) behaves the same way:
   each defect is `sigma` of a nonzero element of `ker pi`.

Node: `leavitt-completeness-transport-formula-for-root-data`, with route
`leavitt-completeness-transport-formula-proof`.

## 3. Must completeness enter the construction? (open)

Let `C_2 = <s_0, s_1, t_0, t_1 | t_i s_j = delta_ij>` be the Cohn algebra over `F_2`, and put
`q = 1 - s_0 t_0 - s_1 t_1`, so `C_2 / (q) = R`. Every rank model of `EL_3(R)` pulls back to a model
of `EL_3(C_2)` with the same `N_23 N_12`. So an argument that uses only the Cohn relations proves
`N_23 N_12 = 0` for every rank model of `EL_3(C_2)`.

**Open:** `cohn-coefficient-el3-rank-models-satisfy-two-root-identity`.
- **If true,** it gives the binary gate.
- **If false,** completeness has to enter the construction of the corner data for any proof of the
  binary gate. The final contradiction needs only the three Toeplitz relations.

**What is known.**
- `C_2` has no unital rank model: take the toeplitz node with `e = 1`.
- `q` is a minimal idempotent: `t_i q = 0 = q s_j` and `q C_2 q = F_2 q`. So `g -> 1 + q(g - 1)`
  embeds `SL_3(F_2)` in `EL_3(C_2)`.
- The models trivial on `ker(EL_3(C_2) -> EL_3(R))` are exactly the pulled-back ones.

**Relation to L4b.** L4b asks whether a proof of (iii) must use the Leavitt relations. This asks the
same thing for the completeness relation specifically, with the Cohn algebra as the test ring.

## 4. Scope note: reading an `EL_3` model as an `EL_4` model

This is compatible with w4-r4-adversary's frame note (9fd9898e8e): `D` has to be read in the block
frame throughout, and the audit found no frame error.

One further point. The abstract isomorphism `phi : EL_4(R) -> EL_3(R)` does not carry the block
`EL_3(R) <= EL_4(R)` onto itself, so the plan runs on the `R^x` model `tau = sigma o phi` and handles
its block defect. Triviality still transfers back to `sigma`:
- the normal closure of the block is all of `EL_4(R)`;
- for example `x_14(r) = [x_12(r), x_24(1)]`, `x_24(r) = [x_21(r), x_14(1)]` and
  `x_34(r) = [x_31(r), x_14(1)]` are each a commutator of a block element with another element, so
  each lies in that closure;
- so `tau` trivial on the block gives `tau` trivial, and hence `sigma` trivial.
