# Rank-four plan, check (ii): completeness is dispensable

Lane `w4-r4-complete` (family R4), 2026-09-12. This artifact addresses Plan 1 of
`research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md`, recorded as the node
`rank-four-isometry-relations-give-corner-cuntz-family`. That plan asks for a corner Leavitt family
in a rank ultraproduct `M`, subject to three checks:

- (i) `T_i S_j = delta_ij e`;
- (ii) `S_0 T_0 + S_1 T_1 = e`;
- (iii) `rk(e) = rk(D) > 0`, where `D = N_23 N_12`.

This lane owns check (ii). The answer is structural. In a rank ultraproduct the contradiction never
uses completeness, check (i) only has to hold up to a rank budget, and check (iii) is automatic once
the corner is supported in `D` itself. Section 2 records how the Leavitt relation reaches the root
data, for test rings where completeness still means something. Section 3 is a strength filter for
purely relational assemblies. Section 4 is the open calibration: whether completeness has to enter
the construction at all.

## 0. Setting and conventions

`M = prod_omega M_(n_k)(F) / d_omega`, where `F` is any field, `d_omega` is the ideal of
normalized-rank-null sequences, and `rk(x) = lim_omega rank(x_k)/n_k`. For a rectangular matrix
`X in M_(p x q)(M)` put `rk(X) = lim_omega rank(X_k)/n_k`, with `X_k` a `p n_k x q n_k` matrix
over `F`. This is well defined, because a null perturbation of an entry changes the rank by a null
amount. Matrix rank over a field gives:

- (P1) `rk(XY) <= min(rk X, rk Y)`;
- (P2) `rk(X + Y) <= rk X + rk Y`;
- (P3) the rank of a block matrix is at most the sum of the ranks of its blocks;
- (P4) `rk(diag(x, x)) = 2 rk(x)`;
- (P5) `rk(x) = 0` implies `x = 0` in `M`.

`M` is von Neumann regular, since `prod_omega M_(n_k)(F)` is regular and so is every quotient of a
regular ring. So every `x in M` has a left projection: an idempotent `e` with `eM = xM`, and then
`rk(e) = rk(x)`.

## 1. The Cohn rank inequality

**Theorem 1.** Let `x in M`, `S_0, S_1 in xM` and `T_0, T_1 in M`. Then

```text
rk(x)  <=  sum over i, j in {0,1} of  rk(delta_ij x - T_i S_j) .
```

The same bound holds when instead `T_0, T_1 in Mx` and `S_0, S_1` are arbitrary. It also holds for
square matrices over `F` with normalized rank, with the same proof, so it can be used at a finite
level before passing to the ultraproduct.

*Proof.* Write `S_j = x y_j`. Form the row `S = [S_0  S_1] = x [y_0  y_1]` and the column
`T = [T_0 ; T_1]`.
1. By (P1), `rk(TS) <= rk(S) <= rk(x)`.
2. `TS` is the `2 x 2` matrix with entries `T_i S_j`, so `diag(x, x) = TS + Delta`, where
   `Delta_ij = delta_ij x - T_i S_j`.
3. By (P4), (P2) and (P3):

   ```text
   2 rk(x) = rk(diag(x, x)) <= rk(TS) + rk(Delta) <= rk(x) + sum rk(Delta_ij) .
   ```

For the dual version, use `rk(TS) <= rk(T) <= rk(x)` instead. QED

**Corollary 2 (corner Cohn families vanish).** If `S_j in xM` and `T_i S_j = delta_ij x` for all
`i, j`, then `x = 0`. In particular, if `e` is an idempotent and `S_j, T_i in eMe` satisfy
`T_i S_j = delta_ij e`, then `e = 0`. The proof uses no completeness relation, no idempotency of `x`,
and no condition on where `T_i` lives.

This is the rank count `rank(TS) <= n < 2n` that
`leavitt-isometry-commutators-constrain-el3-rank-models` uses for finite-dimensional
representations. What is new here is its form: a defect inequality with left support in an
arbitrary element.

Taking `x = 1` recovers the fact that the Cohn algebra `C_2 = <s_0, s_1, t_0, t_1 | t_i s_j = delta_ij>`
has no unital homomorphism into any rank ultraproduct.

## 1.1 Consequences for Plan 1

**(a) Completeness is dispensable.** The `D != 0` branch of
`leavitt-el3-triviality-via-rank-four-cuntz-family` already reaches its contradiction from check (i)
together with `rk(e) > 0`, by Corollary 2. That branch needs none of the following:
- the unital homomorphism `R -> eMe`;
- Theorem D on corners;
- `leavitt-algebra-has-no-unital-rank-model`.

**(b) Check (i) relaxes to a rank budget.** Suppose `D != 0`. It is enough to find `x in M` with
`rk(x) > 0`, `S_0, S_1 in xM` and `T_0, T_1 in M` such that

```text
sum over i, j of rk(delta_ij x - T_i S_j)  <  rk(x) .
```

The relations need not be exact: the four defects may be anything whose total rank is below
`rk(x)`.

**(c) Check (iii) is automatic for the right support.** Take `x = D`, or its left projection `e`
(`eM = DM`, `rk(e) = rk(D)`). Then `rk(x) > 0` whenever `D != 0`, with nothing to prove. With this
choice, all of Plan 1 comes down to one task: produce `S_j in DM` and `T_i in M` whose total
two-pair defect rank is below `rk(D)`. This is landed as the open claim
`two-root-defect-gives-small-defect-corner-cohn-family`, with the route
`leavitt-el3-triviality-via-cohn-rank-inequality`. By Theorem 1 the conclusion of that claim can
never hold, so the claim is equivalent to the identities for the models in scope. Its content is the
construction, exactly as for the exact Plan 1 node.

**(d) What check (ii) can still mean.** In a rank ultraproduct no family satisfying (i) with
`rk(e) > 0` exists. So completeness can be neither verified nor refuted for such a family: any
construction is a proof by contradiction, and completeness never enters it. The largest subcorner on
which completeness holds is the zero corner. Completeness keeps a meaning only in test rings with no
faithful rank function, such as `End_F(V)` for an infinite-dimensional `V`, or group algebras.
Sections 2 and 3 treat those.

**(e) Where the Leavitt input still enters.** The final contradiction uses the Cohn relations
`t_i s_j = delta_ij` through both pairs, and nothing else. This is consistent with
`fd-represented-coefficients-violate-two-root-identities`, since the subring generated by both pairs
has no unital rank model (Theorem 1 with `x = 1`). The one-pair Toeplitz subring does have one, so
both pairs are needed. Whether the construction of the relaxed data has to use completeness is the
open calibration in Section 4.

**(f) A scope note on the existing route.** The route
`leavitt-el3-triviality-via-rank-four-cuntz-family` says a model `sigma` of `EL_3(R)` "is" a model
of `R^x = EL_4(R)`. The abstract isomorphism `EL_4(R) ~= R^x ~= EL_3(R)` does not map the block
`EL_3(R) <= EL_4(R)` onto itself, so the block restriction of `sigma o phi` is a different `EL_3`
model. The route's conclusion survives:
1. Apply the argument to the `R^x` model `tau = sigma o phi`, for an isomorphism
   `phi : EL_4(R) -> EL_3(R)`. Both branches make `tau` trivial on the block.
2. The normal closure of the block in `EL_4(R)` is all of `EL_4(R)`. For example
   `x_14(r) = [x_12(r), x_24(1)]`, `x_24(r) = [x_21(r), x_14(1)]` and `x_34(r) = [x_31(r), x_14(1)]`,
   and each commutator of a block element with an arbitrary element lies in the normal closure.
3. So `tau` is trivial, and therefore `sigma = tau o phi^(-1)` is trivial.

The defect `D` that Plan 1 has to handle is the block defect of `tau`, not that of `sigma`.
