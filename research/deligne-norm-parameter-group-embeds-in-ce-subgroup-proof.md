---
rg: 2
id: deligne-norm-parameter-group-embeds-in-ce-subgroup-proof
kind: route
title: Camouflage norm models by regular representations of congruence quotients, and cut a hyperlinear lattice by spectral projections of its central unitary
target: deligne-norm-parameter-group-embeds-in-ce-subgroup
requires:
  - deligne-sep7-norm-parameter-closed-subgroup
  - maslov-ce-parameter-set-is-a-closed-subgroup
  - maslov-ce-subgroup-classifies-finite-deligne-covers
---

Notation of the target. `Gamma = Sp_4(Z)` is residually finite. Fix finite-index normal subgroups
`N_1 >= N_2 >= ...` of `Gamma` with `cap_j N_j = {e}`, and put `F_j = Gamma / N_j`, with left regular representation
`lambda_j`. Write `tr` for normalized traces and `||x||_2 = tr(x* x)^(1/2)`. For `x in Gamma~ = Gamma x_b Z`, put
`s(g) = (g,0)`. Then

```text
s(g) s(h) = z^(b(g,h)) s(gh),       z central,   s(e) = 1   (b normalized).                  (S)
```

**Microstate form of `E_CE`.** Following `maslov-ce-parameter-set-is-a-closed-subgroup` (MCS2), `theta in E_CE` iff
the following holds. For every finite `S` in `Gamma` and every `delta > 0` there are `D` and unitaries
`X(g) in U(D)`, `g in S S`, such that for all `g, h in S`:
- `||X(g)X(h) - c_theta(g,h) X(gh)||_2 < delta`;
- `|tr X(g) - [g = e]| < delta`.

This is the standard equivalence between Connes embeddability of a finitely generated twisted group von Neumann
algebra `L_c(Gamma)`, with its canonical trace, and canonical-trace projective microstates.

## Step 1. Regular camouflage (NCE1)

Let `theta in P_op`. So there are `U_n : Gamma -> U(d_n)`, with `U_n(e) = I` and
`||U_n(g)U_n(h) - c_theta(g,h)U_n(gh)||_op -> 0` for each fixed pair. Choose `j_n -> infinity` and put

```text
X_n(g) = U_n(g) (x) lambda_(j_n)(g N_(j_n))      in  U(d_n |F_(j_n)|).
```

Since `lambda_j` is an honest representation,
`X_n(g)X_n(h) - c_theta(g,h) X_n(gh) = (U_n(g)U_n(h) - c_theta(g,h) U_n(gh)) (x) lambda_(j_n)(gh N_(j_n))`. Its
operator norm equals the defect of `U_n`, and it dominates the normalized HS norm, so it tends to `0`.

Next, `tr X_n(g) = tr U_n(g) * [g in N_(j_n)]`. For `g != e` we have `g notin N_(j_n)` for all large `n`, because the
`N_j` decrease to `{e}`. So `tr X_n(g) = 0` eventually, and `X_n(e) = I`. These are canonical-trace
`c_theta`-microstates, so `theta in E_CE`. Hence `P_op <= E_CE`. `[]`

## Step 2. From `E_CE = R/Z` to hyperlinearity (NCE2, "if")

This is (FIC2) of `sp4-finite-index-scalar-data-iff-hyperlinear-covers`. A direct proof follows.

Pick an irrational `theta in E_CE`. Canonical microstates along a free ultrafilter give a map
`V : Gamma -> U(M^w)` into a matricial tracial ultraproduct, with:
- `V(g)V(h) = c_theta(g,h) V(gh)` exactly;
- `tau(V(g)) = [g = e]`.

Put `W(g,j) = exp(2 pi i theta j) V(g)`. Then

```text
W(g,j) W(h,l) = e(theta(j+l)) c_theta(g,h) V(gh) = e(theta(j + l + b(g,h))) V(gh) = W((g,j)(h,l)),
```

so `W` is a homomorphism `Gamma~ -> U(M^w)`.

It is injective. If `W(g,j) = 1`, then `tau(V(g)) = e(-theta j)` is nonzero, so `g = e`. Then `e(theta j) = 1` with
`theta` irrational, so `j = 0`. Hence `Gamma~` is hyperlinear. `[]`

## Step 3. From hyperlinearity to `E_CE = R/Z` (NCE2, "only if")

Let `pi : Gamma~ -> U(M)` be injective, with `M = M^w = prod_w (M_(k_n), tr)`. Let `N = pi(Gamma~)''` and
`u = pi(z)`. Then `u` is central in `N`. Let `mu` be the spectral measure of `u` with respect to `tau`, and `E_u` its
spectral projection-valued measure.

**3a. The support is large.** Suppose `supp mu` were contained in the `K`-th roots of unity for some `K >= 1`. Then
`u^K = int lambda^K dE_u(lambda) = 1`, so `z^K in ker pi`, which contradicts injectivity. So the closed set
`supp mu` is not contained in any finite subgroup of `T`. Hence
`A = { theta in R/Z : e(theta) in supp mu }` is not contained in any finite subgroup of `R/Z`.

**3b. Every support point is CE.** Fix `theta in A` and `eps > 0`. Let `p = E_u({e(t) : |t - theta| < eps})`.
- `p != 0`, because `e(theta) in supp mu`.
- `p` lies in the center of `N`, since it is a Borel function of the central element `u`.
- `||u p - e(theta) p||_op <= 2 pi eps`.

Put `V(g) = pi(s(g)) p`, a unitary of the corner `pMp`. By (S), `V(g)V(h) = (u p)^(b(g,h)) V(gh)`, and
`||(up)^m - e(theta m) p||_op <= 2 pi |m| eps`. Hence

```text
||V(g)V(h) - c_theta(g,h) V(gh)||_op <= 2 pi |b(g,h)| eps.                                     (C1)
```

Also `V(e) = p`, the unit of `pMp`.

The corner is again a matricial ultraproduct. Lift `p` to projections `p_n in M_(k_n)` with `tr p_n -> tau(p)`,
and put `r_n = rank p_n`. Then `pMp = prod_w (M_(r_n), tr)`, with the renormalized trace `tau_p = tau / tau(p)`.

Now camouflage as in Step 1. Put `Y_j(g) = V(g) (x) lambda_j(g N_j)` in `pMp (x) M_(|F_j|)`, which is again a
matricial ultraproduct. Then:
- its defect satisfies (C1);
- `(tau_p (x) tr)(Y_j(g)) = tau_p(V(g)) [g in N_j]`.

Fix a finite `S` and `delta > 0`. Choose `eps` with `2 pi eps max_(S x S) |b| < delta / 2`, and choose `j` with
`S cap N_j subset {e}`. Lift the finitely many unitaries `Y_j(g)`, `g in S S`, to unitaries at a matrix level along
`w`. At that level:
- the pair defects are `< delta` in `||.||_2`;
- the traces are within `delta` of `[g = e]`.

So `theta in E_CE`. `[]`

**3c. Closing up.** `A <= E_CE`, and `A` is not contained in any finite subgroup. By
`maslov-ce-parameter-set-is-a-closed-subgroup` (MCS1), `E_CE` is a finite cyclic group or `R/Z`. So `E_CE = R/Z`.
`[]`

*Remark.* In the tracial setting the arc projection `p` exists by Borel functional calculus. In the operator-norm
corona the corresponding cut is exactly the corner-extraction hypothesis `(CPE*)` of
`deligne-lattice-non-mf-forces-finite-parameter-group`. Step 3 is the tracial analogue of item 5 there, and it is
unconditional for that reason.

## Step 4. (NCE3) and corollaries

**The equivalences.**
- Step 2 and Step 3 give: `Gamma~` is not hyperlinear iff `E_CE != R/Z`, iff `E_CE` is finite (MCS1).
- If `E_CE` is finite of order `m'`, pick a prime `q` not dividing `m'`. Then `1/q notin E_CE`, so `E_q` is not
  hyperlinear, by (FDC1) of `maslov-ce-subgroup-classifies-finite-deligne-covers`.
- Conversely, if some `E_q` is not hyperlinear, then `1/q notin E_CE` by (FDC1), so `E_CE != R/Z`.

**Finiteness of `P_op`.** By Step 1, `P_op <= E_CE`. A closed subgroup of a finite cyclic group is finite, and its
order divides the order of the group. `[]`

**The corollaries (NCE4)-(NCE6)** follow by composing with the cited nodes, exactly as stated in the target.
