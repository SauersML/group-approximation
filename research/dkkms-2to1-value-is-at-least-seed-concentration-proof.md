---
rg: 2
id: dkkms-2to1-value-is-at-least-seed-concentration-proof
kind: route
title: Label each class block by block from its identified seed, putting 0 on the one variable a smoothed block exposes and completing each equation locally, check agreement block by block, and identify the seed by counting blocks whose image is at most a line, with Hoeffding on the per-block score gap 1/2 - 2^(1-l)
target: dkkms-2to1-value-is-at-least-seed-concentration
requires:
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
artifacts:
  - experiments/dkkms-heavy-smoothing-local-labelling-2026-09-19/check_local_labelling.py
---

The notation is that of the target. `pi : X_U -> Y` is the quotient map, and
`e_v` is the unit vector of variable `v`. In block `i`, the three variables map
to the three nonzero vectors `ebar_v` of `Y_i`, and every nonzero vector of
`Y_i` is `ebar_v` for exactly one `v`.

## Step 0: premise

**(I)** The DKKMS instance as quoted verbatim (TR16-198 §4.2) in
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`. That includes:

- tuples of pairwise variable-disjoint equations, `X_U`, `H_U` and `h_U`;
- the vertex sets `A` and `B`;
- the edge process: `U` uniform, then `V`, then `L'` uniform in
  `Gr(X_V, l-1)` and `L` uniform among the `l`-spaces of `X_U` containing
  `L'`, restricted to `(U,L) in A` and renormalized;
- folding by `L + H_U = R + H_U`, unfolding by the `(H_U, h_U)`-extension,
  and aggregated folded constraints.

The lift `Lift(G)` is used only through its definition, given in
`dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games` (its edge
constraint reads the unfolding on `L'` and at `y_e = can(S_C, L' + H_U)`).
None of that node's theorems is used.

Since each `L'` lies in the same number of `l`-spaces of `X_U`, the pair
`(L', L)` is uniform among pairs with `L' <= L`, given `V`.

## Step 1: which folding classes hold one tuple

Let `I` be triple-simple and let `(U,L) in A`, with `S = L + H_U`. Suppose the
paper's class of `(U,L)` also holds `(U',L_2)` with `U'` not a reordering of
`U`.

- Then `L_2 + H_(U') = S`, so `H_(U') <= S`, and the variables of `U'` are the
  support of `S`, which is the variable set of `U`.
- `H_(U') != H_U`. Equal spans of disjoint weight-3 vectors have the same
  triples, and on a triple-simple instance the same triples give the same
  equations.
- So some equation vector `x_(e')` of `U'` lies in `S` but not in `H_U`. Its
  image `pi(x_(e'))` is a nonzero vector of `Lbar = S/H_U`, supported on at most
  3 blocks.

Call `(U,L)` **sparse** if `Lbar` contains a nonzero vector with at most 3
nonzero blocks. Off sparse edges, the class of `(U,L)` is exactly
`{(U^perm, L_2) : L_2 + H_U = S}`. All its members have the same `X_U`, `H_U`
and `h_U`. This is the tuple class `(U, S)` of the target. Step 7 bounds the
sparse mass by `mu_sp`.

## Step 2: the labelling

Fix a non-sparse tuple class `(U, S)` and any hyperplane `P` of `Lbar` (Step 5
takes `P = Q*`, the MAP seed, or `P = P*`, the rule of Lemma ID). The block
rule, given an equation `e` on the triple `{v_1 < v_2 < v_3}` with right-hand
side `b` and a subspace `J <= Y_i`, is:

- `rule(J, e) = ` the assignment of the triple with `x(v) = 0` and with the
  least variable other than `v` set to `b`, and the third to `0`, if
  `J = <ebar_v>` is a line;
- `rule(J, e) = ` the assignment with `x(v_1) = b` and `x(v_2) = x(v_3) = 0`
  otherwise.

Both satisfy `e`.

- **A.** `x^P := sum_i rule(pi_i(P), e_i)`. This is a functional on `X_U` with
  `x^P restricted to H_U = h_U`. The class label is `sigma_C := x^P`
  restricted to `R_C`. On a sparse class, `sigma_C` is arbitrary.
- **B at `(V, L')`.** `y` is the functional on `X_V` given as follows. On a
  kept block `i`, `y_i = rule(Q_i^B, e_i)`, where `Q_i^B` is the block-`i`
  image in `Y_i` of the block-`i` components of `L'`. On a smoothed block with
  variable `v`, `y(v) = 0`. The B-label is `y` restricted to `L'`.

B reads only `V` (its kept equations with their right-hand sides) and `L'`.
Neither side reads any other equation of `I`, or any assignment.

For the lift, the A-label is `f := x^P + x^P(y_P) phi_P` restricted to `R_C`,
where `Phat` is the preimage of `P` in `S`, `y_P = can(S, Phat)` and `phi_P` is
the functional on `S` with kernel `Phat`. The B-label is `(y restricted to
L', 0)`.

## Step 3: block images of the seed

Let `Q = (L' + H_U)/H_U`. Its block-`i` image `pi_i(Q)` is the image in `Y_i`
of the block-`i` components of `L'`, because `H_U` is the kernel of `pi`
and `pi` acts block by block. So on a kept block, `pi_i(Q) = Q_i^B`.

On a smoothed block with variable `v`, `X_V` meets block `i` in `<e_v>`. So
`pi_i(Q) <= <ebar_v>`, and `pi_i(Q) = 0` exactly when every `z in L'` has
`z_i = 0`.

## Step 4: agreement when `P` is the seed

**Claim.** If `P = Q`, then `x^P(z) = y(z)` for every `z in L'`.

Write `z = sum_i z_i` by blocks. Both functionals split as sums over blocks,
so it is enough to show `x^P_i(z_i) = y_i(z_i)` for each block.

- **Kept block.** `x^P_i = rule(pi_i(Q), e_i) = rule(Q_i^B, e_i) = y_i` by
  Step 3.
- **Smoothed block, `pi_i(Q) = <ebar_v>`.** `z_i in <e_v>`, and both
  `x^P(v) = 0` and `y(v) = 0`.
- **Smoothed block, `pi_i(Q) = 0`.** `z_i = 0` by Step 3.

## Step 5: value of `G_multi` and `G_folded`

Take a non-sparse class `C = (U, S)` and put `P = P(C)`, a function of the
class only.

- **Unfolding.** `S = R_C ⊕ H_U`, and `x^P` agrees with `h_U` on `H_U`. So the
  `(H_U, h_U)`-extension of `sigma_C = x^P restricted to R_C` is `x^P` on `S`.
  The unfolding at every member `(U^perm, L)` is `x^P restricted to L`.
- **Multi-edges.** A multi-edge `((U,L),(V,L'))` is satisfied iff
  `x^P restricted to L' = y restricted to L'`. By Step 4 this holds whenever
  `P(C) = Q`.
- **Folded constraints.** All members of `C` adjacent to `(V, L')` share `U`
  up to order, so they share the seed `Q = (L' + H_U)/H_U`. When `P(C) = Q`,
  every member constraint of the aggregate holds, so the aggregated constraint
  holds. Its weight is the sum of the member weights.

Hence both values are at least `Pr_edge[not sparse, P(C) = Q]`. That is at
least `Pr[P(C) = Q] - mu_sp`.

- With `P = Q*(C)`, a maximiser of `w(. | C)`, we get
  `Pr[Q*(C) = Q] = E_C w(Q*(C) | C) = E_C max_Q w(Q | C) = 1 - xi`.
- With `P = P*`, we get `1 - Pr[P* != Q]`.

The law of the edge given `U` does not read `I`, and every tuple has the same
block structure. So `xi` and `Pr[P* != Q]` are functions of `(l, k, beta)`
only.

## Step 6: the lift

The functional `phi_P` vanishes on `Phat`, which contains `H_U`. So
`f = x^P + x^P(y_P) phi_P` still agrees with `h_U` on `H_U`, and the unfolding
of `f restricted to R_C` at every member is `f` on `S`.

Take an edge with `P = Q`. Then `L' + H_U = Phat`, so `y_e = can(S, Phat) = y_P`.

- On `L' <= Phat` we have `phi_P = 0`, so `f restricted to L' = x^P
  restricted to L' = y restricted to L'` by Step 4.
- `f(y_e) = x^P(y_P) + x^P(y_P) phi_P(y_P) = 0`, which is the B bit.

So the lift value is at least the same bound as in Step 5.

## Step 7: the column model, and the sparse mass

Fix `U`, and let `V` be drawn as in the paper, with `s` smoothed blocks and
`N' = dim X_V = 3k - 2s >= k`.

**The model.** Draw `t_1, ..., t_(l-1)` i.i.d. uniform in `X_V`, and `t_l`
uniform in `X_U`. Put `tbar_j = pi(t_j)`. Let `E` be the event that
`tbar_1, ..., tbar_l` are independent. On `E`, put
`L' = span(t_1..t_(l-1))` and `L = L' + <t_l>`.

**`E` is validity.** `E` holds iff `pi` is injective on `L`, that is, iff
`dim L = l` and `L meet H_U = 0`, because `ker pi = H_U`. Each valid pair
`(L', L)` comes from exactly `|GL_(l-1)(F_2)| * 2^(l-1)` column tuples (an
ordered basis of `L'`, then `t_l in L \ L'`).

**Density against the paper's law.** Given `V`, the model gives a valid
`(V, L', L)` weight `Pr[V] |GL_(l-1)| 2^(l-1) / (2^(N'(l-1)) 2^(3k))`. The
paper gives it `Pr[V] / (|Gr(X_V,l-1)| [3k-l+1, 1])`. Their ratio is a
constant times

`2^(N'(l-1)) / (|Gr(N', l-1)| |GL_(l-1)|) = prod_(j<l-1) (1 - 2^(j-N'))^(-1)`,

which lies in `[1, (1 - 2^(l-1-k))^(-1)]`. Normalized to probability laws on
valid outputs, the two differ in total variation by at most `a/(1-a)`, where
`a = 2^(l-1-k)`. For `k >= l` this is at most `2^(l-k)`.

**`Pr[not E]`.** Take `c != 0` in `F_2^l`.

- If `c_l = 1`, then `sum_j c_j tbar_j` is uniform in `Y`, since `tbar_l` is
  uniform and independent of the rest. So it is `0` with probability `4^(-k)`.
- Otherwise it is uniform on `W_V = pi(X_V)`, which has dimension
  `2k - s >= k`. So it is `0` with probability at most `2^(-k)`.

A union over the `2^(l-1)` choices of each kind gives
`Pr[not E] <= 2^(l-1)(4^(-k) + 2^(-k)) <= 2^(l-k)`.

**Independence.** Given `V`, the block components of the columns are
independent across blocks.

- In a kept block, the `l` block images are i.i.d. uniform in `Y_i`.
- In a smoothed block with variable `v`, the first `l-1` images are
  `c_j ebar_v`, with `c` uniform in `F_2^(l-1)`. The last image is uniform in
  `Y_i` and independent of `c`.

**The sparse mass.** Let `Sp` be the set of nonzero vectors of `Y` with at most
3 nonzero blocks. Then `|Sp| <= 3k + 9 C(k,2) + 27 C(k,3) <= 5 k^3`.

- A combination with `c_l = 1` is uniform in `Y`, so it lies in `Sp` with
  probability at most `5k^3 4^(-k)`.
- A combination with `c_l = 0` and `c != 0` is uniform on `W_V`, so it lies in
  `Sp` with probability at most `5k^3 2^(-k)`.

So under the model, `Pr[sparse] <= 2^(l-1) * 5k^3 (4^(-k) + 2^(-k)) <= 5 * 2^l k^3 2^(-k)`.
Conditioning on `E` divides by `1 - 2^(l-k) >= 1/2`, and passing to the paper's
law adds `2^(l-k)`. So for `k >= l + 1`,

`Pr_edge[sparse] <= 10 * 2^l k^3 2^(-k) + 2^(l-k) <= mu_sp`.

## Step 8: proof of Lemma ID

Work in the model. Let `M_i : F_2^l -> Y_i` send `c` to the block-`i` image
of `sum_j c_j t_j`. On `E`, the hyperplanes of `Lbar` are the images
`P_psi = Tbar(ker psi)`, one for each nonzero functional `psi` on `F_2^l`.
The seed is `Q = P_(psi_0)`, with `psi_0 = (0,...,0,1)`. Also
`pi_i(P_psi) = M_i(ker psi)`.

Put `Z_i(psi) := 1{dim M_i(ker psi) <= 1}`, so that
`s(P_psi) = sum_i Z_i(psi)`. Fix `psi != psi_0` and put
`D_i := Z_i(psi_0) - Z_i(psi)`, which lies in `[-1, 1]`.

**Kept block.** The columns of `M_i` are i.i.d. uniform, so the law of `M_i`
is invariant under `M_i -> M_i g` for `g in GL_l`. Some `g` maps `ker psi_0` to
`ker psi`. So `Z_i(psi)` and `Z_i(psi_0)` have the same law, and `E D_i = 0`.

**Smoothed block, variable `v`.** `M_i(ker psi_0) = <c_1 ebar_v, ...> <= <ebar_v>`,
so `Z_i(psi_0) = 1`.

For `psi != psi_0`, let `K := ker psi meet ker psi_0`, which has dimension
`l - 2`, and pick `u in ker psi` with `u_l = 1`. Then
`M_i(ker psi) = M_i(K) + <M_i u>`, where `M_i(K)` is `<ebar_v>` if `c` does not
vanish on `K`, and `0` if it does. Also `M_i u = (c . u') ebar_v + m_l`, with
`m_l` uniform in `Y_i` and independent of `c`.

- `c` vanishes on `K`, an event of probability `2^(2-l)` (the annihilator of
  `K` in `F_2^(l-1)` has 2 elements). Then `dim M_i(ker psi) <= 1`.
- Otherwise `M_i(ker psi) <= <ebar_v>` iff `m_l in <ebar_v>`, which has
  probability `1/2`.

So `E Z_i(psi) = 2^(2-l) + (1 - 2^(2-l))/2 = 1/2 + 2^(1-l)`, and
`E D_i = Delta_l = 1/2 - 2^(1-l)`.

**Tail.** Given `V` with `m` smoothed blocks, the `D_i` are independent and
`E sum_i D_i = m Delta_l`. The rule errs against `psi` only if
`sum_i D_i <= 0`. By Hoeffding (range 2 per block), this has probability at
most `exp(-2 (m Delta_l)^2 / (4k)) = exp(-m^2 Delta_l^2 / (2k))`.

- `m` is Binomial`(k, beta)`, so `Pr[m < beta k/2] <= exp(-beta k/8)`.
- On `m >= beta k/2`, the bound is at most `exp(-beta^2 Delta_l^2 k/8)`.

A union over the `2^l - 2` competitors bounds `Pr_model[P* != Q, E]` by the
bracket in `eps_ID`. Dividing by `Pr[E] >= 1 - 2^(l-k)` gives the model law
on valid outputs. Step 7 adds `2^(l-k)` for the paper's law. Finally,
`1 - xi = E_C max_Q w(Q|C) >= E_C w(P*(C)|C) = Pr[P* = Q]`, since `P*` is a
function of the class.

`Delta_3 = 1/4`, and `Delta_l` increases with `l`. At `l = 2`, `Delta_2 = 0`,
and the rule has no signal.

## Step 9: the corollaries

**Triple-simple regular instances of low value.** Fix `eps in (0, 1/2)`, take
`D = ceil(2/eps^2)` and `N >= max(D, k)`. The variables are
`Z_N x {0,1,2}`, and the triples are

`T_(a,j) = {(a,0), (a+j,1), (a+2j,2)}`, for `a in Z_N` and `0 <= j < D`.

- Each variable lies in exactly `D` triples, since `a -> a + j` and
  `a -> a + 2j` are bijections of `Z_N`.
- Distinct `(a, j)` give distinct triples, since `a` is read off the first
  coordinate and `j` off the second.
- The triples `T_(a,0)` for `a < k` are pairwise disjoint, so legitimate
  k-tuples exist.

Draw the right-hand sides uniformly. For a fixed assignment, the number of
satisfied equations is Binomial`(DN, 1/2)`, so Hoeffding gives probability at
most `exp(-2 eps^2 DN) <= exp(-4N)` of satisfying more than `(1/2 + eps) DN`.
There are `2^(3N) < e^(4N)` assignments, so some choice of right-hand sides has
value `<= 1/2 + eps`.

**R.** The hole says: for every `delta > 0` there are `l, beta, s, k_1` with the
soundness property. Take `delta = 1/2` (any `delta < 1` works), and let
`(l, beta, s, k_1)` be arbitrary with `l >= 3`.

- By Steps 7 and 8, `eps_ID + 2^(l-k) + mu_sp -> 0` as `k -> infinity`. Pick
  `k >= max(k_1, l + 1)` with this sum `< 1/2`.
- Let `I` be the instance above with `eps = s - 1/2`. It is regular and has
  value `<= s`.
- By Steps 5 and 8, `val(G(I; l,k,beta)) > 1/2`.

So no choice of parameters works, and the hole is false.

**SC.** Suppose `val <= delta` on a triple-simple `I`. Then
`1 - xi - mu_sp <= delta`, so `E_C max_Q w = 1 - xi <= delta + mu_sp`.
Suppose also that `beta` exceeds both terms of the stated maximum. Then

- `(2^l - 2) exp(-beta^2 Delta_l^2 k/8) < (1 - delta)/8`;
- `exp(-beta k/8) < (1 - delta)/8`;
- so `eps_ID < (3/2)(1 - delta)/4 = 3(1 - delta)/8`, using
  `1 - 2^(l-k) >= 2/3`.

Adding `2^(l-k) + mu_sp <= (1 - delta)/4` gives
`xi + mu_sp < 5(1-delta)/8 < 1 - delta`. That contradicts
`1 - xi - mu_sp <= delta`.

The published smallness `beta sqrt(k) 2^l << 1` means
`beta << 2^(-l) k^(-1/2)`, which is below the ceiling.

**FB.** Since `val_YES <= 1` and, by Step 6, `val_NO >= 1 - xi - mu_sp`,
the difference is at most `xi + mu_sp`.

**The extension in the target.** Take any orientation lift whose pinned bit is
the unfolding evaluated at a vector depending only on `(C, Q)`, carried by B.
Step 6 works for it with `y_P` replaced by that vector, taken outside `Phat`.

## Step 10: checks

The artifact implements Steps 2 to 4 and the rule `P*` on the column model.
It samples the right-hand sides uniformly, and prints ALL PASS.

- On every sample, A's assignment satisfies every equation of its tuple.
- Whenever `P* = Q`, the constraint holds on a basis of `L'`. There are 0
  failures in 3,040 samples, with `k` up to 3000.
- The identification rates and the Hoeffding comparison are those quoted in
  the target.
