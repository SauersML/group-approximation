---
rg: 2
id: coset-refinement-forces-rectangular-central-splitting-proof
kind: route
title: Cosets are rectangular, their block sums are shared commutant projections, and central supports pass the used sets to the centre
target: coset-refinement-forces-rectangular-central-splitting
requires: []
---

Notation as in the target.  Fix `q != q'`, write `D = D_(qq')`, `c = c_(qq')`
and `N = N_(qq')`, and work in `M` with its faithful trace.

**(R1) Cosets are rectangular.**

- For `u, v, w in cD`, `u v^(-1) w = c d_1 d_2^(-1) d_3 in cD`.
- If `(x,y), (x',y), (x',y') in cD`, then
  `(x,y') = (x,y)(x',y)^(-1)(x',y') in cD`.
- So any path of length three in the bipartite graph of `cD` closes up, and
  each connected component is a complete bipartite graph `B_i x B'_i`.
- Distinct components have disjoint `B_i` and disjoint `B'_i`.

**(R2) The blocks exhaust the fibre.**  If `s` lies in no `B_i`, then
`p_q^s = p_q^s sum_(s') p_(q')^(s') = 0` by (CS).  So
`sum_i sum_(s in B_i) p_q^s = 1`, and likewise on `q'`.

**(R3) Shared block projections.**  Put `z_i = sum_(s in B_i) p_q^s` and
`z'_i = sum_(s' in B'_i) p_(q')^(s')`.

- For `s in B_i` and `s'` not in `B'_i`, `(s,s')` is not in `cD`, so
  `z_i p_(q')^(s') = 0`.
- By (R2), `z_i = z_i z'_i`.  Symmetrically `z'_i = z'_i z_i`.
- Taking adjoints, `z_i = (z_i z'_i)^* = z'_i z_i = z'_i`.

**(R4) Commutant.**

- `z_i` commutes with every `P_q^a`: both lie in the commutative algebra of
  the PVM `p_q`.
- `z_i = z'_i` commutes with every `P_(q')^(a')` for the same reason.
- So `z_i in N' ∩ M`, and `sum_i z_i = 1`.

**(R5) Accepted rectangles in the commutant.**

- `z_i P_q^a = sum_(s in B_i, beta_q(s) = a) p_q^s`.  If it is nonzero, then
  `a in beta_q(B_i)`.
- Likewise `U_(q')(z_i) ⊆ beta_(q')(B'_i)`.
- Since `B_i x B'_i ⊆ cD`,

  ```text
  U_q(z_i) x U_(q')(z_i) ⊆ (beta_q x beta_(q'))(cD) ⊆ Acc_(qq').
  ```

**(R6) Passing to the centre.**  Let `N` act on `L^2(M)`.

- **Central support.**  For a projection `z in N'`, let `C(z)` be the
  projection onto the closed span of `N' z L^2(M)`.  It is invariant under
  `N'` and its commutant, so `C(z) in N'' ∩ N' = Z(N)`.
- **Used sets are unchanged.**  Let `x in N`.
  - If `xz = 0`, then `x u z = u x z = 0` for all `u in N'`, so `x C(z) = 0`.
  - Conversely, `z <= C(z)`.
  - Hence `U_q(C(z_i)) = U_q(z_i)`, and likewise on `q'`.
- **A partition.**
  - The `C(z_i)` are commuting central projections with `∨_i C(z_i) = 1`.
  - For nonempty `T ⊆ {1, ..., m}`, put
    `f_T = prod_(i in T) C(z_i) prod_(i not in T) (1 - C(z_i))`.
  - These form a partition of unity in `Z(N)`.  The term `f_(emptyset)`
    vanishes, since the `C(z_i)` have supremum `1`.
- **(RCS).**  Pick `i in T`.  Then `f_T <= C(z_i)`, so
  `U_q(f_T) ⊆ U_q(z_i)` and `U_(q')(f_T) ⊆ U_(q')(z_i)`.  By (R5) this is
  (RCS).

**Corollary 1 (factor pairs).**  `Z(N) = C`, so the only piece is `1`.

**Corollary 2 (three-colourings).**

- On a piece `f`, `U_x(f)` and `U_y(f)` are nonempty, because `sum_i P_x^i f = f`.
- They are disjoint, because `(i,i)` is rejected.
- So one of them, say `U_y(f)`, is `{j}`.  Then `P_y^j f = f` and
  `P_y^(j') f = 0` for `j' != j`.
- Hence `[P_x^i, P_y^(j')] f = 0` for all colours, and summing over pieces
  gives commutation.

**Corollary 3 (label-matching presentations).**  Suppose
`Acc = ⊔_k L_k x L'_k` for a labelling of answers.

- Put `f_k = sum_(a in L_k) P_q^a`.  A perfect model gives
  `f_k = sum_(a' in L'_k) P_(q')^(a')`, by the argument of (R3).
- So `f_k` is central in `N`, and `U_q(f_k) x U_(q')(f_k) ⊆ L_k x L'_k`.

**Corollary 4 (without padding).**

- **(<=)** Set `c_(qq') D_(qq') = s_0 <S^(-1)S>`.  This is a coset
  containing `S = S_(qq')`, and transposing gives the data for `(q',q)`.
  - In the GNS algebra of `tau`, `P_q^a P_(q')^(a') = 0` off `S`, by
    `tau(pr) = ||pr||_2^2`.
  - So the relations (CS) hold there, and `tau` factors through `A(R)`.
- **(=>)** Suppose `tau` factors through a refinement with coset `cD ⊆ Acc`.
  - Then `S ⊆ cD`, so `cD = s_0 D`.
  - Also `S^(-1) S ⊆ D^(-1) c^(-1) c D = D`.
  - So `s_0 <S^(-1)S> ⊆ cD ⊆ Acc`.
- **The hull contains the rectangular closure.**  Apply the first line of
  (R1) to `S ⊆ s_0 <S^(-1)S>`.

**Model test (the `M_3` example).**

- **The model is a valid perfect model.**  `f_1, f_2, f_3` are orthonormal,
  and `f_1 ⊥ e_1`, so `P_q^1 P_(q')^1 = 0`, which is the only rejected pair.
- **The pair algebra is all of `M_3`.**  Compress `f_1 f_1^*` by the diagonal
  projections to get the matrix unit `E_(23)`.  Compress `f_2 f_2^*`, whose
  `(1,2)` entry is `1/(2 sqrt2)`, to get `E_(12)`.  Together with the
  diagonal these generate `M_3`.
- **Every answer is used.**  All `e_i` and `f_j` are nonzero.
- **Conclusion.**  By Corollary 1 the rectangle `{1,2,3}^2` would have to be
  accepted, but it contains `(1,1)`.
