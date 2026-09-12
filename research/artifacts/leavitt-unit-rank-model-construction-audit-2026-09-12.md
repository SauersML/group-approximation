# Rank models of the Leavitt unit group: the algebra route is dead, the units route is open

Lane `gk-l-gate-pos`, 2026-09-12. Supports the claims
`leavitt-algebra-has-no-unital-rank-model` (Section 1),
`block-unipotent-rank-models-of-leavitt-el3-are-trivial` (Section 5) and
`monomial-rank-models-are-hamming-models` (Section 6), and the construction records
on `binary-leavitt-unit-group-is-f2-linear-sofic` and
`projective-ternary-group-is-f3-linear-sofic` (Section 7).

Throughout `R = L_(F_2)(1,2) = F_2<s_0,s_1,t_0,t_1 | t_i s_j = delta_ij, s_0t_0+s_1t_1=1>`,
and `H = R^x` its unit group, `H = EL_n(R) = GL_n(R)` for every `n >= 2`
(Khanh--Thanh). A **rank ultraproduct** over a field `F` is
`M = prod_omega M_(n_k)(F) / d_omega`, with `d_omega` the ideal of
normalized-rank-null sequences. `M` is unit-regular, hence directly finite:
`rk(1 - ab) = rk(1 - ba)` for all `a,b` (Arzhantseva--Paunescu,
arXiv:1212.6780, Proposition 2.8; the map `v -> bv` carries `ker(1-ab)`
bijectively onto `ker(1-ba)` because `v = abv` on that kernel).

## 1. No unital rank model of the algebra `R`

**Proposition.** There is no unital `F`-algebra homomorphism `phi : R -> M`
into any rank ultraproduct `M` over any field `F`.

*Proof.* `R` is simple (the Leavitt algebra of the rose with two petals is a
simple ring; Leavitt 1962, or the Leavitt path algebra of a graph with one
vertex and two loops). A unital homomorphism is nonzero, so its kernel is a
proper two-sided ideal, hence `0`, so `phi` is injective. Now
`phi(t_0) phi(s_0) = phi(t_0 s_0) = phi(1) = 1_M`. `M` is directly finite, so
`phi(s_0) phi(t_0) = 1_M = phi(1)`, i.e. `phi(s_0 t_0 - 1) = 0`. But
`s_0 t_0 - 1 != 0` in `R`, contradicting injectivity. QED

The same argument kills any field: direct finiteness of `M` is characteristic
free. It also kills any unital rank-approximate homomorphism
`phi_k : R -> M_(m_k)(F)` (additive, `rk(phi_k(ab) - phi_k(a)phi_k(b)) -> 0`,
`rk(phi_k(1) - 1) -> 0`, `rk(phi_k(a)) not-> 0` for `a != 0`): assembling the
`phi_k` gives exactly a unital injective `phi : R -> M`, which cannot exist.

This is the rank-metric shadow of `binary-leavitt-algebra-not-directly-finite`:
`R` is not directly finite, and rank ultraproducts are, so `R` cannot sit
unitally inside one. Contrast `linear-sofic-group-algebra-is-stably-finite`,
which embeds the *group algebra* `F[G]` of a linear sofic group; that needs the
group elements to go to invertibles, which the isometries `s_i` are not.

## 2. What this forbids, and what it does not

**Forbidden: the algebra route to a model of `H`.** The natural way to build a
rank model of `H = EL_n(R)` is to first model the coefficient algebra and then
take elementary matrices:

```text
e_ij(a) = 1 + a E_ij   |-->   1 + phi(a) E_ij .
```

The Steinberg relation `[e_12(a), e_23(b)] = e_13(ab)` forces
`phi(ab) = phi(a) phi(b)`, and `e_ij(a) e_ij(b) = e_ij(a+b)` forces additivity,
so `phi` must be an (approximate) unital algebra homomorphism `R -> M`. Section 1
rules that out. So **no rank model of `H` extends to a rank-approximate
homomorphism of the ambient algebra `R`.** Any model must be genuinely
non-multiplicative on `R`.

**Not forbidden: a model of the units.** The obstruction is about `s_i`, which
are one-sided invertible non-units. In `EL_n(R)` they never appear inverted:
`e_ij(a)^{-1} = e_ij(-a)`, so `s_i` sits only as an off-diagonal entry of a
matrix whose inverse re-uses `s_i`, never `s_i^{-1}`. Direct finiteness of `M`
therefore places no constraint of the Section 1 kind on a group homomorphism
`sigma : EL_n(R) -> M^x`. This is the gap that keeps
`binary-leavitt-unit-group-is-f2-linear-sofic` open: the algebra is provably
un-modellable in rank, while the unit group might still be modellable, because
a group model may read the letters `s_i, t_i` only through the invertible
elementary matrices they build.

## 3. Constructions tried, and where each dies

Every construction below aims at `sigma : H -> M^x` and fails against a recorded
constraint.

1. **Graded path-space truncation.** `R` acts on `F_2[{0,1}^*]` by
   `s_i : e_w -> e_iw`, `t_i : e_iw -> e_w` (`e_jw -> 0`, `j != i`),
   `t_i e_empty = 0`. Truncating to strings of length `<= N` forces a choice at
   level `N` (send `s_i` of a leaf to `0`, or wrap). The tree `{0,1}^(<=N)` has
   `2^N` leaves and `2^N - 1` internal nodes, so the error is supported on a
   `1/2` fraction and the normalized-rank defect is bounded below by a constant.
   This is the exponential-growth (paradoxicality) obstruction, and it is the
   precise mechanism behind "the natural Cantor truncation is dead" recorded on
   `binary-leavitt-unit-group-is-f2-linear-sofic`. It is fatal to any model that
   represents the algebra, consistent with Section 1.

2. **Model the algebra, then take elementary matrices.** Dead by Section 2:
   there is no approximate unital algebra homomorphism to assemble.

3. **Genuine finite-dimensional representation of `H`.** Dead: `H` is finitely
   generated, infinite and simple, so every genuine finite-dimensional
   representation is trivial (recorded on the target). Models must be genuinely
   almost multiplicative.

4. **A model where the nine-leaf Kazhdan `Gamma` fixes a linear-size piece.**
   Excluded in every tensor degree by
   `leavitt-rank-models-kazhdan-fixed-ideals-are-global`.

## 4. Where a positive construction must now live

A model of `H` must (i) be genuinely non-multiplicative on `R` (Section 2),
(ii) not factor through a finite group (Section 3.3), (iii) respect the global
fixed-ideal constraint of Section 3.4, and (iv) place its multiplicative defect
below linear rank scale, since the linear-scale layer is conserved for free
(`rank-ultraproduct-compressors-conserve-fixed-right-ideals`). The question first
recorded here was whether the Leavitt multiplication `(a,b) -> ab` can be
carried on the off-diagonal blocks of elementary matrices with `o(n_k)` rank
defect while never inverting the isometries. Section 5 answers it negatively, at
every choice of block dimensions. Section 6 removes the permutation-type models,
and Section 7 records the class that remains. Property (T) alone does not decide
that class in either direction: it supplies no rank rounding over a finite field
(`kazhdan-group-rank-models-admit-no-expander-decomposition`). The remaining
question is the same heart as the rank row
`f2-linear-sofic-groups-kill-rigid-compression-defects`.

## 5. Block-unipotent models collapse at every block dimension

Claim `block-unipotent-rank-models-of-leavitt-el3-are-trivial`, route
`block-unipotent-rank-models-of-leavitt-el3-proof`.

The question: can a model of `EL_3(R)` carry the Leavitt multiplication on
off-diagonal blocks `V_j -> V_i` of *different* dimensions, as the module
isomorphism `R_R = R_R^2` suggests, with `psi_ij(1)` a rank-deficient
near-isometry instead of the identity? No.

`gk-vf-linear` already remarked, on `leavitt-algebra-has-no-unital-rank-model-proof`,
that elementary-matrix models `1 + phi(a) E_ij` built from one given coefficient
map `phi` on equal blocks are excluded even without `phi(1) = 1`, since corners
of rank ultraproducts are directly finite. This section drops both
presuppositions: the block maps are independent and the block ranks arbitrary.

**Setting.** `K` a field and `R_K = L_K(1,n)` with `n >= 2`, which is simple and
has `t_0 s_0 = 1 != s_0 t_0`. `M` a directly finite ring, for instance a rank
ultraproduct over any field. `e_1, e_2, e_3` pairwise orthogonal idempotents of
`M`, of arbitrary ranks. `sigma : St_3(R_K) -> M^x` a homomorphism with
`sigma(x_ij(a)) = 1 + psi_ij(a)` and `psi_ij(a) in e_i M e_j`. Approximate block
support at finite stages becomes exact in the ultraproduct.

**Theorem.** `psi_ij(a) = 0` for all `i != j` and all `a`, so `sigma` is trivial.

*Step 0, block calculus.* For `X in e_i M e_j` and `Y in e_j M e_k`, with
`i, j, k` distinct, `X^2 = Y^2 = YX = 0`. So `(1 + X)^(-1) = 1 - X`, and

```text
[1 + X, 1 + Y] = (1 + X)(1 + Y)(1 - X)(1 - Y) = 1 + XY,
```

since every other monomial of the expansion contains `YX`, `X^2` or `Y^2`. Hence
`x_ij(a) x_ij(b) = x_ij(a + b)` and `[x_ij(a), x_jk(b)] = x_ik(ab)` give

```text
(A)  psi_ij(a + b) = psi_ij(a) + psi_ij(b),
(B)  psi_ij(a) psi_jk(b) = psi_ik(ab)            (i, j, k distinct).
```

The relations `[x_ij(a), x_kl(b)] = 1` with `j != k` and `i != l` hold
automatically.

*Step 1, matrix units.* Put `u_ij = psi_ij(1)`, so `u_ij u_jk = u_ik`. Let
`p_i = u_ij u_ji`. With `{i, j, k} = {1, 2, 3}`, `u_ji = u_jk u_ki` gives
`u_ij u_ji = u_ik u_ki`, so `p_i` does not depend on `j`. Then

```text
p_i u_ij = u_ik u_ki u_ij = u_ik u_kj = u_ij,      u_ij p_j = u_ij u_jk u_kj = u_ik u_kj = u_ij,
```

so `p_i^2 = u_ij (u_ji u_ij) u_ji = u_ij p_j u_ji = p_i`. The maps `u_ij` and `u_ji`
are mutually inverse between the corners: `u_ij u_ji = p_i` and `u_ji u_ij = p_j`.
In a rank ultraproduct, `rk(p_1) = rk(p_2) = rk(p_3)`.

*Step 2, support.* By (B), `psi_ij(a) = psi_ik(a) u_kj = psi_ij(a) p_j` and
`psi_ij(a) = u_ik psi_kj(a) = p_i psi_ij(a)`. So every `psi_ij(a)` lies in
`p_i M p_j`.

*Step 3, the corner homomorphism.* Put `phi(a) = psi_12(a) u_21`, which equals
`psi_13(a) u_32 u_21 = psi_13(a) u_31`. It is additive by (A), `phi(1) = p_1`,
`phi(a)` lies in `p_1 M p_1` by Steps 1 and 2, and

```text
phi(a) phi(b) = psi_12(a) u_21 psi_13(b) u_31 = psi_12(a) psi_23(b) u_31 = psi_13(ab) u_31 = phi(ab).
```

Moreover `psi_ij(a) = u_i1 phi(a) u_1j`, with `u_11 = p_1`, so `phi` determines
`sigma`.

*Step 4, direct finiteness.* A corner of a directly finite ring is directly
finite: if `ab = p` in `pMp`, then `(a + 1 - p)(b + 1 - p) = 1`, so
`(b + 1 - p)(a + 1 - p) = 1` and `ba = p`. From `phi(t_0) phi(s_0) = p_1` we get
`phi(s_0 t_0 - 1) = 0`. If `p_1 != 0`, then `ker phi` is a proper two-sided ideal
of the simple ring `R_K`, so `phi` is injective, contradicting `s_0 t_0 != 1`.
So `p_1 = 0`, hence `phi = 0`, and every `psi_ij = 0`. QED

**Weyl elements and unequal blocks.** With (A), `psi_ji(-1) = -u_ji`, and

```text
sigma(w_ij) = (1 + u_ij)(1 - u_ji)(1 + u_ij) = (1 - p_i - p_j) + u_ij - u_ji,
```

using `u_ij u_ji = p_i`, `u_ji u_ij = p_j` and `u_ij u_ji u_ij = u_ij`. This is the
signed swap of the two corners, and the identity on the rest. The Weyl relations
follow from (A) and (B), so they force nothing beyond Step 1: `rk(p_i) = rk(p_j)`
is forced, `rk(e_i) = rk(e_j)` is not, and `e_i - p_i` carries the trivial
action. An ansatz with unequal blocks is therefore an equal-corner model plus a
trivial summand. Step 4 kills the equal-corner part before the Kazhdan
fixed-ideal conditions come into play; the trivial summand satisfies them
vacuously.

**Scope.** For `R = L_K(1,2)`, `R_R = R_R^2` gives `M_3(R) = R` and
`R^x = GL_3(R)`. Over `F_2`, `GL_3(R) = EL_3(R)`
(`leavitt-gl-equals-el-and-perfect-unit-group`). So every rank model of `R^x`
that is block unipotent for some 3-block decomposition and some identification
`R^x = EL_3(R)` is trivial. That includes every model built from approximate
`R`-modules, the natural action on `V_1 + V_2 + V_3`, at any ranks. For the
ternary unit group, restrict a model to its nontrivial subgroup `EL_3`.

## 6. Monomial models are Hamming models

Claim `monomial-rank-models-are-hamming-models`, route
`monomial-rank-models-are-hamming-models-proof`.

**Proposition.** Let `F` be a finite field and `Mon_N(F)` the monomial `N x N`
matrices, acting faithfully on `X_N = F^x x [N]` by
`j(A)(lambda, i) = (c lambda, pi(i))`, where `A e_i = c e_(pi(i))`. For `A, B` in
`Mon_N(F)`,

```text
(1/2) d_H(j(A), j(B))   <=   rk(A - B) / N   <=   d_H(j(A), j(B)),
```

with `d_H` the normalized Hamming distance on `X_N`.

*Proof.* Both distances are left invariant, so take `C = B^(-1) A` and compare it
with `1`. Let `m` count the `i` with `C e_i != e_i`. `j(C)` moves exactly the
points `(lambda, i)` with such `i`, so `d_H(j(C), 1) = m / N`. `C - 1` has at most
`m` nonzero columns, so `rk(C - 1) <= m`. Conversely, split `[N]` into the cycles
of `pi`. After a simultaneous permutation of rows and columns, `C - 1` is block
diagonal along the cycles. A fixed point with label `c != 1` gives the block
`c - 1 != 0`. A cycle `i_1 -> ... -> i_l` with `l >= 2` gives a block whose columns
`c_r e_(i_(r+1)) - e_(i_r)`, `r <= l - 1`, restricted to the rows
`i_1, ..., i_(l-1)`, form a bidiagonal matrix with `-1` on the diagonal. So that
block has rank at least `l - 1 >= l / 2`. Summing, `rk(C - 1) >= m / 2`. QED

**Consequence.** If `sigma_k : G -> GL_(N_k)(F)` take values within `o(N_k)` rank
of monomial matrices, are asymptotically multiplicative in normalized rank, and
keep every nontrivial `g` at rank distance bounded below from `1`, then `j`
applied to the nearby monomial matrices is a sofic approximation of `G`.
Multiplicative defects at most double, and separation does not shrink. So a
nonsofic group has no monomial linear sofic approximation over any finite field.
This removes the permutation-type family for `R^x` (`openai-leavitt-unit-nonsofic`),
for `L_(F_3)(1,2)^x` (`d-ary-leavitt-groups-nonsofic-over-finite-fields`), and for
`PG` (`projective-leavitt-unit-groups-mod-scalars-are-nonsofic`).

## 7. What a surviving model must look like

A rank model of `R^x`, of `L_(F_3)(1,2)^x` or of `PG` over a finite field must:

1. be non-multiplicative on the algebra (Sections 1 and 2);
2. be block unipotent for no 3-block decomposition of any identification with
   `EL_3`, and in particular not be built from approximate modules (Section 5);
3. not lie within `o(n)` rank of monomial matrices (Section 6);
4. not factor through a finite group (Section 3.3);
5. meet the global fixed-ideal condition in every tensor degree (Section 3.4),
   with its multiplicative defect below linear rank scale.

Property (T) supplies no rank rounding to exploit
(`kazhdan-group-rank-models-admit-no-expander-decomposition`). In characteristic
`p`, `(sigma(x_ij(a)) - 1)^p = sigma(x_ij(a))^p - 1` is rank-null, so root
subgroups act approximately unipotently. Condition 2 says that for every
decomposition, either some root subgroup acts non-additively, meaning
`(sigma(x_ij(a)) - 1)(sigma(x_ij(b)) - 1)` is not rank-null for some `a, b`, or the
square-zero parts are not simultaneously supported on orthogonal blocks. No
construction and no obstruction is known for this remaining class.

**Host family.** Sections 1 and 5 hold for every field `K` and every `L_K(1,n)` with
`n >= 2`, and Section 6 holds over every finite field. So they apply to the whole
host family landed by `gk-lp-hosts` (22e71610d0, 4da43c6520), including `F_3` and
`F_4`, because every finite-field Leavitt unit group is nonsofic
(`d-ary-leavitt-groups-nonsofic-over-finite-fields`).

**Degree-truncation building blocks.** The diffuse honest models of `EL_3(F_q[t])`
(`kazhdan-rank-ultraproducts-can-have-diffuse-commutants`) are block unipotent:
`e_ij(a)` acts on `F_(q^k)^3` as `1 + a(alpha) E_ij`. They exist because `F_q[t]`
has honest finite-dimensional modules. Through a polynomial subring
`F_q[t] <= R` they model the subgroup `EL_3(F_q[t]) <= EL_3(R)`. By Section 5, an
extension to `EL_3(R)` cannot stay block unipotent on every root subgroup; it must
break block unipotence on root elements `x_ij(a)` with `a` outside the subring.
Section 5 alone does not exclude a hybrid that is block unipotent on the subring's
root subgroups and arbitrary on the others, because Step 3 needs block support of
`psi_1j(a)` for every `a` in `R`. In characteristic two the hybrid is dead anyway.
`matrix-unit-root-rank-models-of-simple-el3-are-trivial` (gk-l-gate-neg, 384d050274)
needs block support only of the six unit root elements, and the hybrid has it through
Step 1: `sigma(x_ij(1)) = 1 + u_ij` with `u_ij` in `p_i M p_j`.

**Check of the complement case** (gk-l-gate-pos, characteristic two). Put
`V' = (1 - p_1 - p_2 - p_3)V`, on which the `x_ij(1)` act trivially, and
`n = sigma(x_13(a)) - 1`. Commuting with `x_12(1)` and `x_23(1)` leaves
`n = d P + c E_13 + f E_1' + g E_'3 + h E_''`, with `P` the block identity on the three
copies of `W`. Unipotence gives `d^2 = 0`. The relation `[x_13(a), x_32(1)] = x_12(a)`
gives `sigma(x_12(a)) = 1 + c(1 + d) E_12 + g(1 + d) E_'2`. The expansion
`x_13(a) = [x_12(a), x_23(1)]` then forces `d = f = h = 0`. Next,
`[x_21(1), x_13(a)] = x_23(a)` gives `sigma(x_23(a)) = 1 + c E_23`, and the expansion
`x_13(a) = [x_12(1), x_23(a)]` forces `g = 0`. So a complement acted on trivially by
the unit root elements adds no intertwiner terms.

**Surviving shape.** In characteristic two, a nontrivial model must restrict to
`SL_3(F_2) = EL_3(F_2)` as something other than `(natural (x) W) (+) trivial`. That
claim is stated only in characteristic two. The ternary host `L_(F_3)(1,2)^x`, where
`(1 + n)^(-1) = 1 - n + n^2`, is not covered, and the signed propagation is not
recorded here.
