---
rg: 2
id: leavitt-unit-group-has-no-integer-heisenberg-subgroup
kind: claim
title: The binary Leavitt unit group contains no integer Heisenberg group
distinct_from:
  thompson-v-has-no-heisenberg-subgroup: that settles the question inside V_n by undistortion of cyclic subgroups; this asks it for the whole unit group, whose linear units have no undistortion theorem.
  kun-thom-wreath-embeds-in-leavitt-unit-group: that is the embedding claim this question tests; this is the first subgroup obstruction on its path, and its truth would refute that claim for every admissible parameter.
  char-two-curve-linear-groups-satisfy-boone-higman: that embeds characteristic-two linear groups of transcendence degree one in the unit group; this asks about a group that is linear over no field of positive characteristic.
---

**OPEN.** Let `R = L_(F_2)(1,2)` and `Q = R^x`. The claim is that there are no
`a, b` in `Q` such that `c = [a,b]` has infinite order and commutes with `a` and
`b`. By the normal-subgroup argument in `thompson-v-has-no-heisenberg-subgroup`,
this is equivalent to `Q` having no subgroup isomorphic to `H_3(Z)`.

**Payoff.** Every Theorem E actor `G` contains `SL_d(Z)` with `d >= 3`, and hence
`H_3(Z)`. So this claim refutes `kun-thom-wreath-embeds-in-leavitt-unit-group`
for every admissible `(q, r, d)`, together with every alternative listed there,
since each of them contains `G`
(`kun-thom-wreath-nonembedding-from-no-heisenberg`). The Kun--Thom chain could
then reach `Q` only through a group with the same hyperlinearity status that is
not a supergroup of `G`. A negative answer would instead produce
`H_3(Z) <= Q`, the first test named in
`research/artifacts/hyperlinear-nonsofic-l-times-2026-09-12.md`, Section 1.4.

## Attempts

**Thompson elements.** If `a` and `b` lie in one conjugate of the embedded `V`,
then `thompson-v-has-no-heisenberg-subgroup` excludes the configuration. That
theorem rests on undistortion of cyclic subgroups of `V`, and says nothing about
linear units.

**Matrices over commutative subrings.** These are excluded by the
positive-characteristic determinant lemma of
`kun-thom-wreath-embeds-in-leavitt-unit-group`. Passing to the quotients by
prime ideals bounds the order of `c` in terms of the matrix size, and the
nilradical contributes a unipotent factor of `2`-power order.

**A distortion invariant.** This route is partly built, and it dies at a linear
lower bound.
- Put `R_N = span{ s_alpha t_beta : |alpha|, |beta| <= N }`. Since `t_beta s_gamma`
  reduces to `s_gamma'` or to `t_beta'` or to `0`, one has
  `R_N R_M <= R_(N+M)`.
- So `ell(x) = min{ N : x in R_N }` is subadditive, and
  `lambda(u) = lim_m max(ell(u^m), ell(u^-m))/m` exists for every unit `u`.
- `R_N` is a finite set, so a unit whose powers have bounded depth has finite
  order.
- A Heisenberg center satisfies `c^(m^2) = [a^m, b^m]`, hence `lambda(c) = 0`.
- Every monomial of `R_N` has degree `|alpha| - |beta|` in `[-N, N]`. A Thompson
  element with a hyperbolic attractor therefore has `lambda > 0`.
- The route needs `lambda(u) > 0` for every unit of infinite order. No argument
  controls cancellation among the monomials of a general linear unit, so this is
  not proved.
- Numerical screen (`research/artifacts/leavitt-unit-depth-growth-experiment-2026-09-12.md`).
  About 550 short random words in four Thompson generators and three transvections
  were checked in exact normal form. Every unit without a detected finite order had
  linearly growing depth, with rational late slopes between `1/4` and `4`, or had
  bounded depth and order `31`. No sublinear growth was seen. This is evidence only.

**Thompson centers are excluded (established).**
`leavitt-north-south-thompson-unit-has-cyclic-centralizer` proves that the north--south
unit `c = s_00 t_0 + s_01 t_10 + s_1 t_11` has `C_Q(c^a) = <c>` for all `a != 0`, and that
`g c^a g^-1 = c^b` forces `b = +-a`. So no Heisenberg center is conjugate to a power of
`c`, and neither is the base of any `BS(1,k)` with `|k| >= 2`. The proof reads
coefficients on deep fundamental domains near the attractor, so it needs a unit with
point dynamics. A genuinely linear center has none. There `K_0(R) = 0` also kills the
determinant-degree invariant that would work over commutative coefficients (artifact,
Section 4).

**Earlier outline, now subsumed.** Let `u, z` be elements of `V` with disjoint clopen
supports `U, Z`. Suppose each acts on its support as a north--south map: one
attracting and one repelling fixed point, with every other orbit running from
the repeller to the attractor. Then no `w` in `Q` satisfies `w u w^-1 = u z`. In
particular no Heisenberg subgroup has a generator `u` and center `z` of this
form.
- View `w` as a compactly supported locally constant function on the Cuntz
  groupoid, acting on `M = C(C, F_2)` by `(w f)(x) = sum_(r(gamma)=x) w(gamma) f(s(gamma))`.
  This action is faithful because `R` is simple.
- `w u = (uz) w` says that `w` is invariant under
  `T(gamma) = [uz] gamma [u^-1]`. The source of `T^m gamma` is `u^m s(gamma)` and
  its range is `(uz)^m r(gamma)`.
- The degree cocycle is bounded on the compact support of `w`. The degree of the
  `m`-th power of a north--south element at a point of its support grows linearly,
  with nonzero slope, while points outside the support contribute `0`.
- Any arrow in which exactly one endpoint moves under the relevant power therefore
  has drifting degree along its `T`-orbit, and `w` vanishes on it. The surviving
  arrows show `w(M_U) <= M_U + M_Z` and `w(M_Z + M_rest) <= M_rest`, where
  `rest = C - (U cup Z)`.
- Since `w` is bijective, its restriction `A : M_U -> M_U + M_Z` is bijective and
  intertwines `u` with `uz`. But the `u`-invariant functions in `M_U` are the
  constants on `U`, a space of dimension `1`, while the `uz`-invariant functions
  in `M_U + M_Z` have dimension `2`. This is a contradiction.

The outline uses bisection structure of `u` and `z`. It does not touch
configurations in which the center is a genuinely linear unit, and that is where
the claim remains open.
