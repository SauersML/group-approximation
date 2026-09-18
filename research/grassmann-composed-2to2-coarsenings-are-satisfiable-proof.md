---
rg: 2
id: grassmann-composed-2to2-coarsenings-are-satisfiable-proof
kind: route
title: Folding offsets are coboundaries against the dimension-m Lemma 4.1 representative, so one gauge labelling satisfies every exact triple of a DKKMS agreement game
target: grassmann-composed-2to2-coarsenings-are-satisfiable
requires: [linear-view-unique-verifiers-collapse-to-quotient-coarsening]
artifacts:
  - experiments/dkkms-coarsening-2026-09-17/check_dkkms_coarsening.py
---

Notation is as in the target claim. All spaces are over `F_2`. `Fun(S)` denotes
the linear functionals on a subspace `S`, and `Ann(M) <= Fun(S)` those vanishing
on `M <= S`.

## Imported (verbatim citations)

Dinur, Khot, Kindler, Minzer, Safra, *Towards a Proof of the 2-to-1 Games
Conjecture?*, ECCC TR16-198, Section 4.2.

- Vertices: "A ={(U,L )|U∈U , L∈Gr(XU,𝓁 ), L∩HU ={0}}", with
  "HU = Span(xe :e∈U)" and "hU :HU→ F2, h U(xe) =be,∀e∈U (12)".
- Legitimacy: "(a) the equations e1,...,e k are distinct and do not share
  variables and (b) for any pair of variables x∈ ei andy∈ ej, i⁄= j,x,y do not
  appear together in any equation in the instance (X, eq)". The regular 3LIN
  instance has "two distinct equations share at most one variable".
- Folding: "C(U0,L 0) ={(U,L )∈A|L +HU +HU0 =L0 +HU +HU0}".
- **Lemma 4.1.** "For (U,L ) there is an𝓁-dimensional subspaceR⊆{ 0, 1}n such
  that C(U,L ) = {(U′,L′)∈A|L′ +HU′ =R +HU′}. Furthermore, for any two vertices
  (U1,L 1), (U2,L 2)∈ A, eitherC(U1,L 1) =C(U2,L 2) orC(U1,L 1)∩ C(U2,L 2) =φ."
- Unfolding (Definition 4.2): "For every (U,L )∈C we unfold σ = ˜A(C) by
  deﬁning,A(U,L ) = ˜σU|L, where ˜σU is the (HU,hU) extension ofσ".
- The 2-to-1 constraint: "The constraint between (U,L ) and (V,L′) accepts pairs
  (σ,σ′) iff σ|L′ =σ′", aggregated over members of a class after unfolding.
- **Claim 4.3.** "LetC∈ ˜A, letσ = ˜A(C), and for each(U,L )∈C letA(U,L ) = ˜σU|L
  be its unfolding. Then for any subspaceD and for any (U1,L 1), (U2,L 2)∈C such
  thatD⊆L1∩L2,A(U1,L 1)|D =A(U2,L 2)|D." So an aggregated folded constraint
  coincides with the constraint through any single member, and every constraint
  of `G_folded` is one agreement edge.

The construction has a free dimension parameter `l`, and Lemma 4.1 is stated
for it. We apply it to the same 3LIN instance and the same set of legitimate
`U` with `l` replaced by an arbitrary `m >= 1`. This gives the dimension-`m`
vertex set `A_m = {(U, N) : N in Gr(X_U, m), N meet H_U = {0}}` and the
dimension-`m` folding classes `Q`. For each class we fix one space `R_Q` as in
Lemma 4.1. So for every `(U, N) in Q`, `N + H_U = R_Q + H_U`.

Imported from the graph:
`linear-view-unique-verifiers-collapse-to-quotient-coarsening` (ESTABLISHED),
items 2 and 3 with `p = 2`.

## Lemma A (independence and consistent offsets)

Let `U, U'` be legitimate.

(i) Every equation `e` of `U` that is not an equation of `U'` meets the variables
of `U'` in at most one variable.

*Proof.* Suppose two variables `i, j` of `e` lie in `U'`. If they lie in one
equation `e'` of `U'`, then `e` and `e'` share two variables, so `e = e'`,
contrary to assumption. Otherwise they lie in different equations of `U'` and
appear together in `e`, which contradicts legitimacy (b) of `U'`.

(ii) The vectors `x_e`, for `e` ranging over the equations of `U` and of `U'`
without repetition, are linearly independent. So `H_U meet H_U'` is spanned by
the common equations, and `h(x_e) = b_e` defines one linear `h` on `H_U + H_U'`
that restricts to `h_U` and to `h_U'`.

*Proof.* Let `sum_(e in T) x_e = 0`. An equation `e in T` of `U` that is not in
`U'` has, by (i), at least two variables outside `U'`. Those variables lie in no
other equation of `U`, since the equations of `U` are disjoint, and in no
equation of `U'`. So they have odd coefficient, which is a contradiction. Hence
`T` consists of equations of `U'`, which are disjoint, so `T` is empty.

(iii) Let `S` be a subspace with `S <= X_U meet X_U'` and `S meet H_U = {0}`.
Then `S meet (H_U + H_U') = {0}`.

*Proof.* Let `s in S` with `s = sum_(e in T) x_e + sum_(e' in T') x_e'`, where
`T` is a set of equations of `U` and `T'` a set of equations of `U'`. Take
`e' in T'` not an equation of `U`. By (i) it has at least two variables outside
`U`. They occur in no other equation of `T'` (disjointness) and in no equation
of `T` (all inside `U`). So `s` is nonzero outside `U`, contradicting
`s in X_U`. So `T'` consists of equations of `U`, `s in H_U`, and `s = 0`.

(iv) Let `C` be a class of `A_m`, `R_C` a Lemma 4.1 representative, and
`(U, L) in C`. Then `R_C <= X_U`, `R_C meet H_U = {0}`, and the map
`r : L -> R_C` taking `x` to its `R_C`-component in `R_C + H_U` is a linear
bijection.

*Proof.* `R_C <= R_C + H_U = L + H_U <= X_U`. Since `L meet H_U = {0}`,
`dim(R_C + H_U) = m + dim H_U`, so `R_C meet H_U = {0}`, the decomposition in
`R_C + H_U` is unique, and `r` is linear. If `r x = 0`, then `x in L meet H_U`,
so `x = 0`. Both spaces have dimension `m`.

In particular, `(U, M) in A_(dim M)` for every member `(U, L)` of `C` and every
nonzero `M <= R_C`. This justifies item 2 of the target.

## Lemma B (exactness sees one subspace)

Fix an agreement edge `e` with endpoints `z_1, z_2`, subspace `W`, maps
`r_i : L_i -> R_i` (for a B-vertex, `R_i = L_i = L'` and `r_i = id`), and
`H_e = {(s_1, s_2) : u_1(s_1)|W = u_2(s_2)|W}`. By Lemma A(iv), each `r_i` is
injective on `W`, so `s -> u_i(s)|W = s o r_i + h_(U_i) o (id - r_i)` maps
`Fun(R_i)` affinely onto `Fun(W)`. Hence both projections of `H_e` are onto,
`Phi` is a linear outer game in the sense of the collapse theorem, and
```text
H_e = { (s_1, s_2) : exists phi in Fun(W), u_1(s_1)|W = phi = u_2(s_2)|W }.
```
An affine view of `z_i` has linear kernel `K_i <= Fun(R_i)`. Write
`K_i = Ann(M_i)` with `M_i <= R_i`, so `A_(z_i)/K_i = Fun(M_i)`.

**Lemma B.** `H_e` induces a bijection `Fun(M_1) -> Fun(M_2)` if and only if
`M_1 = r_1(N)` and `M_2 = r_2(N)` for one `N <= W`. In that case the bijection is
`beta(s_1|M_1) = s_2|M_2` where `u_1(s_1)|N = u_2(s_2)|N`.

*Proof.* Suppose `H_e` induces a bijection. Fix `s_1`. The `s_2` with
`(s_1, s_2) in H_e` form a coset `s_2* + Ann(r_2 W)`. `s_2|M_2` is constant on
it, so every functional vanishing on `r_2 W` vanishes on `M_2`, and
`M_2 <= r_2 W`. Symmetrically `M_1 <= r_1 W`. Put `N_i = W meet r_i^(-1)(M_i)`,
so `r_i(N_i) = M_i`. For `x in N_i`,
`s_i(r_i x) = phi(x) + h_(U_i)(x - r_i x)`. So on `H_e`, `s_i|M_i` and
`phi|N_i` determine each other. Then `phi|N_1` must determine `phi|N_2` for all
`phi in Fun(W)`. If `N_2` is not contained in `N_1`, some `phi` vanishes on
`N_1` but not on `N_2`, and `phi = 0` gives a second value. So `N_2 <= N_1`,
symmetrically `N_1 <= N_2`, and we put `N = N_1 = N_2`. Conversely, if
`M_i = r_i(N)`, then `s_1|M_1 <-> phi|N <-> s_2|M_2` are bijections, which gives
the stated `beta`.

By item 2 of the collapse theorem, the exact cross triples of `V` on `e` are
triples whose kernel pair satisfies Lemma B, with constraint `beta`. Exact
triples with `o(w) = o(w')` have `K = K'` and `beta = id`, so every labelling
of `Can` satisfies them.

## Lemma C (the gauge is well defined)

For a nonzero subspace `N` and a legitimate `U` with `(U, N) in A_m`, let `Q` be
its dimension-`m` class and `R_Q` the fixed representative. Put
`g_U(N)(x) = h_U(x - pi_(Q,U)(x))` for `x in N`, where `pi_(Q,U)(x)` is the
`R_Q`-component of `x` in `R_Q + H_U = N + H_U`.

**Lemma C.** `g_U(N)` is linear, and `g_U(N) = g_(U')(N)` whenever
`(U, N), (U', N) in A_m`.

*Proof.* Linearity follows from Lemma A(iv) and linearity of `h_U`. The classes
agree, since `N + H_U + H_U' = N + H_U + H_U'` puts `(U', N)` in `C(U, N)`.
Write `x = q + y = q' + y'` with `q, q' in R_Q`, `y in H_U` and `y' in H_U'`.
Then `q - q' = y' - y in R_Q meet (H_U + H_U')`. By Lemma A(iv),
`R_Q <= X_U meet X_U'` and `R_Q meet H_U = {0}`. So Lemma A(iii) gives
`q = q'`, hence `y = y' in H_U meet H_U'`, and `h_U(y) = h_U'(y)` by
Lemma A(ii).

Write `g(N)` for the common value. The **gauge labelling** of `Can` is
```text
F*(z, M) = g(M),      M <= R_z nonzero,  F*(z, 0) = 0.
```
For an A-class `z`, `g(M)` exists by Lemma A(iv). For a B-vertex `(V, L')` and
`M <= L'`, use any legitimate `U` with `(U, M) in A_m`; if there is none, put
`F*(z, M) = 0`. This is item 2 of the target, and `F*(z, M)` depends only on `M`.

## Theorem (perfect satisfiability)

`F*` satisfies every exact triple of every DKKMS agreement game, so
`val(Can(Phi, V)) = 1` for every affine-view unique verifier `V` and every 3LIN
input.

*Proof.* Same-owner exact triples are trivial (Lemma B). Take an exact cross
triple on `e`, with `M_i = r_i(N)`, `N <= W`, and `N` nonzero. Its constraint
`beta` holds on `(F*(z_1, M_1), F*(z_2, M_2))` iff some `phi in Fun(N)` satisfies
`F*(z_i, M_i)(r_i x) = phi(x) + h_(U_i)(x - r_i x)` for `x in N` and `i = 1, 2`.
(Extend `phi` to `W` and lift it to `s_i` by the onto maps of Lemma B.) It is
enough to show that, for each `i`,
```text
F*(z_i, M_i)(r_i x) + h_(U_i)(x - r_i x) = g(N)(x)     for all x in N.     (*)
```
Fix `i`, drop the index, and suppose first that `z` is an A-class through `(U, L)`.
Since `N <= W <= L`, `N meet H_U = {0}` and `(U, N) in A_m`. Also
`M + H_U = N + H_U`, so `(U, M)` and `(U, N)` lie in one class `Q`, and
`F*(z, M) = g_U(M)` is measured against the same `R_Q + H_U` as `g_U(N)`. For
`x in N`, `r x = x - (x - r x)` with `x - r x in H_U`. Uniqueness of the
decomposition gives `pi_(Q,U)(r x) = pi_(Q,U)(x)`, so
```text
g_U(M)(r x) = h_U(x - pi_(Q,U)(x)) - h_U(x - r x).
```
By Lemma C, this is (*). For a B-vertex, `r = id`, `M = N`, and there is no
offset. If some legitimate `U` has `(U, N) in A_m`, then `F*(z, N) = g(N)` by
Lemma C, and (*) holds. Such a `U` exists whenever the other endpoint is an
A-class (take its member `U_j`). If none exists, both endpoints are B-vertices,
both labels are `0` on `N`, and `beta` holds with `phi = 0`. In every other case
both sides of `beta` are induced by `phi = g(N)`.

## Corollary (class kill)

By `linear-view-unique-verifiers-collapse-to-quotient-coarsening`, items 1 and 3
with `p = 2`, every affine-view unique verifier with oblivious completeness `c`
over a DKKMS agreement game `Phi` satisfies
```text
val(V(Phi)) >= w_ex * val(Can(Phi, V)) = w_ex >= 2c - 1
```
on every input. A reduction to `Gap-UG(c, s)` therefore has `s >= 2c - 1`.

*The check.* `experiments/dkkms-coarsening-2026-09-17/check_dkkms_coarsening.py`
verifies Lemma 4.1 at each dimension, Lemma A(iii) for representatives, Lemma B by
enumerating `H_e`, Lemma C, and (*), on unsatisfiable instances (see the target's
Attempts).
