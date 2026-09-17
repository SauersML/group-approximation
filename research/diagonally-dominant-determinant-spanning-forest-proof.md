---
rg: 2
id: diagonally-dominant-determinant-spanning-forest-proof
kind: route
title: Split off finite components, dominate the rest by a gauge-transformed wired spanning forest Laplacian, and apply Lyons' nonnegativity of tree entropy
target: diagonally-dominant-integral-matrices-obey-determinant
requires: []
---

Direct proof (2026-09-17, lane sw-047). Notation as in the target.

**External inputs.**
- **(L)** R. Lyons, *Identities and inequalities for tree entropy*, CPC 19
  (2010), arXiv:0712.3035, theorems `t.logdet` and `t.nonneg` (Section 3).
  Let `rho` be a unimodular probability measure on rooted, connected, infinite,
  unweighted, locally finite graphs with `E log deg(o) < infinity`, and let
  `Delta = D - A` be the combinatorial Laplacian. Then
  `h(rho) = E_rho integral_[0,infinity) log lambda d mu_(Delta,o)(lambda) >= 0`,
  where `mu_(Delta,o)` is the spectral measure of `Delta` at the root and the
  atom at `0` counts as `-infinity`.
- **(W)** The wired uniform spanning forest (WUSF) of a connected, locally
  finite, infinite graph `X` is a probability measure on spanning subgraphs of
  `X`. It is invariant under every automorphism of `X`, and almost surely every
  component is an infinite tree. See Benjamini--Lyons--Peres--Schramm,
  *Uniform spanning forests*, Ann. Probab. 29 (2001), Section 5, and
  Lyons--Peres, *Probability on Trees and Networks*, Ch. 10.
  - **Why components are infinite.** A finite component `K` would require the
    forest to contain no edge of the finite edge boundary of `K`. That event
    has probability `0` for the UST of every wired exhaustion, since a spanning
    tree connects `K` to the rest. Hence it has probability `0` in the limit.
    There are only countably many `K`.
- **(M)** `log` is operator monotone on `(0, infinity)`. If `0 <= S <= T` are
  bounded operators and `eps > 0`, then `log(S + eps) <= log(T + eps)`.

## Step 0: kernel form

`T` acts on `l^2(V)`, `V = G x [n]`, by right multiplication. Its kernel is
`K((x,i),(y,j)) = T_ij(x^-1 y)`.
- **Symmetry and invariance.** `K` is integer-valued, symmetric (because `T`
  is self-adjoint), and invariant under the free action `h.(x,i) = (hx,i)`.
- **Diagonal dominance.** Each row has finitely many nonzero entries, and
  `K(v,v) >= sum_{w != v} |K(v,w)|` for every `v`.
- **Spectral measure.** `mu_T = sum_i mu_(T,(e,i))`, and
  `log det_N(G)(T) = integral_(0,infinity) log lambda d mu_T`.

## Step 1: edge decomposition

Let `X` be the simple graph on `V` with an edge `{v,w}` whenever `v != w` and
`K(v,w) != 0`. For such an edge set `eps_vw = sign K(v,w)` and
`u_vw = 1_v + eps_vw 1_w`. The rank-one operator `u_vw u_vw^*` has `1` at
`(v,v)` and `(w,w)` and `eps_vw` at `(v,w)` and `(w,v)`. Hence

    T = sum_{edges {v,w} of X} |K(v,w)| u_vw u_vw^*  +  W,
    W = diag( K(v,v) - sum_{w != v} |K(v,w)| ) >= 0.

In particular `T >= 0`. `G` acts on `X` by automorphisms. `X` is locally finite
with bounded degree.

## Step 2: finite and infinite components split off

The component of `(x,i)` in `X` is `x` times the component of `(e,i)`. So
whether it is finite depends only on `i`, and `[n] = I_fin ⊔ I_inf`.
- `T` has no entries between different components, and `W` is diagonal.
- So `T = T_fin ⊕ T_inf` on `l^2(G x I_fin) ⊕ l^2(G x I_inf)`, and
  `mu_T = mu_fin + mu_inf` with `mu_fin = sum_{i in I_fin} mu_(T,(e,i))`.

**Finite part.** Take a finite component `C` with stabilizer
`St_C = {h : hC = C}`. The group `St_C` is finite, since `G` acts freely and `C`
is finite.
- **Counting types in `C`.** If `(g,i)` and `(g',i)` both lie in `C`, then
  `h = g'g^-1` maps one to the other and `hC ∩ C` is nonempty, so `h in St_C`.
  Hence each type `i` occurring in `C` occurs exactly `|St_C|` times.
- **The finite-part measure.** Let `C_1, ..., C_m` represent the `G`-orbits of
  finite components; distinct orbits use disjoint sets of types. By invariance
  of `v -> mu_(T,v)`,
  `mu_fin = sum_k (1/|St_(C_k)|) sum_{v in C_k} mu_(T_(C_k), v)`.
  Here `T_C` is the finite integer symmetric matrix `K|_(C x C)`, and the inner
  sum is its eigenvalue counting measure.
- **Integrality.** The product of the nonzero eigenvalues of `T_C` is, up to
  sign, the lowest nonzero coefficient of its characteristic polynomial. This
  is a nonzero integer.

Therefore
`integral_(0,infinity) log lambda d mu_fin = sum_k |St_(C_k)|^-1 log det'(T_(C_k)) >= 0`.
This step does not use diagonal dominance.

**Why components rather than supports.** Support subgroups do not detect
finite components. For example, `[[1, g], [g^-1, 1]]` has components of size 2
over any `G`.

## Step 3: the forest and unimodularity

Assume `I_inf` is nonempty; otherwise we are done. Let `X_inf` be the induced
subgraph on `V_inf = G x I_inf`. Apply (W) to each (infinite) component of
`X_inf` independently. The result is a random spanning forest `F` of `X_inf`.
- **Invariance.** Its law is invariant under `G`, since `G` permutes components
  and WUSF is automorphism-invariant.
- **Components.** Every component of `F` is an infinite tree of degree at most
  `d = max deg X`.

**The rooted tree.** Pick `i` uniformly from `I_inf` and let `rho_F` be the law
of the rooted graph `(F_(e,i), (e,i))`, the component of the root in `F` up to
rooted isomorphism. Then `rho_F` is unimodular.
- Let `f >= 0` be a Borel function on doubly rooted graphs. Put
  `m(v,w) = E f(F_v, v, w)`, which is `0` when `w` is not in `F_v`. By
  invariance, `m(hv,hw) = m(v,w)`.
- By Tonelli and the substitution `g -> g^-1`,

      sum_{i,j in I_inf} sum_{g in G} m((e,i),(g,j))
        = sum_{i,j} sum_g m((g^-1,i),(e,j))
        = sum_{j,i} sum_{h} m((h,i),(e,j)),

  which is the mass-transport principle for `rho_F`.
- `rho_F` is concentrated on infinite unweighted trees with bounded degree, so
  `E log deg(o)` is finite. By (L), `h(rho_F) >= 0`.

## Step 4: the forest operator and the gauge

For a realization of `F`, set

    S_F = sum_{edges {v,w} of F} u_vw u_vw^*.

**Domination.** `T_inf - S_F` is the sum of three nonnegative pieces:
- `sum_{edges of F} (|K(v,w)| - 1) u_vw u_vw^*`;
- `sum_{edges of X_inf not in F} |K(v,w)| u_vw u_vw^*`;
- `W|_(V_inf)`.

So `0 <= S_F <= T_inf` for every realization.

**Gauge.** In each tree of `F` fix a vertex `r` and define `sigma: V_inf -> {±1}`
by `sigma(r) = 1` and `sigma(w) = -eps_vw sigma(v)` along tree edges. This is
consistent because `F` is a forest. `M_sigma` is diagonal and unitary, and:
- `M_sigma u_vw u_vw^* M_sigma` has off-diagonal entry
  `eps_vw sigma(v) sigma(w) = -1`;
- the diagonal of `S_F` at `v` is `deg_F(v)`;
- so `M_sigma S_F M_sigma = Delta_F`, the combinatorial Laplacian of `F`;
- `M_sigma delta_v = ±delta_v`, so for every Borel `B`,
  `<1_B(S_F) delta_v, delta_v> = <1_B(Delta_F) delta_v, delta_v>`.

In particular `mu_(S_F,v) = mu_(Delta_F,v)`, and this depends only on the rooted
tree `(F_v, v)`. Averaging:

    E sum_{i in I_inf} integral_[0,inf) log lambda d mu_(S_F,(e,i))
      = |I_inf| h(rho_F) >= 0.                                    (*)

Every term is bounded above by `log(2d)`, so the expectations are well defined
in `[-infinity, infinity)`.

## Step 5: monotonicity

Fix `v = (e,i)` with `i in I_inf` and `eps in (0,1]`.
- **Comparison at fixed `eps`.** By (M) and Step 4,
  `<log(S_F + eps) delta_v, delta_v> <= <log(T_inf + eps) delta_v, delta_v>`
  for every realization of `F`.
- **Limit `eps -> 0`.** The spectra lie in `[0, ||T||]`, and `log(lambda + eps)`
  decreases to `log lambda` as `eps -> 0`, bounded above by `log(||T|| + 1)`.
  By monotone convergence, `integral log d mu_(S_F,v) <= integral log d mu_(T,v)`
  in `[-infinity, infinity)`, including the atom at `0`.
- **Summing.** Sum over `i in I_inf` and take `E`; the right side does not
  depend on `F`. With (*) this gives

      integral_[0,infinity) log lambda d mu_inf(lambda) >= |I_inf| h(rho_F) >= 0.

  In particular `mu_inf({0}) = 0`, so `T_inf` is injective, and
  `integral_(0,infinity) log lambda d mu_inf >= 0`.

Adding Step 2: `log det_N(G)(T) >= 0`. ∎

## Corollaries

- **Domination.** If `T >= S >= 0` with `S` SDD and injective, Step 5 applies
  with `S` in place of `S_F`.
- **Rectangular.** `det(B) = det(B^*B)^(1/2)` is Lück's definition for
  non-square matrices.

## Remarks

- **Where diagonal dominance is used.** Only in Step 1, to make `W >= 0`.
- **Where integrality is used.** Only in the finite part (Step 2) and in
  `|K(v,w)| >= 1` for the domination in Step 4. The infinite part is purely
  probabilistic.
- **Where the hypothesis stops.** A non-SDD `T` has no such decomposition.
  For example, `Delta - c` with `c >= 1` is excluded. The bound
  `log det(lambda - A) >= log(lambda - ||A||)` is useless once
  `||A|| > lambda - 1`.
- **The measured-relation analogue.** Steps 1--5 appear to run verbatim for
  SDD elements of `M_n(Z R)` over a probability-measure-preserving countable
  Borel equivalence relation `R`, with the WUSF chosen measurably. This is
  recorded as a remark only, not as a claim.
