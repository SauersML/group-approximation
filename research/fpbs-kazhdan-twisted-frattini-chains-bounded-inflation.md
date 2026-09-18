---
rg: 2
id: fpbs-kazhdan-twisted-frattini-chains-bounded-inflation
kind: claim
title: Kazhdan groups carry no twisted Frattini chain of linear crown count whose acting quotients have bounded p-abelianization, at any Plancherel weight
distinct_from:
  fpbs-kazhdan-twisted-certificates-vanishing-weight: that kills abelian-crown certificates of weight bounded below on p-Frattini closed kernel families; this needs no weight bound and replaces it by a bound on d_p of the acting quotient, on chains closed under the M-radical instead of the scalar Frattini subgroup, so it reaches low-weight crowns such as natural modules of SL_n(F_p).
  fpbs-kazhdan-twisted-lift-independence: that proves one lifting step and leaves descent compatibility open; this proves descent compatibility with loss at most d_p(Q) and runs the full support-shrinking iteration to a contradiction with (T).
  fpbs-kazhdan-positive-rank-gradient: that asks for a positive-gradient Farber chain; this is a class-killing obstruction for one family of abelian non-central crown certificates.
artifacts:
  - experiments/twisted-lackenby-lift-2026-09-17/independence_bound.py
  - experiments/twisted-lackenby-lift-2026-09-17/independence_results.txt
---

**Proposed ESTABLISHED (written deduction, unrefereed).** It is built on the
lemma of `fpbs-kazhdan-twisted-lift-independence` and on the ingredients (K),
(L6.1) and (Tr) of Theorem B in
`research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md`.

## Definitions

- `N` is a finite index subgroup of a group `Gamma`, and `M` is an absolutely
  irreducible nontrivial `F_p[N]`-module of dimension `d`. Its kernel is `K`,
  and `Q = N/K`.
- The **restricted derivation rank** `h(N;M)` is the dimension of the image of
  restriction `H^1(N;M) -> Hom_Q(K,M)`. The five-term sequence gives
  `mu(N;M) d - h^2(Q;M) <= h(N;M) <= mu(N;M) d`, with `mu` the abelian crown
  count of `fpbs-kazhdan-twisted-certificates-vanishing-weight`.
- The **M-radical** `R_M(N)` is the intersection of `K` with the kernels of all
  derivations `N -> M`. Inner derivations and derivations inflated from `Q`
  vanish on `K`. So `R_M(N) = K cap ker Xi` for any `h(N;M)` derivations `Xi`
  with independent restrictions, and `N/R_M(N)` is an extension of `Q` by
  `M^h`.
- A **twisted Frattini chain** is a sequence `(N_i, M_i)` as above with
  `N_(i+1) <= R_(M_i)(N_i)` and `[R_(M_i)(N_i) : N_(i+1)]` coprime to `p`.
  The members need not be normal in `Gamma`.

## Statement

**Theorem.** Let `Gamma` be a Kazhdan group, `p` a prime, and `c > 0`,
`D >= 0`. There is no twisted Frattini chain `(N_i, M_i)` in `Gamma` with:

1. (linear crown count) `h(N_i;M_i) >= c [Gamma:N_i] dim M_i` for all `i`;
2. (bounded inflation) `d_p(N_i/K_i) <= D` for all `i`;
3. (a start) `d_p(N_i)` is unbounded along the chain, **or** `M_i` is
   self-dual for infinitely many `i`.

Condition 3 is used only once, to find the first carried classes. A single
member of large enough index with `d_p(N_i) >= D + ceil(2|R|/c) + 1`, or with
`M_i` self-dual, suffices, where `<X|R>` is a finitely presented Kazhdan cover
of `Gamma`. The self-dual start covers every module with a nondegenerate
invariant bilinear form, e.g. natural modules of `Sp_(2n)(F_p)`, orthogonal
groups and `SL_2(F_p)`, so there condition 3 is automatic.

**What it kills.** Take an abelian-crown certificate for
`fpbs-kazhdan-positive-rank-gradient` built from a chain of modules whose
acting quotients are perfect, or have bounded `p`-abelianization. Examples are
natural modules of `Sp_(2n)(F_p)`, or of `SL_n(F_p)` on chains with
unbounded `d_p` (absolutely irreducible over `F_p`), whose Plancherel weight
tends to zero. If each next member sits inside the previous `M`-radical with
index prime to `p`, the certificate cannot live in a Kazhdan group. No
Plancherel-weight bound is used anywhere.

## Proof

**Setup.**
- Take a finitely presented Kazhdan cover `pi: G -> Gamma` with presentation
  `<X|R>`, Kazhdan pair `(X,kappa)`, and `eps = kappa^2/(4|X|)`.
- Put `A_i = pi^(-1)(N_i)` and `K_i = pi^(-1)(ker of N_i on M_i)`. Inflate
  `M_i` and scalar classes to `A_i`. The acting quotient is unchanged.
- Fix `h = h(N_i;M_i)` derivations of `N_i` with independent restrictions and
  inflate them to `Xi` on `A_i`. Put `R_i = K_i cap ker Xi`, which is
  `pi^(-1)(R_(M_i)(N_i))`. Only these inflated derivations are used; `A_i`
  may have more, which is harmless.
- All scalar cocycles are cellular cocycles on covering complexes of the
  presentation complex of `G`, and supports are measured there.
- `M` is a local system on `K_(A_i)` (whose fundamental group is `A_i`).
  Trivialize it along a maximal tree, so each derivation is an `M`-valued
  1-cocycle `xi(e)` with transports `rho`. Its path function satisfies
  `xi(gamma delta) = xi(gamma) + rho(gamma) xi(delta)` on the path groupoid.
  On the cover for `R_i`, `Xi(v)` (path function along any path from the base
  vertex to `v`) is well defined, since two such paths differ by a loop in
  `R_i`, where `Xi` vanishes and `rho` is trivial.
- The twisted lift is the path-function construction of
  `fpbs-kazhdan-twisted-lift-independence` on `K_(A_i)`:
  `Y_a(e) = sum a_jk c_j(e) Xi_k(initial vertex of e)`. Its proof uses only the
  groupoid cocycle identity, loops at the base vertex, and one `M`-valued
  condition per 2-cell (a relator loop has `C = 0` and `Xi = 0`). So it runs
  unchanged, with `r` the number of 2-cells.
- Fix `u = ceil(2|R|/c)`, `w = u + D`, and `theta = theta_w < 1` from (L6.1).

**Step 0 (the inflation loss is at most `d_p(Q)`).** Let `C` be a subspace of
`H^1(A;F_p)`, where `A = A_i`, `M = M_i` and `R = R_i` (normal in `A`, since
`Xi` is `A`-equivariant on `K_i`). The kernel of
restriction `H^1(A;F_p) -> H^1(R;F_p)` is `Hom(A/R, F_p)`, by
inflation-restriction.
- `P = A/R` is an extension `1 -> M^h -> P -> Q -> 1`.
- `M` is nontrivial and irreducible, so `[Q,M] = M`. Hence `M^h` lies in
  `[P,P]` and `Hom(P,F_p) = Hom(Q,F_p)`.
- So restriction to `R` loses at most `d_p(Q) <= D` dimensions from any space
  of classes.

**Step 1 (carried classes).** Suppose we have a stage `i` and a space `V` of
cocycles on the covering complex `K_(A_i)`. Assume every nonzero element of
`V` represents a nonzero class, `dim V >= w + 1`, and the support fraction is
at most `sigma`.
- (L6.1) gives `W <= V` of dimension `w` with support fraction at most
  `theta sigma`.
- By Step 0, `W cap ker(res to R_i)` has dimension at most `D`. Choose a
  `u`-dimensional complement `C` of it inside `W`.
- Then `C` has support fraction at most `theta sigma`, and `C` restricts
  injectively to `R_i`, which is the twisted-lift invariant
  `x0 = dim C(K_i cap ker Xi_i) = u`.

**Step 2 (twisted lift).** The `h` derivations `Xi` have independent
restrictions, so `Xi(K_i) = M_i^h` (step 2 of the weight-transfer proof).
- `K_i cap ker C` has index at most `p^u` in `K_i`. So `Xi(K_i cap ker C)` has
  codimension at most `u` in `M^h`, and `v0 >= h - u/d`.
- The lemma of `fpbs-kazhdan-twisted-lift-independence` applies with
  `r = |R|[G:A_i]`. It gives at least
  `t >= u(h - u/d) - |R|[G:A_i] d` independent `Q`-equivariant classes
  `R_i -> M_i`.
- With `h >= c[G:A_i] d` and `cu >= 2|R|`, this is
  `t >= |R|[G:A_i] d - u^2/d`.
- Their coordinates span at least `t d` classes in `H^1(R_i;F_p)`.
- Each coordinate is represented by the lifted cochain `Y_a` on `K_(R_i)`,
  which vanishes on every edge over which all `c in C` vanish. So the span `V'`
  has support fraction at most `theta sigma`.

**Step 3 (coprime descent).** `[R_i : A_(i+1)]` is coprime to `p`, so by (Tr)
restriction `H^1(R_i;F_p) -> H^1(A_(i+1);F_p)` is injective. Pulling back
cocycles preserves support fractions.
- So `V'` restricts to a space on `K_(A_(i+1))` of dimension at least
  `t d >= |R|[G:A_i] d^2 - u^2`, with fraction at most `theta sigma`.
- Once `[G:A_i] > (u^2 + w + 1)/|R|` this is at least `w + 1`, and Step 1
  applies at stage `i+1`.
- Hypothesis 1 holds at `i+1`, and the index only grows.

**Step 4 (self-dual start: a quadratic count).** Let `M = M_i` be self-dual,
with invariant nondegenerate form `B(x,y) = epsilon B(y,x)`,
`epsilon = +-1` (it exists because `Hom_Q(M,M*)` is one-dimensional).
- For `a` in `F_p^(h x h)` define the `F_p`-cochain on the cover for `R_i`:
  `Y_a(e) = sum a_jk B(Xi_j(v), rho(v) xi_k(e))`, where `v` is the initial
  vertex of `e` and `rho(v)` the transport along a path to it. Its path function satisfies
  `Phi_a(uv) = Phi_a(u) + B_a(Xi u, u.Xi v) + Phi_a(v)`, using `Q`-invariance
  of `B`.
- A 2-cell at a vertex `g` evaluates to `Phi_a(boundary loop)`, because `Xi`
  vanishes on relator loops. So the cocycle space `Z` has codimension at most
  `r = |R|[G:A_i]` (one scalar condition per 2-cell, not `dim M`).
- On `R_i`, `Phi_a` is a homomorphism. For `x, y` in `K_i`,
  `Phi_a(xy) = Phi_a(x) + B_a(Xi x, Xi y) + Phi_a(y)`, and as in step 2 of the
  independence lemma
  `Phi_a([x,y]) = B_a(Xi x, Xi y) - B_a(Xi y, Xi x)`, with `[x,y]` in `R_i`.
- `Xi(K_i) = M^h`, and `x, y` range independently. So `Phi_a|R_i = 0` forces
  `sum (a_jk - epsilon a_kj) B(m_j, m'_k) = 0` for all `m, m'` in `M^h`, i.e.
  `a = epsilon a^T`. That subspace has dimension at most `h(h+1)/2`.
- Hence `d_p(R_i) >= h(h-1)/2 - |R|[G:A_i]`. With `h >= c[G:A_i] d` this
  exceeds `w + 1` once `[G:A_i]` is large, and (Tr) carries the classes to
  `A_(i+1)`.

**Step 5 (start and contradiction).**
- By hypothesis 3, pick a stage `i_0` of index above `(u^2 + w + 1)/|R|` (and
  above the Step 4 threshold) with `d_p(A_(i_0)) >= d_p(N_(i_0)) >= w + 1`, or
  with `M_(i_0- 1)` self-dual, in which case Step 4 gives the classes on
  `A_(i_0)`. Take `V` spanned by `w + 1` independent classes, with
  `sigma <= 1`.
- Run Steps 1-3 for `m` stages with `theta^m < eps`. At stage `i_0 + m` some
  nonzero class on `K_(A_(i_0+m))` has a representative of support fraction
  below `eps`. It is supported on fewer than `kappa^2 [G:A]/4` edges.
- This contradicts (K). QED.

## Calibration

- **Numerical check of Step 0.** In
  `experiments/twisted-lackenby-lift-2026-09-17/independence_results.txt`
  (`Q = S_3` on `F_2^2`, `d_2(S_3) = 1`), the loss `u - x0` is:
  - `F_2` with both classes: `2 - 1 = 1`;
  - `F_2` with the sign class: `1 - 0 = 1`;
  - `F_2` with `U = y`: `1 - 1 = 0`;
  - `F_3`: `3 - 2 = 1`;
  - genus 2, all classes: `4 - 3 = 1`.
  It never exceeds `d_2(Q) = 1`, and it is attained when the sign character is
  among the carried classes.
- **Free groups** (not Kazhdan). Chains with hypotheses 1-3 are not excluded:
  every step except (K) goes through, and the output is classes of vanishing
  relative support.
- **Known Kazhdan groups.** `SL_3(Z)` congruence members have `h` bounded, so
  hypothesis 1 fails, as it must.

## What survives

1. **Unbounded inflation.** Acting quotients with `d_p(Q_i) -> infinity`,
   e.g. module chains whose images are `p`-groups extended by large elementary
   abelian tops. The loss in Step 0 is exactly the obstruction. The fixed
   support-shrinking rate `theta_(u+D)` is what needs bounded `D`.
2. **Chains not closed under the M-radical with prime-to-`p` index.** The
   Sylow step of Theorem B needs an inheritance lemma for crown counts. The
   pigeonhole over `Ind` composition factors keeps linear `h/dim`, but does not
   keep `d_p(Q)` bounded.
3. **The start.** Chains whose members eventually have bounded `d_p` and
   non-self-dual modules (for instance natural modules of `SL_n(F_p)`,
   `n >= 3`, on `p`-perfect members) give no first carried classes. A
   certificate for `M*` at one stage gives many classes on the smaller
   radical `R_M cap R_(M*)` through the same pairing (`a` is then forced to
   vanish), but the chain closure would have to use that radical.
4. Non-abelian crowns and the gap `d(Gamma_n) > d(Gamma_n-hat)`, untouched.
