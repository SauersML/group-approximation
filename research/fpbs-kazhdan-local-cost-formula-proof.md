---
rg: 2
id: fpbs-kazhdan-local-cost-formula-proof
kind: route
title: Project a cluster-counting field onto Kazhdan invariants, induce on the condensed clusters, and truncate a cheap graphing for the converse
target: fpbs-kazhdan-local-cost-formula
requires:
  - cost-is-constant-on-weak-equivalence-classes
  - fpbs-small-marker-induction-input
  - fpbs-bernoulli-maximal-cost
---

Full written proof. This is not a formal verification.

**Imported inputs.**
- **[K]** Kechris, Corollary 10.14 (node `cost-is-constant-on-weak-equivalence-classes`). For finitely generated
  `Gamma` and free actions, `a ≺ b` implies `C(a) >= C(b)`.
- **[G]** Gaboriau's induction formula (node `fpbs-small-marker-induction-input`). For a complete section `U`,
  unnormalized costs satisfy `C(R) = C(R|U) + mu(X \ U)`.
- **[AW]** Abert--Weiss maximality (node `fpbs-bernoulli-maximal-cost`). Used only to pass from `C(b_Gamma) = 1`
  to fixed price one.
- **[T]** The definition of a Kazhdan pair. Only its standard consequence is used: if a unitary representation
  `pi` has invariant projection `P`, then `kappa ||xi - P xi|| <= max_{s in S} ||pi(s) xi - xi||`. To see this, apply
  the Kazhdan property to `xi' = xi - P xi`, which lies in the subrepresentation without invariant vectors, and note
  that `pi(s) xi - xi = pi(s) xi' - xi'`.

Property (T) groups are finitely generated, so [K] and [AW] apply.

## 1. The cluster Hilbert bundle

- For `x` in `X`, let `Cl(x)` be the countable set of clusters of `G_x`. Enumerate each cluster by its least element
  in a fixed enumeration of `Gamma`. This makes `x -> l^2(Cl(x))` a measurable field of Hilbert spaces, and
  `H = L^2(X; l^2(Cl(x)))` is a Hilbert space with `||xi||^2 = int sum_C |xi_x(C)|^2 dmu`.
- Equivariance gives `Cl(gamma x) = gamma Cl(x)`. The formula `(pi(gamma) xi)_x(C) = xi_{gamma^{-1} x}(gamma^{-1} C)`
  defines a unitary representation, since `mu` is invariant.
- **Invariant vectors condense.** Let `eta` be `pi`-invariant, so `eta_{gamma x}(gamma C) = eta_x(C)`.
  - For `c > 0`, the set `F_c(x) = {C : |eta_x(C)| >= c}` is finite, because `sum_C |eta_x(C)|^2 < infinity`
    almost surely. It is also equivariant.
  - Its size is an invariant function, so it is almost surely constant, equal to `k_c`, by ergodicity.
  - If `eta != 0`, then `k_c >= 1` for small `c`.
  - Let `U(x)` be the union of the clusters `C` with `eta_x(C) != 0`, and `U_c(x)` the union of `F_c(x)`. Then `U_c`
    increases to `U` as `c` decreases to `0`.
- **Finite clusters of a finite equivariant set are null.** Let `T(x)` be the union of the finite clusters in
  `F_c(x)`, a finite set. By invariance, `E[1{g in T}/|T|] = E[1{e in T}/|T|]` for every `g`. Summing over `g` gives
  `P(T nonempty) <= 1`, which forces `P(e in T) = 0`.

## 2. Theorem 1

**The counting field.** Define `xi_x(C) = (|C cap B_R| / |B_R|)^{1/2}`.
- `||xi||^2 = E|V cap B_R|/|B_R| = p`, by invariance.
- `(pi(s) xi)_x(C) = (|C cap s B_R| / |B_R|)^{1/2}`.
- Using `(a^{1/2} - b^{1/2})^2 <= |a - b|` gives
  `||pi(s) xi - xi||^2 <= E sum_C | |C cap B_R| - |C cap s B_R| | / |B_R|`.
- Every cluster meets `B_R union s B_R` in a union of window classes `K`, since a path inside `W` is a path of
  `G_x`. The triangle inequality under merging gives `||pi(s) xi - xi||^2 <= D_{R,W}(s) <= D`.

**Projection.** Let `eta = P xi`. By [T], `||xi - eta||^2 <= D/kappa^2`.
- Since `D < kappa^2 p = kappa^2 ||xi||^2`, `eta != 0`.
- `eta` vanishes on the clusters outside `U`. So `||xi 1_{not U}|| <= ||xi - eta||`.
- The left side equals `(p - u)^{1/2}`, where `u = mu(e in U_x)`, again by invariance. Hence `p - u <= D/kappa^2`.
- By monotone convergence, for every `epsilon > 0` there is `c` with `p - u_c <= D/kappa^2 + epsilon`. Here
  `u_c = mu(e in U_c(x))`, and it is positive once `epsilon < p - D/kappa^2`.

**Cost.** Fix such a `c`, write `k = k_c`, and let `U = {x : e in U_c(x)}`, a set of measure `u_c`.
- Every orbit meets `U`, so `U` is a complete section. Restricted to one orbit, `R|U` has exactly the `k` clusters
  of `F_c` as its points.
- **Graphing `Psi`.**
  - The edges of `G` inside `U`: each edge `{e, f}` at `x` is the pair `(x, f^{-1} x)`, a Borel partial isomorphism.
    Their cost is `E[deg_G(e) 1_U]/2`.
  - Connectors. Off a null set, the cluster relation on `U` is aperiodic, since finite clusters of `F_c` are null by
    Section 1. It therefore has a Borel complete section `V'` of measure at most `d` (node
    `fpbs-small-marker-induction-input`). For `x` in `V'` and each other cluster of `F_c`, add an edge from `x` to
    the nearest point of `V'` in that cluster. Ties are broken by the least word in a fixed enumeration of
    `Gamma`, which is equivariant. This adds at most `(k-1) d` to the cost.
- **`Psi` generates `R|U`.** On each orbit, `R|U` has the `k` clusters of `F_c` as its points. The edges of `G`
  generate each cluster, and the connectors join the clusters.
- By [G], `C(X) = C(R|U) + 1 - u_c <= 1 + E[(deg_G(e)/2 - 1) 1_U] + (k-1) d`. Let `d -> 0`.
- Finally, `-(deg/2 - 1) <= 1`, so
  `E[(deg/2 - 1) 1_U] <= E[(deg/2 - 1) 1_V] + (p - u_c) <= E[(deg/2 - 1) 1_V] + D/kappa^2 + epsilon`.
  Let `epsilon -> 0`.

**Corollary 2.** `X ≺ b_Gamma` gives `C(b_Gamma) <= C(X)` by [K]. A factor of iid is a factor of `b`, so it is weakly
contained in `b`.

## 3. Theorem 3

**Upper bound (`<=`).** Apply Corollary 2 with `R = 0` and `V = Gamma`. Then `p = 1` and `D = 2 delta_W`. The
hypothesis `delta_W < kappa^2/2` is exactly `D < kappa^2 p`. Block factors are factors of iid.

**Lower bound (`>=`).** Let `eta > 0`, and take a Borel graphing `Phi` generating the orbit relation `R` of `b`, with
cost below `C(b) + eta`.
- Split `Phi` into countably many partial isomorphisms `x -> gamma x` with constant `gamma`. Let `Phi_n` be the first
  `n` of them, with group elements in a finite set `F_n`, and let `R_n` be the relation it generates. Then `R_n`
  increases to `R`.
- Setting `G_x = {{g, h} : (g^{-1} x, h^{-1} x) in Phi_n}` gives an equivariant bond subgraph on `V = Gamma` of
  `Cay(Gamma, F_n)`, with `E deg/2 = cost(Phi_n)`. The points `e` and `s` are joined in `G_x` iff `x R_n s^{-1} x`.
- For each `s` in `S`, `P(x R_n s^{-1} x) -> 1`. Each joining path is finite, so choosing `n` and then a window `W`
  large makes `delta_W` as small as desired. In that case `E deg/2 - 1 + 2 delta_W/kappa^2 <= C(b) - 1 + 2 eta`.
- Each edge indicator of `G` is a Borel function of the iid labels. Approximating the finitely many indicators at
  `e` in `L^1` by finite-range functions of finitely many finite-alphabet labels changes `E deg` and the cylinder
  probability `delta_W` arbitrarily little, by a union bound over the finitely many coordinates in `W`. Rational
  weights can be arranged at the same stage.

## 4. Corollary 4

- For a block rule with rational weights on finitely many labels, `E deg` and `delta_W` are finite sums over
  labelings of a finite ball. Solvable word problem computes the ball, so these are exact rationals.
- Replacing `kappa` by a rational `kappa_0 <= kappa` keeps every bound valid, and the lower-bound construction
  still drives `delta_W` to `0`. So `C(b_Gamma) = 1 + inf` over a computably enumerable family of rationals.
- Fixed price one: `C(b) = 1` together with [AW] and `C >= 1` gives fixed price one. Conversely, fixed price one gives
  `C(b) = 1`.
- The degree-and-connection reformulation follows from the lower-bound construction, which gives `E deg/2 < 1 + eta/2`
  and `delta_W < kappa^2 eta/4` separately. The upper bound handles the reverse direction.

## 5. Scope

- The theorem gives no certificate for any particular group. Producing block rules with value near `0` is exactly
  the open core.
- It gives neither the countable-group passage nor anything for groups without property (T).
- Novelty caveat: the Kazhdan projection step is standard in subrelation rigidity. The contributions here are the
  quantitative cost inequality, the window-local converse, and the resulting right-c.e. formula; they were not found
  in the graph or in the sources read.
