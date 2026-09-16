---
rg: 2
id: profinite-diagonal-transfer-limit-proof
kind: route
title: Level-j clopens of the diagonal extension are the induced action from N_j, and stabilized closures turn every transfer into multiplication by the index
target: profinite-diagonal-cantor-type-is-transfer-limit
requires: [induced-cantor-action-type-semigroup-matches-subgroup]
---

Notation as in the target.  `pi_j : K -> Gamma/N_j` is the quotient map, and
`[s] = pi_j^(-1)(s)`.  Types are classes of clopens in `X x N` (finitely many
levels), moved by group elements and with levels permuted.

**1. Cantor and free.**  `K` is compact, metrizable and totally disconnected.
It is infinite because `Gamma` is infinite and embeds in `K` (the kernel of
`Gamma -> K` is the intersection of the `N_j`).  So `K` has no isolated points
and `Y` is a Cantor space.  If `gamma (x, k) = (x, k)` then `gamma k = k` in
the group `K`, so `gamma` maps to `e`, so `gamma = e`.

**Level algebras.**  Let `B_j` be the set of clopens
`⊔_(s in Gamma/N_j) A_s x [s]` with `A_s` clopen in `X`.  Then `B_j` is a
`Gamma`-invariant subalgebra, `B_j ⊆ B_(j+1)`, and every clopen of `Y` is a
finite union of rectangles `A x [s]`, so it lies in some `B_j`.
`B_j` is `Clopen(X x Gamma/N_j)` with the diagonal action.  The map
`[g, x] -> (g x, g N_j)` is a well-defined equivariant homeomorphism
`Gamma x_(N_j) X -> X x Gamma/N_j`.  Its inverse is `(y, g N_j) -> [g, g^(-1) y]`,
and it sends `{e} x A` to `A x [N_j]`.

**2. Minimality.**  Suppose every `N_j` is minimal.  A nonempty clopen of `Y`
contains some `A x [g N_j]` with `A` nonempty.  Translating by `g^(-1)` gives
`A' x [N_j]`, and finitely many `n_i in N_j` have `⋃ n_i A' = X`.  So
`⋃ n_i (A' x [N_j]) = X x [N_j]`, and translating by coset representatives of
`Gamma/N_j` covers `Y`.  Conversely, let `Z ⊊ X` be nonempty, closed and
`N_j`-invariant.  For `s = g N_j` the set `g Z` depends only on `s`, since
`n Z = Z` for `n in N_j`.  Then `W = ⋃_s g_s Z x [s]` is closed, nonempty and
`Gamma`-invariant, and it misses `(X \ Z) x [N_j]`.

**3. Measures.**  The projection `Y -> X` pushes an invariant probability
forward.  Conversely, for an invariant probability `m` on `X` and Haar
measure `h` on `K`, `m x h` is invariant because `h` is translation-invariant.

**4. Transfer limit.**  An equidecomposition between clopens of `Y x N` uses
finitely many pieces, all in some `B_i`.  So `S(Y, Gamma)` is the direct
limit of the level semigroups `S_j = S(X x Gamma/N_j, Gamma)`, along the maps
induced by `B_j ⊆ B_(j+1)`.  By `induced-cantor-action-type-semigroup-matches-subgroup`
and the homeomorphism above, `[A] -> [A x [N_j]]` is an isomorphism
`S(X, N_j) -> S_j`.  In `B_(j+1)`,
`A x [N_j] = ⊔_(t in N_j/N_(j+1)) A x [t N_(j+1)]` and
`A x [t N_(j+1)] = t (t^(-1) A x [N_(j+1)])`.  So the connecting map is
`rho_j [A] = sum_t [t^(-1) A]`.  Changing `t` to `t n` with `n in N_(j+1)`
does not change `[t^(-1) A]`.  At stage `j`,
`1_Y = ⊔_s X x [s] = ⊔_s g_s (X x [N_j])`, so `[1_Y] = [Gamma : N_j][1_X]`.

**5. Invariant measures.**  Given `nu`, set `mu_j(A) = nu(A x [N_j])`.  It is
`N_j`-invariant since `n (A x [N_j]) = n A x [N_j]`, and the splitting in step 4
gives `mu_j(A) = sum_t mu_(j+1)(t^(-1) A)`.  Invariance of `nu` gives
`nu(A x [g N_j]) = nu(g^(-1) A x [N_j]) = mu_j(g^(-1) A)`.  Conversely, given a
chain, the formula is independent of the representative `g` by
`N_j`-invariance.  It is consistent between levels by the chain identity, and
additive on each `B_j`.  It is invariant because
`gamma (A x [g N_j]) = gamma A x [gamma g N_j]`.  The two constructions are
inverse to each other.

**6. Firewall.**  Let `C_j` be the closure of `N_j` in `Homeo(X)`, and suppose
`C_j = C` for `j >= j_0`.  For a clopen `D` and `gamma in Homeo(X)` the set
`{h : h(D) = gamma D} = {h : h(D) ⊆ gamma D, h(X \ D) ⊆ X \ gamma D}` is open
in the compact-open topology and contains `gamma`.
* For `j >= j_0`, every piece `D -> gamma D` of an `N_(j_0)`-equidecomposition
  can be realized by some `n in N_j` with `n D = gamma D`, since
  `gamma in N_(j_0) ⊆ C` and `C` is the closure of `N_j`.  So the quotient map
  `S(X, N_j) -> S(X, N_(j_0)) =: S` is an isomorphism.
* For `j >= j_0`, each `t^(-1)` with `t in N_j ⊆ C` agrees with some
  `n in N_(j+1)` on `A` (same reason, as `C = C_(j+1)`), so
  `[t^(-1) A] = [A]` and `rho_j` is multiplication by `d_j = [N_j : N_(j+1)]`.
* Infinitely many `d_j` are at least 2, since the intersection of the `N_j`
  is trivial and `Gamma` is infinite.

Suppose `(n+1) x <= n y` in the limit, with `n >= 1`.  Represent `x` and `y`
at a stage `i >= j_0` where the inequality already holds in `S`.  Choose a
later stage `i'` with `P = d_i ... d_(i'-1) >= n^2`, and write
`k = floor(P/n) >= n`.  Then `k n <= P <= k(n+1)`, so in `S`
`P x <= k(n+1) x <= k n y <= P y`.  This inequality is `x <= y` at stage `i'`.
So `S(Y, Gamma)` is almost unperforated.

If some `C_j` differs from `C_(j+1)`, then `C_(j+1)` is a closed normal
subgroup of finite index in `C_j`, so it is open.  Stabilization fails only if
this happens infinitely often.
