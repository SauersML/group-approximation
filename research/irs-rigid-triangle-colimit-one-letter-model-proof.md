---
rg: 2
id: irs-rigid-triangle-colimit-one-letter-model-proof
kind: route
title: Round each vertex chart, pad to free, align two edges by conjugation, and feed the exact model to the free-or-trivial soficity test
target: irs-rigid-triangle-colimit-sofic-iff-one-letter-model
requires:
  - almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial
---

Notation as in the claim. `d_H(sigma, tau) = |{p : sigma p != tau p}|/d` on `Sym(d)`, and
`supp pi = {p : pi p != p}`. The required claim is used only in step (c) => (a), through its
Consequence 2. Every other step is self-contained.

## Elementary facts

- (F1) `d_H` is invariant under left and right multiplication, and
  `d_H(sigma tau, 1) <= d_H(sigma, 1) + d_H(tau, 1)`. Hence
  `d_H(u sigma u^(-1), 1) = d_H(sigma, 1)`.
- (F2) For permutations `pi, psi` of `[d]`: `d_H(pi psi pi^(-1), psi) <= 2|supp pi|/d`.
  Indeed `pi psi pi^(-1) p = psi p` whenever `p notin supp pi` and `psi p notin supp pi`, and
  the remaining points lie in `supp pi` or in `psi^(-1)(supp pi)`.

## Lemma A (rounding an almost action of a finite group)

Let `H` be finite and `sigma : H -> Sym(d)` a map with `d_H(sigma(gh), sigma(g) sigma(h)) <= delta`
for all `g, h` and `d_H(sigma(e), 1) <= delta`. Then there is a homomorphism `rho : H -> Sym(d)`
with `d_H(rho(g), sigma(g)) <= (|H| + 1)(|H|^2 + 1) delta` for every `g`.

*Proof.* Let `X_0` be the set of `x` with `sigma(e) x = x` and
`sigma(gh) x = sigma(g) sigma(h) x` for all `g, h`. Then `|[d] \ X_0| <= (|H|^2 + 1) delta d`.
Let `X_1 = {x in X_0 : sigma(k) x in X_0 for all k}`. A point outside `X_1` is outside `X_0`
or in some `sigma(k)^(-1)([d] \ X_0)`, so `|[d] \ X_1| <= (|H| + 1)|[d] \ X_0|`.

Fix `x in X_1` and put `O(x) = {sigma(k) x : k in H}`. For `y = sigma(k) x`:
`sigma(g) y = sigma(gk) x in O(x)`, `sigma(g) sigma(h) y = sigma(g) sigma(hk) x = sigma(ghk) x
= sigma(gh) y`, and `sigma(e) y = sigma(ek) x = y`. Each equality uses only `x in X_0`. So every
`sigma(g)` maps `O(x)` injectively into itself, hence bijectively, and `sigma` is an action on
`O(x)`. Let `Y` be the union of the `O(x)`, `x in X_1`. Define `rho(g) = sigma(g)` on `Y` and the
identity off `Y`. Each `rho(g)` is a permutation, `rho` is a homomorphism, and `rho(g)` differs
from `sigma(g)` only off `Y`, which lies in `[d] \ X_1`. QED

## Lemma B (aligning two free actions)

Let `H` be finite, and `alpha, beta : H -> Sym(Omega)` free actions on a finite set. Put
`D = {p : alpha(h) p != beta(h) p for some h}`. Then:
- `Omega \ D` is invariant under `alpha(H)` and `beta(H)`, and the two actions agree on it;
- there is `pi in Sym(Omega)` with `supp pi` contained in `D` and
  `pi alpha(h) pi^(-1) = beta(h)` for all `h`;
- `|D| <= sum_h d_H(alpha(h), beta(h)) |Omega| <= |H| max_h d_H(alpha(h), beta(h)) |Omega|`.

*Proof.* Let `p notin D`, `h in H` and `q = alpha(h) p = beta(h) p`. For every `k`,
`alpha(k) q = alpha(kh) p = beta(kh) p = beta(k) q`, so `q notin D`. Hence `alpha(h)` maps
`Omega \ D` into itself, so onto itself, and it agrees there with `beta(h)`. So `D` is invariant
under both actions, and both restrict to free actions on `D`. Each is a disjoint union of
`|D|/|H|` regular orbits. Choose representatives `p_1, ..., p_m` of the `alpha`-orbits and
`q_1, ..., q_m` of the `beta`-orbits in `D`. Set `pi(alpha(h) p_j) = beta(h) q_j`, and `pi = id`
off `D`. Then `pi` is a bijection. On `D`,
`pi alpha(k) alpha(h) p_j = beta(kh) q_j = beta(k) pi alpha(h) p_j`. Off `D`,
`pi alpha(k) = alpha(k) = beta(k) = beta(k) pi`. The size bound is a union bound over `h`. QED

## Lemma C (padding to free)

Let `rho_ij : X_ij -> Sym(d)` be homomorphisms, `NF_ij` the set of points with nontrivial
`rho_ij`-stabilizer, and `N = lcm(|X_12|, |X_13|, |X_23|)`. There are `d'` with
`d <= d' < d + N` and free homomorphisms `rho'_ij : X_ij -> Sym(d')` with `rho'_ij(y) p = rho_ij(y) p`
for every `y` and every `p in [d] \ NF_ij`.

*Proof.* `NF_ij` is invariant, since stabilizers along an orbit are conjugate, and its
complement is a free `X_ij`-set. So `|NF_ij| = d mod |X_ij|`. Choose `d' = 0 mod N` in
`[d, d + N)` and put `P = [d'] \ [d]`. Then `|NF_ij u P| = 0 mod |X_ij|`. Identify `NF_ij u P`
with `X_ij x [m]`, let `X_ij` act there by left multiplication, and keep `rho_ij` on
`[d] \ NF_ij`. QED

Consequently, for an edge group `X_e` shared by `X_ij` and `X_ik`, and `x in X_e`,

```text
d' d_H(rho'_ij(iota_ij x), rho'_ik(iota_ik x)) <= d d_H(rho_ij(iota_ij x), rho_ik(iota_ik x)) + |NF_ij| + |NF_ik| + N.   (C1)
```

## (a) => (b)

Let `sigma_n : S -> Sym(d_n)` be a sofic approximation:
`d_H(sigma_n(gh), sigma_n(g) sigma_n(h)) -> 0` for all `g, h`, and
`d_H(sigma_n(g), sigma_n(h)) -> 1` for `g != h`. Then
`d_H(sigma_n(1), 1) = d_H(sigma_n(1) sigma_n(1), sigma_n(1)) -> 0`, so
`d_H(sigma_n(g), 1) -> 1` for `g != 1`. Replacing `sigma_n` by `n` disjoint copies of itself
changes none of these quantities, so we may assume `d_n -> infinity`.

Fix `epsilon > 0`, and identify each `X_ij` with its image in `S`, by (S3). Let `m = max |X_ij|`,
`C = (m + 1)(m^2 + 1)`, and choose `n` with the multiplicativity defects on `X_ij x X_ij` and
`d_H(sigma_n(1), 1)` at most `delta`, and `d_H(sigma_n(g), 1) >= 1 - delta` for every nontrivial
`g` in the three vertex groups. Lemma A applied to `sigma_n` restricted to `X_ij` gives
homomorphisms `rho_ij` with `d_H(rho_ij(y), sigma_n(y)) <= C delta`.
- *Almost free.* For `1 != y in X_ij`, `|Fix rho_ij(y)| <= (1 + C) delta d_n`. So
  `|NF_ij| <= m (1 + C) delta d_n`.
- *Almost glued.* For `x` in an edge group, `iota_ij(x)` and `iota_ik(x)` have the same image in
  `S`, so `sigma_n` takes one value on them and
  `d_H(rho_ij(iota_ij x), rho_ik(iota_ik x)) <= 2 C delta`.

Lemma C and (C1) give free homomorphisms on `[d']` with every edge mismatch at most
`2C delta + 2m(1 + C) delta + N/d_n`. This is at most `epsilon` for `delta` small and `n`
large.

## (b) => (c)

Let the `rho_ij` be free, with every edge mismatch at most `epsilon`. Restrictions of free
actions to subgroups are free.
1. Apply Lemma B to `H = X_1`, `alpha = rho_13 o iota_13` and `beta = rho_12 o iota_12`.
   - This gives `pi_1` with `|supp pi_1| <= |X_1| epsilon d`.
   - Put `rho'_13 = pi_1 rho_13(.) pi_1^(-1)`. It is free, and it agrees exactly with `rho_12` on
     `X_1`.
   - By (F2) it is within `2|X_1| epsilon` of `rho_13`. So the edge-3 mismatch is now at most
     `epsilon_3 = (1 + 2|X_1|) epsilon`, and edge 2 is unchanged.
2. Apply Lemma B to `H = X_3`, `alpha = rho_23 o iota_23` and `beta = rho'_13 o iota_13`.
   - This gives `pi_3` with `|supp pi_3| <= |X_3| epsilon_3 d`.
   - Put `rho'_23 = pi_3 rho_23(.) pi_3^(-1)`. Edge 3 is now exact, and edge 1 does not involve
     `X_23`.
   - By (F2) the edge-2 mismatch is at most `epsilon_2 = epsilon + 2|X_3| epsilon_3`.
3. By the union bound of Lemma B, `|D| <= |X_2| epsilon_2 d`.

## (c) => (a)

Let `epsilon_n -> 0` and let `(rho^n_ij)` be `epsilon_n`-models on `[d_n]`, `d_n >= 1`.
- *Presentation.* Let `A = X_12 u X_13 u X_23`, a disjoint union of finite sets. Let `R` consist
  of the multiplication-table words `a b c^(-1)`, with `a, b, c` in one `X_ij` and `ab = c`
  there, together with the edge words `iota_ij(x) iota_ik(x)^(-1)`. Then `F(A)/<<R>>` is the free
  product of the `X_ij` modulo the edge identifications, that is `S`. Let `N` be the kernel.
- *The almost actions.* Define `sigma_n : F(A) -> Sym(d_n)` on letters by `sigma_n(a) = rho^n_ij(a)`
  for `a in X_ij`. The multiplication words and the edge words of `X_1` and `X_3` map to `1`
  exactly. An edge word of `X_2` maps to `rho_12(iota_12 x) rho_23(iota_23 x)^(-1)`, which moves
  only points of `rho_23(iota_23 x)(D)`, so its defect is at most `epsilon_n`.
- *(AF1).* Every `w in N` is a product of `m(w)` conjugates of words of `R` and their inverses,
  so by (F1) `d_H(sigma_n(w), 1) <= m(w) epsilon_n -> 0`.
- *Fixed points.* By (S1), `S` is nontrivial, so some `X_ij` is nontrivial. Let `1 != y` be in
  it. `Fix_n` lies in `Fix rho^n_ij(y)`, which is empty by (M1).
- *Conclusion.* Consequence 2 of `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`,
  whose hypotheses are (S1), (S2) and finite generation by `A`, gives that `S` is sofic.

(c) => (b) is immediate: an `epsilon`-model has every edge mismatch at most `epsilon`.

## (c) <=> (d)

*`K/<<t>> = S`.* Killing `t` turns the HNN relations into `iota_12(x) = iota_23(x)` for
`x in X_2`. The amalgam `K_0` is the free product modulo the `X_1`- and `X_3`-identifications,
so `K/<<t>> = S`.

*(c) => (d).* By (M2) and the universal property of amalgamated products, the `rho_ij` define an
action `rho_0` of `K_0`. Lemma B with `H = X_2`, `alpha = rho_12 o iota_12` and
`beta = rho_23 o iota_23` has exactly the set `D` as its disagreement set. It gives `tau` with
`supp tau` contained in `D` and `tau alpha(x) tau^(-1) = beta(x)`. Setting `rho(t) = tau`
satisfies the HNN relations, and `|supp tau| <= epsilon d`.

*(d) => (c).* Restrict `rho` to `K_0` to get the `rho_ij`, which satisfy (M2). For `x in X_2`,
`rho_23(iota_23 x) = tau rho_12(iota_12 x) tau^(-1)` with `tau = rho(t)`. These agree at `p` unless
`p in supp tau` or `rho_12(iota_12 x) p in supp tau`. So `D` lies in the union over `x` of
`rho_12(iota_12 x)^(-1)(supp tau)`, and `|D| <= |X_2| epsilon d`.

## (c) <=> (e)

*(c) => (e).* Let `C_1, ..., C_r` be the `rho_0(K_0)`-orbits. Since
`sum_j |D n C_j| = |D| <= epsilon sum_j |C_j|`, some `j` has `|D n C_j| <= epsilon |C_j|`.
- Pick `p in C_j` and let `M` be its stabilizer. Then `kM -> rho_0(k) p` identifies `K_0/M` with
  `C_j`, `K_0` acting by left multiplication.
- The stabilizer of `kM` in `X_ij` is `X_ij n kMk^(-1)`. The vertex groups embed in `K_0`, as the
  factors of an amalgam along injections do. So freeness of the restricted actions says exactly
  that `M` meets every conjugate of every vertex group trivially.
- The left actions of `iota_12(x)` and `iota_23(x)` differ at `kM` iff `n_x k M != kM`, that is,
  iff `k^(-1) n_x k notin M`.

*(e) => (c).* Take the left action on `K_0/M` with `d = [K_0:M]`. The same two identities give
(M1)-(M3).

## Necessary shape

*(N1).* Let `C` be a `K_0`-orbit with `C n D` empty.
- On `C` the edge-2 identifications hold exactly. So the three restricted actions define a
  homomorphism from `S` onto a subgroup of `Sym(C)`.
- A finite quotient of the infinite simple group `S` is trivial, so every `X_ij` acts trivially
  on `C`.
- The actions are free and `C` is nonempty, so every `X_ij` is trivial. Then `S` is trivial,
  contradicting (S1).

By Lemma B, `D` is invariant under the free action `rho_12 o iota_12` of `X_2`, and so is `C`.
So `D n C` is a nonempty union of free `X_2`-orbits, and `|D n C| >= |X_2|`. The orbit count
follows. In (e), `|X_2| <= epsilon [K_0:M]`.

*(N2).* If `M` is normal in `K_0`, then `k^(-1) n_x k in M` iff `n_x in M`. So the defect set is
empty or everything. Empty is excluded by (N1).

*(N3).* `rho : K -> Q` is onto and maps `<<t>>` onto `<<rho(t)>>`. So `Q/<<rho(t)>>` is a finite
quotient of `K/<<t>> = S`, hence trivial. For `1 != y in X_ij`, `rho(y)` moves every point by
(M1). A product of `m` conjugates of `rho(t)^(+-1)` moves at most `m |supp rho(t)| <= m epsilon d`
points. So `m >= 1/epsilon`. For `rho_0(K_0)` the same argument uses
`K_0/<<n_x : x in X_2>> = S` and `supp rho_0(n_x)`, which lies in `D`.

*(N4).* This is the contrapositive of (a) <=> (d).
