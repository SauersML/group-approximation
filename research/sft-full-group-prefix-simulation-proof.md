---
rg: 2
id: sft-full-group-prefix-simulation-proof
kind: route
title: Elements are canonical prefix replacements, so a word acts on each deep cylinder by one replacement that can be computed and compared
target: sft-topological-full-groups-have-exponential-word-problem
requires: []
artifacts:
  - research/artifacts/hl-bh-groupoid-embedding-2026-09-13.md
---

Notation follows Matui, arXiv:1210.5800, Section 6.1, quoted in the artifact:
admissible words `mu` over the edge set `E`, cylinders `C_mu`, terminal vertex
`t(mu)`, and for `t(mu) = t(nu)` the compact open `G`-sets
`U_(mu,nu) = {(x, |mu|-|nu|, y) : sigma^|mu| x = sigma^|nu| y, x in C_mu, y in C_nu}`,
which form a base of the topology of `G` (Matui l.1783–1789).

## 1. Elements are finite tables of canonical similarities

Let `alpha = pi_W` in `[[G|Y]]`, with `W` a compact open `G`-set.

- The sets `U_(mu,nu)` form a base, so compactness gives finitely many
  `U_(mu_i,nu_i) ⊆ W` whose union is `W`.
- Cylinders are nested or disjoint. If `C_(mu_i) ⊆ C_(mu_j)`, then
  `U_(mu_i,nu_i)` and the part of `U_(mu_j,nu_j)` over `C_(mu_i)` are both
  sub-bisections of `W` with the same range set, so they coincide. Keeping only
  the maximal cylinders therefore gives a disjoint decomposition
  `W = U_(mu_1,nu_1) ⊔ ... ⊔ U_(mu_k,nu_k)`.
- On `C_(mu_i)` the map is the canonical similarity `mu_i zeta -> nu_i zeta`
  (it reads a point of `U_(mu_i,nu_i)` from its range coordinate to its source
  coordinate, or the reverse, depending on the convention for `pi_W`; the
  argument below is symmetric).
- The `C_(mu_i)` partition the domain and the `C_(nu_i)` partition the range.

Matui writes the same decomposition at the start of his proof of Theorem
"Haagerup" (l.2113 onward). Fix such a table for every `s in S` and let `L`
bound the lengths of all `mu_i`, `nu_i` appearing. Also let `Y` be a union of
cylinders of length at most `L`.

## 2. A word acts on each deep cylinder by one replacement

For an admissible word `eta` with `C_eta ⊆ Y` and `|eta| >= L`, and `s in S`,
define `s(eta)` as follows: `eta = mu_i eta'` for the unique `i` with
`C_eta ⊆ C_(mu_i)` (it exists because `|eta| >= |mu_i|` and the cylinders
partition), and `s(eta) = nu_i eta'`. Then `s(eta zeta) = s(eta) zeta` for every
admissible `zeta` from `t(eta)`, `t(s(eta)) = t(eta)`, and
`|s(eta)| >= |eta| - L`.

Let `w = s_n ... s_1` and `|eta| = n*L`. Before step `j+1` (for `j <= n-1`) the
current word has length at least `n*L - j*L >= L`, so all `n` steps are defined.
The result `w(eta)` satisfies `w(eta zeta) = w(eta) zeta` for all admissible
`zeta` from `t(eta)`.

## 3. The equality test

Claim: `w` is the identity if and only if `w(eta) = eta` for every admissible
`eta` of length `n*L` with `C_eta ⊆ Y`.

- If `w(eta) = eta` for all such `eta`, then `w` fixes every cylinder pointwise,
  and these cylinders cover `Y`.
- Suppose `w(eta) != eta`.
  - If the two words differ at some position `p <= min(|w(eta)|, |eta|)`, every
    point of `C_eta` is moved.
  - Otherwise one is a proper prefix of the other, say `w(eta) = eta rho` with
    `rho` nonempty (the other case is the same for `w^-1`, whose values are
    computed the same way). Then `w(eta zeta) = eta zeta` would force
    `rho zeta = zeta` for every `zeta in C_(t(eta))`, so every such `zeta` equals
    the periodic point `rho rho rho ...`. That contradicts `X` having no isolated
    points, since `C_(t(eta))` is a nonempty clopen set.

## 4. The running time

There are at most `|E|^(n*L)` admissible words of length `n*L`. For each, the
simulation takes `n` steps, each a table lookup and a rewrite of a word of
length `O(n*L)`, so `O(n^2)` time up to constants depending on the tables. The
total is at most `C*2^(C*n)` for a constant `C` depending only on the graph,
`S` and the tables. That is the stated bound.
