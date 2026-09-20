---
rg: 2
id: set-indexed-repetition-obeys-the-base-sdp-bound-on-keyed-hosts
kind: claim
title: A public key kills anonymity -- for every key kappa on the vertices, val(G_tag^{{n}}) >= opt(G^n) - n*cut(kappa) - C(n,2)*collision(kappa) for every tag count M, so on NO hosts of key cost at most zeta the set-indexed (tagged or not) route to sqrt-scale UG or UGC is decided by the base SDPs once Gamma > zeta + C_+ sqrt(1.5 eta_Sigma ln K); tags act only through underlying vertex collisions, and the survivor must use NO hosts that no partition into pieces of measure about (eta/eps')^2 cuts below eta/eps'
distinct_from:
  set-indexed-repetition-escapes-the-base-sdp-bound: that shows no UNIVERSAL base-SDP bound holds for set-indexed repetition (tagged odd cycle, n >> m) and kills universal set bounds via disjoint copies; this proves an INSTANCE-LEVEL base-SDP bound for every game with a cheap key, which contains both of its examples as the two extremes of one invariant (key cost), and kills the anonymity-certified survivor it left open on all keyed hosts.
  correlated-products-cannot-substitute-rounds-for-alphabet: that kills mu-products, where the players share the coordinate order; set-indexed repetition is not a mu-product (the coordinate order is hidden), and this reduces it to G^n at the price of the key cost, then applies Theorem CP (b) there.
  black-box-repetition-needs-sqrt-scale-soundness-gap: that is a universal-bound kill for ordered repetition; this is a per-instance kill for set-indexed repetition, independent of how soundness is argued.
  parallel-repetition-cannot-substitute-rounds-for-alphabet: that is the ordered-repetition (S1) kill; this transfers its conclusion to set-indexed and tagged repetition on keyed hosts only, and shows it cannot transfer further (key cost is the exact obstruction).
  sqrt-scale-unique-games-hardness: that is the open target; this closes one route class toward it and records the remaining prerequisite, it does not decide the target.
artifacts:
  - experiments/ugc-keyed-set-repetition-2026-09-17/check_keyed_set_repetition.py
  - experiments/ugc-keyed-set-repetition-2026-09-17/output.txt
---

**ESTABLISHED.** Route: `set-indexed-repetition-keyed-hosts-proof`.
Theorem K, Proposition T and Lemma C are elementary and self-contained. The
decision theorem imports Theorem CP (b) of
`correlated-products-cannot-substitute-rounds-for-alphabet` (at `µ = w^(⊗n)`)
and fixed-precision SDP solving (`sdp-fixed-precision-solvable-gls`).

## Setting

- `G` is a bipartite unique game: left `U`, right `V`, alphabet `[k]`, and
  constraint law `w` on triples `(u, v, π)`. `µ_A` and `µ_B` are the laws of
  `u` and `v`. `opt(G^n)` is the ordered `n`-fold repeated value.
- `G^{{n}}` is the set-indexed repetition of
  `set-indexed-repetition-escapes-the-base-sdp-bound`. Sample `n` iid edges and
  condition on `Good` (distinct `u_j` and distinct `v_j`). Alice gets
  `A = {u_j}`, Bob gets `B = {v_j}`, and the matching is hidden.
- `G_{tag,M}` is the tagged blow-up. Its vertices are `(u, a)` and `(v, b)`,
  with tags `a, b` uniform in `[M]`, independent of each other and of the edge.
- A **key** is any map `κ : U ⊔ V → [R]`, in other words a partition of the
  vertices. Its **cut** is `θ(κ) := Pr_(e~w)[κ(u) ≠ κ(v)]`. Its **collision**
  is `q_A(κ) := Σ_r µ_A(κ^(-1)(r))^2`.
- The **key cost** of `G` at `n` is
  `z_n(G) := min_κ [ n θ(κ) + C(n,2) q_A(κ) ]`.
- The **collision mass** is
  `c_n(G) := C(n,2) (Σ_u µ_A(u)^2 + Σ_v µ_B(v)^2)`.
- `C_+ = 2 sqrt(2 C_3)`, where `C_3` is the constant of (H1) in
  `steurer-hellinger-relaxation-rounding`.

## Statements

**Theorem K (a public key simulates the ordered game).** For every bipartite
unique game `G`, every `n >= 1`, every `M >= 1` and every key `κ`,

```text
val(G_{tag,M}^{{n}}),  val(G^{{n}})   >=   opt(G^n)  -  n θ(κ)  -  C(n,2) q_A(κ).
```

Hence both values are at least `opt(G^n) - z_n(G)`, uniformly in `M`. The
simulating strategy uses no tags. Each player sorts their set by key. On the
event that the keys of `A` are distinct and no edge is cut, the two sorted
lists correspond under the hidden matching. The players then apply a shared
uniform permutation, which makes the reordered edge tuple exactly iid, and
play an optimal strategy of `G^n` on it.

**Corollary K (base-SDP bound on keyed hosts).** With `k` the alphabet of `G`,

```text
val(G_{tag,M}^{{n}})  >=  1  -  C_+ sqrt( n ln k (1 - sdp(G)) )  -  z_n(G).
```

**Proposition T (tags act only through collisions).** For every `G`, `n` and
`M`,

```text
val(G_{tag,M}^{{n}})  >=  val(G^{{n}})  -  c_n(G).
```

**Theorem D (decision on keyed NO hosts).** A *set-indexed route* is a
polynomial-time map `x ↦ (G_x, n_x, M_x)`, with `n_x, M_x` in binary, that
outputs `G_{x,tag,M_x}^{{n_x}}` (with `M_x = 1` meaning untagged). Suppose:

- **union-bound completeness:** `x ∈ Y ⇒ n_x (1 - opt(G_x)) <= η_Σ`;
- **soundness:** `x ∈ N ⇒ val(output) <= 1 - Γ`;
- **keyed NO hosts:** `x ∈ N ⇒ z_(n_x)(G_x) <= ζ`;
- **gap:** `Γ > ζ + C_+ sqrt(1.5 η_Σ ln K)`, where `K >= k_x` for all `x`.

Then the source promise problem is in `P`. It is decided by the base SDP
alone. Compute `sdp(G_x)` to precision `η_Σ/(4 n_x)` and accept iff
`n_x (1 - s~) <= 1.25 η_Σ`. The key never needs to be known or computed, and
the soundness argument is irrelevant.

**Corollary D (ratio ceiling, unless P = NP).** For an NP-hard source on keyed
NO hosts,

```text
Γ  <=  ζ + C_+ sqrt(1.5 η_Σ ln K).
```

- **UGC form.** For target `Gap-UG[1 - ε', δ']` with `η_Σ <= 2 ε'` (the
  product certificate of the w21 node), the route needs
  `ln K >= (1 - δ' - ζ)^2 / (24 C_3 ε')`. So a set-indexed route from a
  fixed-alphabet source dies on keyed NO hosts, exactly as the ordered
  (`correlated-products-...`, Corollary CP 2) and universal-bound
  (`set-indexed-...`, (B)) routes do.
- **Tagging is inert.** Because `z_n(G_tag) <= z_n(G)` (tag-blind keys), tagged
  and untagged outputs of the same host die together.

**Lemma C (the odd cycle is keyless, consistently with (A)).** For the odd
cycle `C_m` of the w21 node and every `n >= 2`,

```text
z_n(C_m)  >=  min( n^2/4 ,  n^(3/2) / (2 sqrt m) ).
```

Hence `z_n(C_m) >= 1` once `n^3 >= 4m`. So Theorem K is vacuous on the odd
cycle for all `n >= (4m)^(1/3)`. That range contains the regime `n >> m` where
part (A) of `set-indexed-repetition-escapes-the-base-sdp-bound` shows the set
value collapses, so the two results are consistent.

Conversely, `M` disjoint copies with key = copy index have `θ = 0` and
`q_A = 1/M`. So Theorem K gives `val >= opt(G^n) - n^2/(2M)`, which
recovers the mechanism of (B) (a public order) as `M -> ∞`.

**Lemma S (keyed hosts have non-expanding small sets).** If `z_n(G) <= ζ`, with
`n >= 2`, then some vertex set `S` with `µ_A(S) <= 4ζ/C(n,2)` has
`Φ(S) := Pr_e[v ∉ S | u ∈ S] <= 4ζ/n`. More precisely, the parts of the
optimal key with this property carry at least half of the `µ_A`-mass.
Contrapositive: a host in which every set of `µ_A`-measure at most
`δ_0 = 4ζ/C(n,2)` has expansion above `4ζ/n` (about `sqrt(2ζ δ_0)`) is
keyless at `n`.

## Class kill (impact type 3)

- **Class.** Set-indexed routes, tagged or not, whose NO hosts `G_x` have key
  cost `z_(n_x)(G_x) <= ζ < Γ - C_+ sqrt(1.5 η_Σ ln K)`. This is any NO host
  that can be cut, along a vertex partition, into pieces of collision mass
  `<= ζ/C(n,2)` at total edge cost `<= ζ/n`.
  - Examples include every disjoint union of at least `n^2/ζ` equal pieces.
  - Also included is every long cycle or path of length `L` cut into
    `sqrt(nL)` arcs, with cost `O(n^(3/2)/sqrt L)`, so any `L >> n^3`.
  - Also included are noisy-cube hosts at `2 ε' log2(ε'/η) << 1 - δ'` (by
    subcube keys, table [5] of the check).
- **Invariant.** The invariant is the key cost `n θ + C(n,2) q_A`. It is a
  property of the base host alone, blind to tags and to the soundness
  argument.
- **Where every member dies.** Every member dies at the soundness step.
  - Theorem K bounds the set value below by the ordered value `opt(G^n)`, at
    additive price `z_n`.
  - Theorem CP (b) then forces `n(1 - sdp(G_x)) > 1.5 η_Σ` on every NO output,
    while YES outputs have `n(1 - sdp) <= η_Σ`.
  - So the base SDP separates them. No property of `G^{{n}}` beyond its host
    is ever used.
- **Tag anonymity is not an independent resource.** By Proposition T, tagging
  changes the set value by at most the underlying collision mass
  `c_n(G) = C(n,2)(||µ_A||^2 + ||µ_B||^2)`. The tagged-odd-cycle mechanism of
  the w21 node (anonymity of Bob's tags at one position) lives entirely in
  repeated underlying vertices, which have mass `c_n(C_m) = n(n-1)/m` there. So:
  - on *light* hosts (`c_n <= ζ`), a tagged route is the untagged route on the
    same host, up to `ζ`;
  - on *heavy* hosts (`c_n > ζ`), the effective support
    `1/(||µ_A||^2 + ||µ_B||^2)` is below `C(n,2)/ζ`. Such a host is a bounded
    core at the scale `n ~ ε'/η`.

## Consequence for `sqrt-scale-unique-games-hardness` (impact type 2)

The w21 survivor was "anonymity-certified tagged-set soundness"
`val(G) <= 1 - γ ⇒ val(G_tag^{{n}}) <= δ'`, at `n ~ ε'/η` and
`γ = o(sqrt η)`. It now splits into two prerequisites, each able to fail on
its own:

- **(P1) Keyless NO hosts.** The hard NO instances `G` of the source must have
  `z_n(G) > 1 - δ' - C_+ sqrt(3 ε' ln k)` at `n ~ ε'/η`. By Lemma S this holds
  whenever pieces of measure `(η/ε')^2` expand by more than about `η/ε'` (a
  small-set-expansion condition). It is necessary, because Theorem D applies
  on keyed NO hosts.
  - On noisy-cube hosts, subcube keys show that (P1) needs
    `log2(ε'/η) >~ (1 - δ')/(2 ε')`, that is `η <= ε' 2^(-Ω(1/ε'))`.
  - At `η = poly(ε')` it therefore fails on such hosts. This is a quantitative
    link between the route and the small-set-expansion side of UGC.
- **(P2) Set soundness on keyless hosts.** `val(G^{{n}}) <= δ'` for the (P1)
  NO hosts, using expansion rather than tags. Tags can be dropped from the
  route (Proposition T), except on heavy cores.

**What is dead.** The tagged-blow-up mechanism as a means of creating
anonymity is dead on light hosts. Any set-indexed route whose NO hosts admit a
cheap key is dead unless `P = NP`, whatever its soundness proof.

**What is not claimed.** This does not show that (P1) or (P2) fails. It does
not bound `val(G^{{n}})` from above on keyless hosts, and it does not show that
noisy-cube hosts are keyless at small `η` (subcube keys are only one family).
Completeness better than the union bound is not covered, as in Theorem CP.

## Checks

`experiments/ugc-keyed-set-repetition-2026-09-17/check_keyed_set_repetition.py`
(output `output.txt`) checks the following, all in exact rationals:

1. For `n = 2` on four games (3+3 vertices, `k = 2`) and all 203 keys: exact
   `opt(G^2)`, exact `val(G^{{2}})`, and exact analysis of the key simulation.
   It confirms:
   - the reordered tuple has law exactly `w^(⊗2)`;
   - set win equals ordered win on `E`;
   - `E ⊂ Good`;
   - `Pr[not E] <= nθ + C(n,2) q_A`;
   - `val >= sim >= opt - cost`.
2. The same checks on tagged blow-ups (`M = 2`), with tag-blind keys.
3. `n = 3`, tagged, with random ordered strategies. Exchangeability and the
   simulation identity again hold exactly.
4. The exact key cost of the w21 odd-cycle hosts `C_3` and `C_5` (weights
   `1/2, 1/4, 1/4`) over all vertex partitions, against Lemma C.
5. The subcube key costs on noisy-cube hosts.

DERIVATION set-indexed-repetition-keyed-hosts-proof
