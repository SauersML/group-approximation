---
rg: 2
id: s-arithmetic-affine-rn-groups-are-k-graph-full-groups
kind: claim
title: For K = F_q(t), v = (t) and S = {v, infinity, p_1, ..., p_(k-1)}, the germ groupoid of the affine group of the S-integers with the torsion-free S-units acting on F_q[[t]] is the path groupoid of a one-vertex k-graph; so these Roever-Nekrashevych groups are of type F_infinity, and for q = 2 integrally acyclic and simple
distinct_from:
  rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph: that is the case k = 2, p_1 = t - a (the lamplighter F_q wr Z); this gives every rank k >= 1 and every finite set of places of F_q(t), with a monoid defined by one formula instead of a hand-built pair of edge sets.
  rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp: that proves finite presentability for affine lamplighters; this proves F_infinity and computes the integral homology for a family of every S-rank, whose groups H are non-contracting for k >= 2.
  basilica-rn-group-is-not-a-k-graph-full-group: that gives the obstruction (rational acyclicity of the germ groupoid is necessary); this gives the matching construction, and for number fields locates exactly where the obstruction bites.
  li-finite-k-graph-full-groups-are-f-infinity: that is Li's finiteness theorem; this produces the k-graphs it applies to.
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/s_arithmetic_kgraph.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-s-arithmetic-kgraph.txt
---

**Tiers.** Parts 1–4: **ESTABLISHED** (proof in `s-arithmetic-affine-rn-groups-are-k-graph-full-groups-proof`, lane
proof w12-101, not independently reviewed; machine-checked on five configurations in `s_arithmetic_kgraph.py`,
"ALL OK"; the script takes `q` prime). Imports: Li's `F_∞` theorem (`li-finite-k-graph-full-groups-are-f-infinity`), the FKPS Koszul complex
(`finite-k-graph-boundary-groupoid-standard-facts`), Li's Corollaries C–E (`li-derived-full-group-homology-is-k-theory-cover`).
Part 5 (number fields) is a **SKETCH**: the rational criterion is proved in outline only.

## Setting

- `q` is a prime power, `K = F_q(t)`, `v = (t)`, `O = F_q[[t]]` (the unit ball of `K_v`), with digits `X = F_q`.
- `p_1, ..., p_{k-1}` are distinct monic irreducibles, none equal to `t`, of degrees `d_i`; `k ≥ 1`.
- `S = {v, ∞, p_1, ..., p_{k-1}}`, `R = O_S = F_q[t, 1/t, 1/p_1, ..., 1/p_{k-1}]`.
- `U = ⟨t, p_1, ..., p_{k-1}⟩ ≅ Z^k`: the torsion-free part of `O_S^× = F_q^* × U` (rank `|S| - 1 = k`).
- `H = R_0 ⋊ U_0` with `R_0 = F_q[t][1/(p_1⋯p_{k-1})]` and `U_0 = ⟨p_1, ..., p_{k-1}⟩`, acting on `O` by `x ↦ ux + b`.
  Writing `x = c + ty`, it is self-similar: `h|_c(y) = uy + b'` where `uc + b = c' + tb'`.

## Statement

1. **The monoid.** For `n = (n_∞, n_1, ..., n_{k-1}) ∈ N^k`, put `Q_n = Π p_i^{n_i}` and `m(n) = n_∞ + Σ n_i d_i`, and
   `P_n = {x ↦ (t^{m(n)} x + N)/Q_n : N ∈ F_q[t], deg N < m(n)}`.
   `P = ⊔ P_n` is a submonoid of `Aff(R, U)`, and `d : P → N^k` makes it a **one-vertex `k`-graph `Λ`** (unique
   factorisation). There are `q` edges of colour `∞` (the digit maps `x ↦ c + tx`), and `q^{d_i}` of colour `p_i`
   (`x ↦ (t^{d_i}x + c)/p_i`, `deg c < d_i`). The sets `a(O)`, `a ∈ P_n`, are the `q^{m(n)}` balls of depth `m(n)`.
2. **The groupoid.** The germ groupoid `𝒢_H` of `V_q(H)` is the groupoid of germs of `Aff(R, U)` acting partially on `O`,
   and `(λz, d(λ) - d(μ), μz) ↦ germ of λμ^{-1} at μz` is an isomorphism `G_Λ ≅ 𝒢_H`. So `V_q(H) = F(G_Λ)`.
3. **Finiteness.** Every vertex carries `≥ 2` loops of each colour, so `V_q(H)` is of type `F_∞` (Li).
4. **Homology.** `H_j(𝒢_H; Z) ≅ (Z/(q-1))^{C(k-1, j)}` for `0 ≤ j ≤ k-1`, and `0` for `j ≥ k`.
   - `q = 2`: `𝒢_H` is integrally acyclic, and `V_2(H)` is **integrally acyclic, perfect and simple** (Li's Corollary D).
   - every `q`: `D(𝒢_H)` is rationally acyclic, and `V_q(H)^{ab}` maps onto `H_1(𝒢_H) ≅ (Z/(q-1))^{k-1}` (Li's
     Corollaries C, E).
   - `H` is **not contracting** for `k ≥ 2`: every section of `x ↦ p_1^n x` has multiplier `p_1^n`, so no finite
     set contains the deep sections of all powers. `k = 1` gives Thompson's `V_q`, since `H = F_q[t]` acts by
     finitary translations (there are no carries in characteristic `p`). `k = 2`, `p_1 = t - a` gives `V_q(F_q ≀ Z)` of
     `rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph`.
5. **Number fields (SKETCH).** For a global field `K`, a place `v`, `S ∋ v` containing the archimedean places, and a
   torsion-free `U ≤ O_S^×` with `|U|_v ≠ 1`: `H_*(Aff(O_S, U) ⋉ K_v; Q) = 0` if and only if no character
   `u ↦ |u|_v · Π_{σ ∈ I} σ(u)` (`I` a set of embeddings `K → C`) is trivial on `U`. For function fields `I = ∅`
   only, so the answer is always yes; this matches part 4.
   - `K = Q`, `v = p`, `O_S = Z[1/p]`, `U = ⟨p⟩`: this is the germ groupoid of the odometer group `V_p(Z)`, where
     `Z = ⟨x ↦ x + 1⟩` acts on `Z_p`. It fails, with `I = {id}`: `|p|_p · p = 1`. This agrees
     with the section character of `basilica-rn-group-is-not-a-k-graph-full-group`.
   - `BS(1,3) = ⟨x + 1, 3x⟩` on `Z_2` (`O_S = Z[1/6]`, `U = ⟨2, 3⟩`) passes, so the rational obstruction is silent.
     The groupoid of `Aff(Z[1/6], ⟨2, 3⟩)` on `Z_2` has `H_1 = H_2 = Z/2` (sketched computation), so it is **not**
     a graph (`k = 1`) groupoid.
     Whether it is a `k`-graph groupoid for some `k ≥ 2` is **open**.

## Remarks

- **Torsion-free `U` is essential.** With the full `O_S^×` and `q > 2`, the multipliers `ζ ∈ F_q^*` give torsion
  germs at the fixed point `0`. These are excluded by `torsion-germ-rn-groups-are-not-k-graph-full-groups`.
- **Where the number-field case breaks.** The construction in part 1 needs a tile common to all multipliers. Over
  `Q` the archimedean place seems to prevent that: for `U = ⟨2, 2/3⟩` on `Q_3 × R`, no common tile was found
  (heuristic, not proved).
- **Higher genus.** The proof uses only two facts. Each `w - (deg w)v` for `w ∈ S'` must be principal, and some
  divisor supported on `S'` must have degree `g - 1` and no sections, so that Riemann–Roch makes level sets simply
  transitive. Where these hold, the same construction is expected to work for a curve of genus `g`. This is not attempted here.
