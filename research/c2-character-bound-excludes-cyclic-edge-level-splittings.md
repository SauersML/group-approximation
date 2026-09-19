---
rg: 2
id: c2-character-bound-excludes-cyclic-edge-level-splittings
kind: claim
title: For the one-relator (C2) group H = <b,c,d,e | eDDEdd.bCB.eDDEdd.bDcBd> with eps = (3,0,1,1), the eps-twisted character torsion Delta_omega has degree 1 exactly on the irreducible non-binomial hypersurface S = {b d^-3 + 2ce d^-1 - 3c + 2e d^-1 - 2 = 0} of Hom(H, C*), and degree 0 off it. Consequently in every level splitting of H some cycle edge group has rank >= 2 or is infinite cyclic inside [H,H], and (C2) has no FFLS whose unique cycle edge is cyclic, so the one-cycle case of the FFLS question reduces to edge rank 2 or 3. Unit (bi-monic) twisted-Alexander tests and the D_N torsion degree cannot go further
distinct_from:
  c2-mapping-torus-realizations-are-free-factor-level-splits: that reduces realizability of (C2) to the existence of an FFLS and excludes one-edge FFLS only among the 48 width-3 level rewritings found by search. This excludes every FFLS with one cyclic cycle edge, whatever presentation or tree part it has, by an invariant of H, and constrains all level splittings.
  c2-split-rose-passes-cycle-test-fails-gluing-rank: that excludes one rose by a gluing-rank count on a fixed marked graph. This is marked-graph free and uses the twisted homology of H over its character variety.
  c2-fibred-realizations-reduce-to-a-primitive-class: that asks for one free factor carrying the class c_H. This bounds the edge groups of arbitrary level splittings of H through the Mayer-Vietoris degree of character torsion.
artifacts:
  - experiments/c2-ffls-2026-09-19/RESULTS.md
  - experiments/c2-ffls-2026-09-19/chars.py
  - experiments/c2-ffls-2026-09-19/delta.py
  - experiments/c2-ffls-2026-09-19/twisted.py
---

**ESTABLISHED** through `c2-character-bound-excludes-cyclic-edge-level-splittings-proof`. Unreviewed.
- Theorem B, Corollaries B1 and B2 and the dead ends D1-D3 are proved by hand.
- The Fox derivatives and the formula for `Δ_ω` are exact (sympy, `chars.py`), with random spot checks on and off `S`.
- The coset images in D2 are an exact word-problem computation (`delta.py`).

## Setting

- `G = F_4 ⋊_φ ⟨y⟩`, `φ: p→q→r→s→rrSqPRs`, `ε: G → Z`.
- `H = ⟨b,c,d,e | r⟩` with `r = eDDEdd·bCB·eDDEdd·bDcBd` (the (C2) group after eliminating `a`, as in `c2-mapping-torus-realizations-are-free-factor-level-splits`).
  - `ε(b,c,d,e) = (3,0,1,1)`, `χ(H) = −2`, `N = H ∩ F_4`.
  - `r ∈ [F,F]`, so `H_1(H) = Z^4` is torsion-free. `H` is not free.
- A **level splitting** of `H` is a finite graph of groups for `H` with f.g. vertex and edge groups in `N`, tree edges inside `N`, and one stable letter of `ε = 1` for each cycle edge. An FFLS is a level splitting whose edge groups form a free factor system of `F_4`.
- For a character `ω: H → C^*`, let `Λ = C[t^{±1}]` and let `Λ_ω` be `Λ` with `x` acting by `ω(x) t^{ε(x)}`. Then `Δ_ω ∈ Λ` is the order of the torsion of `H_1(H; Λ_ω) ≅ H_1(N; C_ω)`.

## Theorem B

1. **(Exact formula.)** `Δ_ω` is the gcd of the four Fox derivatives of `r` specialised at `x ↦ ω(x) t^{ε(x)}`. It divides `1 − ω(d)t`. It has degree 1 if `ω ∈ S` and degree 0 otherwise, where
   - `S = { ω : ω(b)ω(d)^{-3} + 2ω(c)ω(e)ω(d)^{-1} − 3ω(c) + 2ω(e)ω(d)^{-1} − 2 = 0 }`.
2. **(Degree bound.)** For any level splitting with cycle edge groups `E_1,…,E_m` and any `ω`, `deg Δ_ω ≤ Σ_j (rk E_j − 1 + [ω|E_j = 1])`. Tree edges contribute nothing.
3. **(Rigidity of `S`.)** `S` is irreducible and not a coset of a subtorus. So it lies in no proper algebraic subgroup `{ω(g) = 1}` with `[g] ≠ 0` in `H_1(H)`.

**Corollary B1.** In every level splitting of `H`, some cycle edge group `E_j` has rank at least 2, or is infinite cyclic with `E_j ≤ [H,H]`.

**Corollary B2.** (C2) has no FFLS whose unique cycle edge group is cyclic.
- By `χ` and the Kurosh corollary of Theorem A, a one-cycle FFLS collapses to an HNN `H = V*_E` with `rk V = rk E + 2 ≤ 6`.
  - `rk E = 0` makes `H` free, which is impossible.
  - `rk E = 4` forces `E = F_4 ⊇ V`, which is impossible.
  - `rk E = 1` is excluded by B1: `H_1(H) = Z^4` forces `[g] = [sgs^{-1}]` in `H_1(V)`, so `g ∈ [V,V]`, and then `⟨g⟩` is not a free factor of `V`.
- **The one-cycle case is therefore reduced to `rk E ∈ {2,3}`, i.e. `rk V ∈ {4,5}`.**

## Dead ends (precise)

- **D1. Bi-monic tests are empty.** An FFLS forces every twisted-Alexander torsion order of finite-index subgroups to be bi-monic. But this holds for every f.g. `H ≤ F_n ⋊ Z`: the `Q[t^{±}]`-torsion of `H_1(N; Q)` is `Z`-pure of finite rank, so `t` acts on a lattice by an element of `GL`. The permutation-rep scans (`twisted.py`, degree ≤ 4) are only a code check.
- **D2. The `D_N` (Linnell) torsion degree is 0.** Over `D_N[t^{±}]` the torsion is `R/Rλ`, and `deg λ = 1` iff every `(PC)^{-1} ∂_x r` maps to 0 in `Q[⟨u⟩\H]`, with `P = eDDEddb` and `u = BeDDEddbD`. `delta.py` finds nonzero images for `x = b, d, e` (2, 10 and 4 cosets). So the `L^2`-type degree bound gives only `rk E ≥ 1`.
- **D3. No twisted degree excludes `rk E ≥ 2`.** For every `n`-dimensional rep `ρ`, the `c`-block of the Fox matrix has determinant `±t^{2n} det(ρ(u) − t)`. So `deg Δ_ρ ≤ n`, which is at most the Mayer-Vietoris bound `(k−1)n + dim coinv ρ(E)` for any edge rank `k ≥ 2`.

## Next step

Decide the HNN case `rk E ∈ {2,3}`, `rk V ∈ {4,5}`, which is the whole one-cycle case, by a non-degree invariant.
- **Pencil condition.** For `rk E = 2`, Theorem B says that `ι_* x_ω` and `j_* x_ω` are parallel in `H_1(V; C_ω) ≅ C^3`, with ratio `ω(d)^{-1}`, exactly for `ω ∈ S` (for `ω` nontrivial on `E`). This is a constraint, not a contradiction: `j` close to conjugation satisfies it.
- Candidate tools are a Whitehead/Stallings enumeration of rank-4 subgroups `V ≤ F_4` containing rank-2 free factors, or BNS/Brown `Σ¹` of `H` (`±ε ∉ Σ¹`).
- Multi-cycle FFLS with all cyclic edges must have a primitive edge generator in `[H,H]`. That is the handle for the tree-with-more-edges case.
- The slide-complex analogue of Theorem A is untouched.
