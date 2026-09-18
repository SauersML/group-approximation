---
rg: 2
id: nv-vertically-triangular-chart-cocycles-are-bounded
kind: claim
title: "Class-kill for nV: every Hilbert-valued function on vertically triangular charts (in particular every infinite weighted sum of brick wall counts) whose generator differences are l2 is itself l2, so the cocycle is a coboundary and bounded by 400 times its values on three elements of V x id"
distinct_from:
  brin-thompson-brick-charts-are-not-commensurated: that shows one set of brick charts is not commensurated; this shows that no l2 (weighted, infinite, Hilbert-valued) combination of such sets gives an unbounded cocycle
  brin-thompson-nv-no-cubical-action-proper-mod-triangular: that bounds finite wall counts along the Callard--Salo element via distortion; this bounds on all of nV every cocycle v - gv with v supported on vertically triangular charts, including infinite weighted wall sums that are not commensurating actions
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that bounds 1_C in every commensurating action; this is a uniform bound on all of nV for a class of non-commensurating cnd functions
  extractable-character-spectra-carry-no-almost-invariant-vectors: that uses the same three elements h_i on spectral laws of C(C,Z) ⋊ V; this transplants the paradoxical gap to l2 of chart rows and pairs it with a codimension-one sweep
---

**ESTABLISHED** by `nv-vertically-triangular-chart-cocycles-are-bounded-proof`.

**Setting.** `C = {0,1}^ω`, `n ≥ 2`, `G = nV`. Let `X` be the set of charts
`φ: C^n → U ⊆ C^n` in the Brin–Thompson groupoid, with `g·φ = g∘φ`. Write
`C^n = C^{n-1} × C` with points `(x, y)`. A chart is **vertically triangular** if
`pr_n∘φ(x, y) = w(x)·y` for a locally constant map `w` from `C^{n-1}` to finite binary
words. Let `Y ⊆ X` be the set of vertically triangular charts. `Y` contains all standard
brick charts `(u_1,…,u_n) ↦ (w_1u_1,…,w_nu_n)`.

Fix `h_1, h_2, h_3 ∈ V`: `h_1` is `0t ↦ 00t, 10t ↦ 01t, 11t ↦ 1t`; `h_2` is
`0t ↦ 01t, 10t ↦ 00t, 11t ↦ 1t`; `h_3` is `it ↦ (1−i)t`. Let `g_i = h_i × id` act on the
first coordinate. For a word `w`, let `s_w ∈ V` swap `[w0]` and `[w1]` by prefix
replacement, and let `σ_w = id × s_w` act on the last coordinate.

**Statement.** Let `π` be a unitary representation of `G` on `H`. Let `v: X → H` be supported
on `Y`. Put `(g·v)(φ) = π(g) v(g^{-1}φ)` and `b(g) = v − g·v`. Suppose `b(g_i) ∈ ℓ²(X; H)`
for `i = 1, 2, 3`, and `b(σ_w) ∈ ℓ²(X; H)` for every word `w`. Then

`‖v‖² ≤ 100 Σ_{i=1}^{3} ‖b(g_i)‖²`.

So `v ∈ ℓ²(X; H)`, `b` is the coboundary of `v` on all of `G`, and `‖b(g)‖ ≤ 2‖v‖` for all `g`.

**Corollary (weighted wall sums).** Let `A_k ⊆ Y` be sets and `w_k ≥ 0`, with `k` in a
countable index set. Suppose `ψ(g) = Σ_k w_k |gA_k Δ A_k|` is finite for the elements `g_i`
and `σ_w`. Then `Σ_k w_k |A_k| ≤ 100 Σ_i ψ(g_i)`, and `ψ ≤ 400 Σ_i ψ(g_i)` on all of `nV`.
To see this, take `H = ℓ²(K)` with trivial `π` and `v(φ) = Σ_k √w_k 1_{A_k}(φ) e_k`.

**Consequence for the goal.** No cnd function built from charts whose last coordinate is
triangular gives the Haagerup property (P1, P2, P3; routes R1 and R2 of the triangular split)
or rules out (T) or FW. This covers finite and infinite weighted brick wall counts and
ℓ²-sections over brick charts twisted by any representation. The obstruction is uniform:
three elements of `V × id` already bound the cocycle.

**Not ruled out.** Supports with some `V × id`-invariant piece on which `v` is not ℓ²: charts
with non-triangular last coordinate, unions of all rows, point orbits, and measure-valued or
non-chart parameter spaces. Also cocycles not of the form `v − g·v` over a permutation module.
