---
rg: 2
id: stationary-vershik-maps-generate-contracting-rsgs-proof
kind: route
title: Vershik maps have one singular point, their singular germs never stack, so the generated group has a finite nucleus
target: stationary-vershik-maps-generate-contracting-rsgs
requires:
  - contracting-rsgs-embed-in-fp-simple-groups
artifacts:
  - research/artifacts/gq-bh-bh-free-03-substitution-full-groups.md
---

Notation as in the target. A path `x = e_1 e_2 ...` in `E` has `e_1` a root edge and
`e_k = (b,i)` for `k >= 2`. Call `(b,i)` *maximal* if `i = L_b` and *minimal* if
`i = 1`; root edges are both (one per terminus). Since `L_b >= 2`, no edge `(b,i)` is
both.

**Step 0 (the SFT).** `Gamma_0` (nodes `A`) is strongly connected because `sigma` is
primitive, and is not a directed cycle because every node has in-degree `L_b >= 2`.
Every node reaches `Gamma_0`, and every path of length `1` ends in `Gamma_0`. So
`Sigma_Gamma` has an irreducible core; it has no isolated points or empty cones.

**Step 1 (extremal paths).** Minimal edges into any `b` start at `l`, maximal ones at
`r`. So the all-minimal path of length `k >= 2` ending at `u` is
`m(u,k) = r_l (l,1)^{k-2} (u,1)`, the all-maximal one is
`M(v,k) = r_r (r,L_r)^{k-2} (v,L_v)`, and the unique infinite extremal paths are
`x_min = r_l (l,1)^∞` and `x_max = r_r (r,L_r)^∞`. The diagram is properly ordered,
and `T` is the Vershik map: at the first non-maximal edge `e_j` of `x`, replace it by
its successor and replace `e_1 ... e_{j-1}` by the all-minimal path to the source of
the successor; `T(x_max) = x_min`. (DHS §1.2; a homeomorphism of `E`.)

**Step 2 (local actions of `T`; claim 1).** Let `α ∈ Cones(E)`.
- If `α` contains a non-maximal edge, `T` maps `C_α` onto the cone of the modified
  word by the canonical similarity, so `T|_α = id_{C_{t(α)}}`.
- If `α = M(v,k)` with `k >= 2`, write `P_k = r_l (l,1)^{k-2}` (length `k-1`, ending
  at `l`). For `ω ∈ C_v`:
  if `ω_1 = (b,i)` with `i < L_b`, then `T(αω) = P_k (σ(b)_{i+1},1)(b,i+1) ω_{≥2}`;
  if `ω_1 = (b,L_b)` (forcing `v = r`), then `αω_1 = M(b,k+1)` and the formula
  recurses. So `T(αω) = P_k · τ_v(ω)` for a map `τ_v : C_v -> C_l` that does not
  depend on `k`. Hence `T|_α` is `τ_v` with the greatest common prefix of its image
  removed, the same map for every `k >= 2`.
- The cones of length `<= 1` are finitely many.

So `T` has finitely many local actions, and
`Nuc_T ⊆ {id_{C_u}} ∪ {T|_{M(v,2)} : v ∈ A}`. The same holds for `T^{-1}`, the
Vershik map of the reversed order (read substitution: reversed words, with `l, r`
exchanged).

**Step 3 (singular points; claim 2).** If `x ≠ x_max`, `x` has a first non-maximal
edge `e_j`, and `T` is a canonical similarity on `C_{e_1...e_j}`. Symmetrically for
`T^{-1}` away from `x_min`.

**Step 4 (two germ facts).**
(a) A canonical similarity `βω ↦ β'ω` preserves the eventual tail. Since the tail
edges `(l,1)` (minimal) and `(r,L_r)` (maximal) differ, no canonical similarity maps
`x_min` to `x_max`, or `x_max` to `x_min`.
(b) If a canonical similarity `c` fixes `x_min`, then near `x_min` it is the depth
shift `x_min[1..K] ζ ↦ x_min[1..K+d] ζ` (its source and target cones contain
`x_min`, so both prefixes are prefixes of `x_min`). Then `T^{-1} c T` equals the
canonical similarity `x_max[1..m] ω ↦ x_max[1..m+d] ω` on `C_{x_max[1..m]}` for all
`m > K`. Indeed `x_max[1..m] = M(r,m)`, and Step 2 gives
`T(M(r,j+1) ω) = x_min[1..j] τ_r(ω)` for every `j >= 1`, so
`T^{-1}(x_min[1..j] τ_r(ω)) = x_max[1..j+1] ω`. The symmetric statement holds for
`T c T^{-1}` near `x_min` when `c` fixes `x_max`.

**Step 5 (germ normal form).** Claim: every `g ∈ G_0` has a finite set `S_g ⊆ E`
such that each `x ∉ S_g` has a cone on which `g` is a canonical similarity, and each
`s ∈ S_g` has a cone on which `g = c_1 ∘ T^ε ∘ c_2`. Here `ε = ±1`, the `c_i` are
canonical similarities, and `c_2(s) = x_max` if `ε = 1`, `c_2(s) = x_min` if
`ε = -1`. The proof is by induction on word length, multiplying on the right by a
generator `h`.
- If `h ∈ V_{Gamma,E}`, compose germs (canonical similarity germs form a groupoid),
  with `S_{gh} ⊆ h^{-1}(S_g)`.
- If `h = T` and `x ≠ x_max`, `T` is a similarity near `x` and the same applies.
- If `h = T` and `x = x_max`: `T(x_max) = x_min`.
  - If `x_min ∉ S_g`, then `gT = (sim) ∘ T` near `x_max`.
  - If `x_min ∈ S_g`, the case `c_2(x_min) = x_max` is impossible by 4(a). Otherwise
    `g = c_1 T^{-1} c_2` with `c_2(x_min) = x_min`, and `gT = c_1 ∘ (T^{-1} c_2 T)`,
    which is a canonical similarity near `x_max` by 4(b). So `x_max ∉ S_{gT}`.
- `h = T^{-1}` is symmetric.

**Step 6 (finite nucleus; claim 3).** Fix `g ∈ G_0` and cover `E`, by compactness,
with finitely many cones from Step 5, shrunk so that each is mapped by `c_2` onto a
cone `C_β` with `T^ε(C_β)` inside the domain cone of `c_1`.
- On a similarity cone `C_α`, `g|_{αγ} = id` for all `γ`.
- On a singular cone `C_α`, BBMZ's composition lemma (l. 413) and the fact that
  canonical similarities have identity local actions give `g|_{αγ} = T^ε|_{βγ}` for
  all `γ`. For all but finitely many `γ` this lies in `Nuc_{T^ε}`.
So `Nuc_g ⊆ {id_{C_u}} ∪ Nuc_T ∪ Nuc_{T^{-1}}` for every `g`, which bounds
`Nuc_{G_0}`. `G_0 ⊇ V_{Gamma,E}` is an RSG by item 1 of
`contracting-rsgs-embed-in-fp-simple-groups`, and with Step 0 it is contracting.
