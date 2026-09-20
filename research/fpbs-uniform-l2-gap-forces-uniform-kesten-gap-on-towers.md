---
rg: 2
id: fpbs-uniform-l2-gap-forces-uniform-kesten-gap-on-towers
kind: claim
title: The uniform l2 gap conjecture forces a uniform percolation Kesten gap along every normal subgroup that has a fibre-truncation tower
distinct_from:
  fpbs-fibre-truncation-towers-add-no-slack: that proves the finite fibre occupations of a tower increase to the relative susceptibility and kills tower-dependent constants; this supplies the tower-independent bound from the uniform l2 gap, through the finite test vector of the truncated fibre, and draws the consequences for the uniform conjecture.
  fpbs-uniform-l2-gap-marked-groups: that is the uniform conjecture itself; this is an unconditional implication from it to a uniform relative gap, plus an unconditional upper bound on its admissible delta.
  fpbs-percolation-kesten-normal-gap: that is the strict relative gap along every normal subgroup with nonamenable quotient; this derives it from the uniform l2 gap, with a constant depending only on the marking size and the quotient spectral radius, for towerable normal subgroups only.
  fpbs-relative-threshold-continuous-at-co-amenability: that shows no relative gap is uniform as the Schreier Cheeger constant tends to 0; this is uniform only at a fixed quotient spectral radius, which is consistent with it.
---

**ESTABLISHED** (an implication, proved unconditionally) through
`fpbs-uniform-l2-gap-forces-uniform-kesten-gap-on-towers-proof`.

**Setting.**

- Let `(Gamma; s_1,...,s_k)` be a `k`-marked group, and put
  `S = {s_i^(+-1)} \ {e}` and `G = Cay(Gamma,S)`, as in Section 1 of
  `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`.
- Let `H` be a normal subgroup of `Gamma` with a **tower**: subgroups
  `H_j <= H`, normal in `Gamma`, of finite index in `H`, nested, with trivial
  intersection.
- Put `pi_j : Gamma -> Gamma/H_j`, and let `G_j` be the simple Cayley graph of
  the marked group `(Gamma/H_j; pi_j(s_1),...,pi_j(s_k))`.
- Let `mu_bar` be the image in `Q = Gamma/H` of the uniform measure on `S`, and
  `rho_Q = limsup_n mu_bar^(*n)(e)^(1/n)`.
- Write (U)`_(k,eta)(M,delta)` for the statement that every `k`-marked group
  whose simple Cayley graph has spectral radius at most `1 - eta` satisfies
  `||T_(p_c+delta)|| <= M`. The norm is (0.1) of
  `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`.
- The conjecture `fpbs-uniform-l2-gap-marked-groups` says: for all `k` and
  `eta`, some `(M,delta)` works.

**Theorem.**

1. **Tower test vector (unconditional).** For all large `j`, `G_j` is the
   `|S|`-regular graph `Cay(Gamma/H_j, pi_j(S))` and `rho(G_j) <= rho_Q`.
   For every `p`,
   ```text
   E_p |K^G_o ∩ H|  =  sup_j E_p |K^(G_j)_o ∩ pi_j(H)|  <=  liminf_j ||T^(G_j)_p|| .
   ```
2. **Uniform Kesten gap from (U).** Suppose `rho_Q <= 1 - eta` and
   (U)`_(k,eta)(M,delta)` holds. Put `delta' = min(delta, eta/(1+eta))`. Then
   ```text
   E_(p_c(G) + delta') |K^G_o ∩ H|  <=  M ,    so    p_c(H;G) >= p_c(G) + delta' .
   ```
   So `fpbs-uniform-l2-gap-marked-groups` implies
   `fpbs-percolation-kesten-normal-gap` for every towerable `H`, with a gap
   that depends only on `k` and `rho_Q`.
3. **The admissible delta is capped (unconditional).** Let `N` be a normal
   subgroup of `F_2` with `sqrt(3)/2 < rho_N := rho(F_2/N) < 1`, and let `T` be
   the standard 4-regular tree. If (U)`_(2,eta)(M,delta)` holds with
   `1 - eta >= rho_N`, then
   ```text
   min(delta, eta/(1+eta))  <=  s_N - 1/3 ,    where   s_N = (2 rho_N - sqrt(4 rho_N^2 - 3))/3 .
   ```
   Moreover `s_N - 1/3 >= (2/3)(1 - rho_N)`, and
   `(s_N - 1/3) / ((2/3)(1 - rho_N)) -> 1` as `rho_N -> 1`.

**Scope of item 2.**

- Towers exist when `H` is finitely generated and residually finite
  (`fpbs-fibre-truncation-towers-add-no-slack`).
- They exist for **every** normal `H` when `Gamma` is residually finite: take
  `H_j = H ∩ K_j` for a nested chain of finite-index normal subgroups `K_j`
  with trivial intersection.
- `rho_Q < 1` whenever `Q` is nonamenable. The proof route reduces this to
  Kesten's criterion for simple random walk. The converse is Kesten's theorem
  for symmetric measures and is not used.
- Under the convention of `U_{M,delta}` in the local-limits note, a graph with
  `p_c + delta > 1` is not in the class, so (U) already forces
  `delta <= 1 - p_c(G_j)` and `delta' = delta`. The cap `eta/(1+eta)` only
  makes item 2 independent of how `T_p` is read for `p > 1`.

So, **granted the uniform conjecture, the percolation Kesten gap holds on every
residually finite group, uniformly in `k` and `rho_Q`.** This covers:

- `F_2 x F_2` along a factor, on which the recorded attempts on
  `fpbs-percolation-kesten-normal-gap` all stop;
- `F_2 x Z`, braid groups, Seifert-fibred groups and surface-by-surface groups;
- lattices with normal subgroups of nonamenable quotient.

**What it changes.**

- **Hardness transfer.**
  - Suppose a relator cylinder contains the whole tower of `(Gamma,S,H)`. This
    happens, for example, for the cylinder of `[s_1,s_3] = e` and the tower
    `F_2 x (F_2/K_j)` of `F_2 x F_2`.
  - Then any proof of the uniform conjecture, or of its cylinder piece on that
    cylinder, proves the relative gap along `H`.
  - So the uniform route is no shortcut past the Kesten route. On residually
    finite groups it is at least as strong, and uniformly so.
- **Calibration of delta.**
  - Item 3 caps the constant: `delta(2,eta) = O(eta)` as `eta -> 0`, whenever
    spectral radii `rho_N` accumulate at `1 - eta` from below.
  - This is consistent with the value `eta/(4(2k-1)) = eta/12` of the high-girth
    patch (`fpbs-high-girth-uniform-l2-patch`, Section 3 of the Baire artifact),
    since `s_N - 1/3 >= (2/3) eta` whenever `rho_N <= 1 - eta`. The truncations
    `G_j` of `N` have girth tending to infinity, so they lie in that patch.
- **The fixed-p l2 norm is not locally bounded at the free group.**
  - For every `p in (s_N, 1/sqrt 3)`, `||T^T_p|| < infinity`, but
    `||T^(G_j)_p|| -> infinity` along the tower of `N`, and `G_j -> T` locally.
  - So only the form "at `p_c + delta`" of the conjecture can be locally
    uniform near `T`. No form at a fixed `p` in `(1/3, 1/sqrt 3)` is locally
    uniform.
