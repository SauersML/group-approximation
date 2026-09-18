---
rg: 2
id: fpbs-fibre-truncation-towers-add-no-slack
kind: claim
title: Along a fibre-truncation tower the finite fibre occupations increase to the relative susceptibility, so truncations add no slack
distinct_from:
  fpbs-expander-approximant-giant-data-is-glued: that kills finite expander approximants through the glued giant law; this concerns infinite quotients that keep Gamma/H intact and make only the fibre finite, where no giant forms and the fibre occupation converges exactly.
  fpbs-relative-susceptibility-tube-excursion-bound: that bounds relative susceptibility on the group itself by a tube term plus a sphere bubble; this compares the group with its fibre truncations and proves monotone convergence of the fibre occupation.
  fpbs-bs-iff-finite-relative-susceptibility: that is the equivalence between the threshold gap and finite relative susceptibility on one graph; this transports relative susceptibility along a tower of covering quotients.
artifacts:
  - research/artifacts/fpbs-fibre-truncation-towers-2026-09-17.md
---

**ESTABLISHED.** Let `Gamma` be finitely generated, `S` a finite symmetric
generating set, `G = Cay(Gamma,S)`, and `H` a normal subgroup. Let
`H_k <= H` be subgroups normal in `Gamma`, of finite index in `H`, nested
(`H_(k+1) <= H_k`), with trivial intersection. Put
`G_k = Cay(Gamma/H_k, S_k)`, `pi_k : Gamma -> Gamma/H_k`, and fix `k_0` with
`H_(k_0) ∩ B_Gamma(2) = {1}`, so that for `k' >= k >= k_0` the maps
`G -> G_(k') -> G_k` are covering maps of simple graphs. Then for every
`p in [0,1]`, every `n >= 1` and `k_0 <= k <= k'`:

1. **Monotone.**
   `P_p(|K^(G_k)_o ∩ pi_k(H)| >= n) <= P_p(|K^(G_(k'))_o ∩ pi_(k')(H)| >= n) <= P_p(|K^G_o ∩ H| >= n)`.
2. **Convergent.** These probabilities converge to `P_p(|K^G_o ∩ H| >= n)`,
   and `chi^(k)(p) = E_p|K^(G_k)_o ∩ pi_k(H)|` increases to
   `chi^H_G(p) = E_p|K^G_o ∩ H|` (possibly `+infinity`).
3. **Thresholds.** `theta_(G_k)(p) <= theta_(G_(k'))(p) <= theta_G(p)`, so
   `p_c(G_k)` is nonincreasing in `k` and at least `p_c(G)`.

Consequently `chi^H_G(p) = sup_k chi^(k)(p)`. For such a tower, the hole
`fpbs-amenable-wq-normal-relative-subcriticality` on `(Gamma,S)` is equivalent
to a bound on the finite fibre occupations `chi^(k)(p)` that is **uniform in
`k`**, at one `p > p_c(G)`.

Towers exist whenever `H` is finitely generated and residually finite: take
`H_k` to be the intersection of the subgroups of `H` of index at most `k`.
Examples are central or normal `Z` (braid groups, `F_2 x Z`, Seifert-fibred
groups), normal `Z^d` (`Z^d x| SL_d(Z)`), and every polycyclic normal subgroup.

**Obstruction (killed class: the finite-models transplant of the hole).**
Consider derivations of the hole, or of `p_c(G) < p_u(G)`, from results on the
truncations `G_k` whose constants depend on `k`. Every such derivation dies at
the passage `k -> infinity`. Examples:

* Choi--Seo on `Gamma/<z^k>` when `Gamma/<z>` is hyperbolic;
* hyperbolic `L2` gaps, whose constants grow with the isometrically embedded
  fibre cycle;
* `p_u = 1` on infinitely-ended truncations;
* the trivial bound `chi^(k) <= [H:H_k]`.

**Where it dies.** By item 2, the only datum that transfers is a uniform bound
on `chi^(k)(p)` at one parameter, and that bound equals `chi^H_G(p)`, which is
the hole itself.

**The invariant.** The fibre occupation at a fixed parameter, uniformly over
the tower. Finite quotients are already killed by the glued giant law, so the
finite-models family has no slack left on this hole.

The other half of the kill is that the uniqueness thresholds of the truncations
bound `p_u(G)` only from above. See
`fpbs-fibre-truncation-pu-lower-semicontinuous`.

**Proof.** `fpbs-fibre-truncation-towers-add-no-slack-proof`. It uses a lifted
exploration coupling along the covering maps and the local injectivity of
`pi_k` on large balls. It does not use amenability, wq-normality or
nonamenability.
