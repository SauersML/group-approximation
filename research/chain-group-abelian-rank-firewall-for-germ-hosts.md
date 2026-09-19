---
rg: 2
id: chain-group-abelian-rank-firewall-for-germ-hosts
kind: claim
title: Every abelian subgroup of the Baumslag-Solitar chain group G_1 is locally cyclic or Z^2 and the zoom's centralizer is Z[1/2], so a faithful germ realization of the chain has a germ group with no Z^3, no Thompson F and no soluble zoom-root pair, which kills the smooth square-map model and forces the dyadic host to carry a global square map with a third singular orbit
artifacts:
  - experiments/chain-germ-firewall-2026-09-17/scout.py
  - experiments/chain-germ-firewall-2026-09-17/window.py
  - experiments/chain-germ-firewall-2026-09-17/out_scout.txt
  - experiments/chain-germ-firewall-2026-09-17/out_scout_nonaffine_6.txt
  - experiments/chain-germ-firewall-2026-09-17/out_window_affine_5.txt
  - experiments/chain-germ-firewall-2026-09-17/out_window_affine_6.txt
distinct_from:
  scale-periodic-bs-chain-germ-representations-are-not-faithful: that exhibits one kernel mechanism (sparse commuting defects) for the affine dilation; this proves a structural invariant of G_1 itself (abelian rank at most 2, cyclic-type centralizers) that every faithful realization must reproduce in its germ group, so it tests every realization, affine or not, by one group-theoretic check.
  non-affine-doubling-lifts-evade-the-sparse-defect-kill: that shows the sparse-defect kill fails off the affine class and splits the faithful-germ route into P0, P1, P2; this turns P1 into three necessary conditions on the germ group (F1-F3), proves that the smooth model dies at F3, and shows that P2 as written there has no global chain configuration and must be replaced by a host with a global square map.
  pl-chain-germ-group-contains-thompson-f: that (OPEN) builds Thompson's F inside the affine germ group; this proves G_1 has no F, so that claim, once proved, gives an independent second kill of the affine realization and a named test (F1) for the non-affine one.
  finite-hirsch-length-soluble-groups-hold-no-bs-chain: that excludes whole soluble host classes from containing a chain configuration; this is about which germ groups can be isomorphic to G_1, and uses Bass-Serre theory of G_1 rather than Hirsch length.
  bs-chain-configurations-exist-in-finite-germ-extensions-of-v: that builds the affine host with the odd square map; this builds the analogous host for a non-affine dyadic doubling lift, where the square map must be global and acquires a singular point at the lift's fixed point -1/6.
---

**ESTABLISHED (unreviewed)** by `chain-group-abelian-rank-firewall-proof` (elementary Bass-Serre theory
and explicit PL computation; no priority claimed).

## Setting

`G_1 = ⟨s, δ, σ | s δ s^-1 = δ^2, δ σ δ^-1 = σ^2⟩ = A *_C B`, with `A = ⟨s, δ⟩ ≅ BS(1,2)`,
`B = ⟨δ, σ⟩ ≅ BS(1,2)` and `C = ⟨δ⟩`. It is the chain group of
`higman-chain-group-pbh-iff-chain-configuration` in the germ convention. Put
- `N_B = ⟨r_n = δ^-n σ δ^n : n ≥ 0⟩ ≅ Z[1/2]`, the roots of the zoom `σ`;
- `ρ = s^-1 δ s` (so `ρ^2 = δ`) and `τ = s^-1 σ s`.

A **germ realization** is any triple of germs at `+∞` of homeomorphisms of the line with `σ(x) = x + 1`,
`δ σ δ^-1 = σ^2` and `s δ s^-1 = δ^2`. It defines `θ : G_1 -> Q = ⟨σ, δ, s⟩`. The realizations of
`non-affine-doubling-lifts-evade-the-sparse-defect-kill` (dyadic PL lift `δ`, PL square map `s`) are
the ones the host route to `G_1 ∈ B_A` needs.

## Statement

1. **Abelian rank firewall.** Every abelian subgroup of `G_1` is either torsion-free locally cyclic
   (isomorphic to a subgroup of `Q`) or isomorphic to `Z^2`. So `G_1` contains no `Z^3`, no `Z^∞`,
   no `Z[1/2] × Z`, no `Z ≀ Z` and no Thompson group `F`.
2. **Centralizer of the zoom.** `C_(G_1)(σ) = N_B ≅ Z[1/2]`.
3. **Free zoom-root pairs.** `⟨σ, ρ σ ρ^-1⟩` and `⟨σ, τ⟩` are free of rank 2. In particular
   `ρ_meta = [[ρ, σ], [ρ, σ^2]]` is a nontrivial element of `G_1` (reduced alternating length 15).
4. **The firewall for germ hosts.** If `θ` is faithful, then:
   - **(F1)** `Q` contains no `Z^3` and no `F`. In particular no nontrivial germ `g ∈ Q` has
     `σ^K`-sparse support for any `K ≥ 1`, that is, a moved set `S` with `S ∩ (S + jK)` bounded above
     for all `j ≠ 0`. Such a `g` would generate `Z^∞` with its `σ^K`-conjugates.
   - **(F2)** every germ in `Q` that commutes with `x ↦ x + 1` lies in `θ(N_B)`, a locally cyclic
     group. So every σ-periodic germ of `Q` is a root of a power of `σ`.
   - **(F3)** `⟨θρ, σ⟩` and `⟨θτ, σ⟩` are not soluble.

   Each of F1, F2, F3 is a necessary condition for prerequisite P1 of
   `non-affine-doubling-lifts-evade-the-sparse-defect-kill`, and each can fail on its own.
5. **The smooth model dies at F3.** Let `u` be the topological linearization of `δ` (so
   `u δ u^-1 = 2x`, `u σ u^-1 = σ`). It exists for `δ_f`, because the circle map of `δ_f` is an
   expanding degree-2 covering (Shub). The germ realization with `u s u^-1 = x^2` (the unique one, up to a
   constant, in which `u s u^-1` is a power map) has `θρ = u^-1 (2^(1/2) x) u` and `θσ = u^-1 (x+1) u`,
   both affine in the `u`-chart. So `⟨θρ, σ⟩` is metabelian and `θ(ρ_meta) = 1`. Regularity of the
   square map alone does not make a realization faithful. The smooth model and the sparse PL model die
   by different mechanisms: a soluble coincidence versus disjoint defects.
6. **P2 needs a global square map.** In the host `⟨V, b_f, a_f⟩` of the non-affine node, with `a_f`
   equal to `s` near `+∞` and to a translation near `-∞`, the relation `a_f b_f a_f^-1 = b_f^2`
   fails near `-∞`: one side is `4x + O(1)` and the other `2x + O(1)`. So the recorded triple is not a
   chain configuration, and it cannot certify `G_1 ∈ B_A` through
   `higman-chain-group-pbh-iff-chain-configuration`. The repair: for the lift
   `δ_f(n + r) = 2n + d(r)` of the non-affine node,
   - `δ_f` has exactly one fixed point, `x_0 = -1/6`, where it is affine of slope 4, and it moves every
     other point away from `x_0`;
   - there is a dyadic PL homeomorphism `s_f` of the whole line with `s_f δ_f s_f^-1 = δ_f^2`
     **exactly**, whose breakpoints accumulate only at `x_0` and `±∞`. On `[4, ∞)` it equals the square
     map of the w16 computations (fundamental-domain piece `[4, 17/2) -> [16, 65)`). On `(-∞, x_0)` it
     is generated by `x ↦ 2x + 1/2` on `[-1, -1/2)`;
   - so `(s_f^-1, δ_f^-1, x+1)` is a chain configuration in `Γ_f = ⟨V, δ_f, s_f⟩`, a finite germ extension
     of `V` with three singular orbits: those of `+∞`, `-∞` and `x_0` (tail `(01)^∞`);
   - the germ group at `x_0` is `⟨D_4, s̃⟩ ≅ BS(1,2)`, finitely presented, and the germ groups at
     `+∞` and `-∞` are both quotients of `G_1`.

   So BHM needs finite presentation of **both** `Q_+` and `Q_-`, and the faithful-germ route supplies
   it only if θ is faithful at both ends (P1+ and P1-). The two ends use independent fundamental-domain
   data, so they can be chosen, and must be checked, separately.

## Evidence on the non-affine example (exact computation, `out_scout.txt`)

On one bulk period at δ-scale `n` (method of the non-affine node):
- `ρ_meta` moves the **whole** period at scales 3, 5 and 6, and the metabelian word
  `τ_meta = [[τ,σ],[τ,σ^2]]` moves measure 4.23 (n = 3) and 3.02 (n = 5), so F3 is not violated at
  the tested scales;
- the affine control (`δ = 2x`) has `ρ_meta = τ_meta = c_1 = 1` on its bulk period, as its local
  affineness predicts.

## Lesson for general BH

Every kill of a germ realization of the chain found so far manufactures a big abelian or soluble
subgroup: `Z^∞` from disjoint defects (the affine kill), `F` from bend pictures (the OPEN affine
picture claim), a metabelian image from an affine coincidence (the smooth model). Bass-Serre theory
of `G_1` says a faithful realization must keep abelian rank at most 2 and zoom-periodic germs cyclic.
So the right invariant for P1 is **abelian rank of the germ group**, not bend density. A realization
is a live candidate exactly when its germs never decouple into far-apart commuting pieces and never
fall into a common affine chart. This is the germ-level form of the statement that `G_1` is an
amalgam of two metabelian groups over `Z` with no room for a third independent commuting direction.
