---
rg: 2
id: abstract-rn-simple-subgroups-avoid-tree-kernel
kind: claim
title: A simple subgroup of an abstract Röver–Nekrashevych group V_d(G, ψ) with ψ injective either meets the tree kernel trivially, and so embeds in the faithful group V_d(ρ_ψ G), or, if finitely generated, embeds in the kernel of the tree action of G
distinct_from:
  abstract-rover-nekrashevych-groups-are-finitely-presented: that shows V_d(G, ψ) is finitely presented for every finite recursion, faithful or not, and moves every difficulty into the tree kernel K_ψ; this shows that no simple subgroup can use K_ψ, so dropping faithfulness buys finite presentation but never new simple hosts.
  self-similar-hosts-contain-only-residually-finite-groups: that keeps non-residually-finite groups out of self-similar groups; this concerns Röver–Nekrashevych groups built from non-faithful recursions, which contain every input group G, residually finite or not.
  deligne-lattice-embeds-in-no-rover-nekrashevych-group: that excludes Deligne's lattice from every faithful V_d(H); Consequence 3 here transfers the exclusion to finitely generated simple subgroups of every abstract V_d(G, ψ) with ψ injective, except for simple groups already inside G.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that is the faithful theorem; Consequence 4 here is its transfer modulo the tree kernel.
---

**ESTABLISHED** by `abstract-rn-simple-subgroups-avoid-tree-kernel-proof` (lane bh-glnq-fresh,
2026-09-19). Elementary. Lane proof, not independently reviewed. No priority claimed.
It closes one candidate route to `gl-n-q-embeds-in-fp-simple-group`: Nekrashevych-type
hosts over non-residually-finite structure groups.

## Setting

As in `abstract-rover-nekrashevych-groups-are-finitely-presented`:
- `G` is a group, `d ≥ 2`, and `ψ : G → S_d ≀_d G`, `ψ(g) = π_g ⟨g_1, ..., g_d⟩`, is a homomorphism;
- `V_d(G, ψ)` is the group of classes of tables `(P, Q, β, λ)` under expansion;
- `ρ_ψ : G → Aut(T_d)` is the tree action and `H = ρ_ψ(G)`. `H` is self-similar and, as a
  subgroup of `Aut(T_d)`, residually finite;
- `K_ψ` is the kernel of the surjection `V_d(G, ψ) → V_d(H)` onto the faithful
  Röver–Nekrashevych group. It consists of the classes `[(P, P, id, λ)]` with every
  `λ(p) ∈ ker ρ_ψ`.

Assume `ψ` is **injective**. Remark 2 of the cited node pads any recursion to an injective one
without changing `ker ρ_ψ`. Then `g ↦ x_g`, the class of "`g` on the cone `C(1)`, identity
elsewhere", is an embedding `G → V_d(G, ψ)` (proof, step 1). So `V_d(G, ψ)` contains `G`,
residually finite or not, and is finitely presented when `G` is.

## Theorem

Let `ψ` be injective and let `S ≤ V_d(G, ψ)` be a simple group.
1. If `S` is not contained in `K_ψ`, then `S ∩ K_ψ = 1`, and `S` embeds in the faithful group
   `V_d(H)`.
2. If `S ≤ K_ψ` and `S` is finitely generated, then `S` embeds in `ker ρ_ψ`, a normal subgroup
   of `G`.
3. If `S ≤ K_ψ` in general, every finitely generated subgroup of `S` embeds in a finite direct
   power of `ker ρ_ψ`.

The structural fact behind 2 and 3: `K_ψ` is the directed union, over cone partitions `P`, of
subgroups `K_P ≅ (ker ρ_ψ)^P`.

## Consequences

1. **Non-faithful recursions give no new simple hosts.** Let `X ≤ S ≤ V_d(G, ψ)` with `ψ`
   injective and `S` finitely generated and simple, for instance finitely presented and simple.
   Then either `S` embeds in `G` (so `G` already contained the host), or `X ≤ S` embeds in the
   faithful `V_d(H)`, `H ≤ Aut(T_d)` self-similar. The free finite presentation of the cited
   node never comes with simplicity beyond the faithful case.
2. **For the root.** A finitely presented simple host of `GL_n(Q)` found inside some
   `V_d(G, ψ)` lies inside `G` or inside a faithful `V_d(H)`; in the second case
   `(Q,+) ≤ V_d(H)`, and `H` is finitely generated when `G` is. So the route "Nekrashevych
   hosts over a non-residually-finite structure group" is exactly the faithful Röver–Nekrashevych
   route. What is known there:
   - `PGL_2(Q) ≤ V_p(Γ_p)` for the rational Iwahori group `Γ_p`, which is not finitely generated
     (`pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori`); its open input is
     `rational-iwahori-group-lies-in-fp-self-similar-group`;
   - roots at periodic points are bounded in contracting `H`
     (`contracting-groups-bound-roots-at-periodic-points`).

   For odd `m ≥ 3` the group `SL_m(Q)` is simple (`sl-odd-q-simple-inputs-for-gl-n-q-root`).
   If `SL_m(Q) ≤ V_d(G, ψ)`, then either `SL_m(Q)` embeds in `V_d(H)`, or every finitely
   generated subgroup of `SL_m(Q)` embeds in a finite power of `ker ρ_ψ`.
3. **The Deligne refutation survives dropping faithfulness.** Deligne's lattice `Γ~` embeds in
   no faithful `V_d(H)` (`deligne-lattice-embeds-in-no-rover-nekrashevych-group`). So if
   `Γ~ ≤ S ≤ V_d(G, ψ)` with `S` finitely generated and simple and `ψ` injective, then `S`
   embeds in `ker ρ_ψ ≤ G`. Abstract Röver–Nekrashevych groups contain finitely generated
   simple hosts of `Γ~` only when `G` already does, so they do not rescue
   `decidable-groups-embed-in-rover-nekrashevych-hosts`.
4. **Kazhdan subgroups.** If `A ≤ V_d(G, ψ)` has property (T), then `A / (A ∩ K_ψ)` is
   residually finite (`kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`).

## Mechanism accounting (critic rules, `research/artifacts/gq-gq-critic.md`)

- **Operation:** a Thompson-type completion, `V_d(G, ψ)`.
- **Divisibility and distortion:** in case 2 of the theorem they are `G`'s own, since the host
  lies in `G`. In case 1 they must be produced by the faithful Cantor dynamics of `V_d(H)`:
  level shifts of `V_d` acting together with the residually finite `H`. This is how
  `V_p(Γ_p)` gets `(Q,+)`: level shifts supply `p`-divisibility and `Z_(p) ≤ Γ_p` the rest.
- **`SL_3(Z)`:** in case 1 it sits in `V_d(H)`, where Kazhdan subgroups are residually finite;
  that does not exclude `SL_3(Z)`.

## Lesson for general BH

Simplicity lives in the faithful action. Recursion data give finite presentation for free,
but a simple subgroup either meets the recursion's tree kernel trivially, and so is seen by
the faithful Cantor action, or lies in the kernel, and so (if finitely generated) inside the
input group. A Thompson-type route to BH can therefore outsource finite presentation to
non-faithful data, but it must realize the input's non-residually-finite behaviour
(divisibility, non-residually-finite Kazhdan pieces) in faithful Cantor dynamics, as
`Q ≤ 2V` (Kojima–Sheng) and `Q ≤ T-bar` (Belk–Hyde–Matucci) do.

## Other candidates weighed (no new claims)

- **Kojima–Sheng `Q ≤ nV` plus distortion.** Gated by `bs12-embeds-in-brin-thompson-2v`
  (OPEN), and for `n ≥ 3` by `gl-3-z-in-no-nv-via-cnd-transversal` (root Attempt 11).
- **Directed unions of Thompson-type completions.** A directed union of hosts is finitely
  generated only if it equals one stage, so one host for all `GL_n(Z[1/m!])` is the root
  itself; the uniformity question is the one left open by
  `gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups`.

## Credit

The presentation and kernel description are those of
`abstract-rover-nekrashevych-groups-are-finitely-presented` (lane bh-ffwz-q59). Building
Thompson-like groups from group data, faithful or not, is the viewpoint of Witzel–Zaremsky's
cloning systems (Groups Geom. Dyn. 12 (2018)), with the Röver–Nekrashevych case treated by
Skipper–Zaremsky; Scott (J. Algebra 90 (1984)), Röver and Nekrashevych for the faithful groups.
The dichotomy is a two-line normal-subgroup argument and may well be folklore.
