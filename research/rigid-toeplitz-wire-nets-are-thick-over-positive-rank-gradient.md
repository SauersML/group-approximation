---
rg: 2
id: rigid-toeplitz-wire-nets-are-thick-over-positive-rank-gradient
kind: claim
title: The wire net of a rigid Toeplitz shift must generate its level subgroup, so its density is at least 2(d(Γ)−1)/(|B_2D|·[Λ:Γ]); along a chain of positive rank gradient (odometer cost > 1) every level has holes of density bounded below, and a rigid Toeplitz shift there is irregular
distinct_from:
  quantum-rigid-subshifts-are-determined-by-thick-collars: that proves the wire nets exist (item 6); this bounds their size below by the rank of the level subgroup, which turns the rank gradient, equivalently the cost of the odometer, into a hole-density bound.
  fpbs-abert-nikolov-rank-gradient-equals-profinite-cost: that imports rank gradient = cost − 1 for Farber chains; this uses it to read the bound as a cost statement about the Toeplitz shift's own odometer.
  time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows: that constrains non-exact automorphism groups of Z^d-rows; this constrains rigid Toeplitz shifts over the acting group itself, which is the residually finite door at Osajda's group.
---

**ESTABLISHED** (lane proof, elementary; bh-ra-proof, 2026-09-19; **Referee PASS** bh-ref-q11 2026-09-19, with one precision; no priority claimed).
Standard facts marked "recalled" were not re-read. It does not decide the Toeplitz door at Osajda's group.

## Setting

As in item 6 of `quantum-rigid-subshifts-are-determined-by-thick-collars`:
- `Λ` is residually finite, and `x` is a Toeplitz point whose orbit closure `X` is infinite and
  `D`-quantum rigid.
- For a normal finite-index `Γ ≤ Λ` there are the holes `H_Γ`, the level class `K_Γ` and the wire net
  `C_Γ ⊆ H_Γ`: a `2D`-coarse component, `Γ`-invariant, carrying all the variation of `K_Γ`.
- Let `inj(Γ) = min{|γ| : 1 ≠ γ ∈ Γ}`, and let `d(Γ)` be the minimal number of generators.
- For a chain `Λ = Γ_0 ≥ Γ_1 ≥ …` of normal finite-index subgroups with trivial intersection, the rank
  gradient is `RG = lim_n (d(Γ_n) − 1)/[Λ:Γ_n]` (Lackenby; recalled).

## Theorem

1. **The net generates.** If `inj(Γ) > 4D`, the image `C̄_Γ` of `C_Γ` in `Γ\Λ` satisfies
   `|C̄_Γ| ≥ 2(d(Γ) − 1)/|B_(2D)|`. Hence the hole density satisfies
   `dens(H_Γ) = |Γ\H_Γ| / [Λ:Γ] ≥ 2(d(Γ) − 1) / (|B_(2D)| · [Λ:Γ])`.
2. **Positive rank gradient forces thick holes.** Along a chain with `RG > 0`, every deep level has
   `dens(H_(Γ_n)) ≥ 2RG/|B_(2D)|`. So the Toeplitz shift is irregular: its hole density does not tend
   to 0.
   - By Abért–Nikolov (`fpbs-abert-nikolov-rank-gradient-equals-profinite-cost`), `RG = cost − 1` for
     the profinite action on `lim Λ/Γ_n`, which is the Toeplitz shift's own odometer.
   - So the bound reads: **the holes of a rigid Toeplitz shift have density at least `2(cost − 1)/|B_(2D)|`
     at every level, where `cost` is that of its odometer.**

## Proof

1. **The covering.** `Λ → Γ\Λ` is a regular covering of `2D`-graphs with deck group `Γ`, because
   `inj(Γ) > 4D` makes it injective on `2D`-balls.
   - `C_Γ` is the full preimage of `C̄_Γ` (it is `Γ`-invariant) and it is connected.
   - For a regular covering over a connected base, the components of the preimage correspond to the
     cosets of the monodromy image of `π_1(C̄_Γ)` in `Γ` (recalled). Connectedness makes the monodromy
     surjective, so `d(Γ) ≤ rank π_1(C̄_Γ)`.
   - The `2D`-graph on `C̄_Γ` has degree `< |B_(2D)|`. So `rank π_1 = |E| − |V| + 1 ≤ |V|·|B_(2D)|/2 − |V| + 1`,
     which gives `|V| ≥ 2(d(Γ) − 1)/|B_(2D)|`.
   - Finally `C_Γ ⊆ H_Γ`.
2. The chain eventually has `inj(Γ_n) > 4D`, since its intersection is trivial and balls are finite.
   `(d(Γ_n) − 1)/[Λ:Γ_n]` decreases to `RG` (recalled), so the bound of item 1 is at least
   `2RG/|B_(2D)|` at every such level. A chain of normal subgroups with trivial intersection is a Farber
   chain, so Abért–Nikolov applies. ∎

## Calibration

| Group | `RG` (cost − 1) | Consequence | Consistent with |
|---|---|---|---|
| `Z^d` | `0` | none; nets may be thin | the hierarchical and crossing-wire rows, whose seams are expected to be thin nets |
| any infinite amenable group | `0` (cost 1, recalled) | none | (RA) is automatic there |
| `F_n` | `n − 1` | holes of density `≥ 2(n−1)/|B_(2D)|` | stronger: no rigid Toeplitz shift over `F_n` exists (`rigid-subshifts-over-free-factors-are-tight-almost-everywhere`, item 4) |
| surface groups, genus `g ≥ 2` | `2g − 2` | thick holes | untested |
| `SL_3(Z)`, groups with an infinite normal amenable subgroup | `0` (fixed price 1, Gaboriau; recalled) | none | untested |

## What this says about the Toeplitz door at Osajda's group

- A rigid Toeplitz shift over the decidable non-exact group `G` would refute (RA′).
- Item 1 of this node, with item 6 of the collars node, says what such a shift must carry at every level:
  - a `Γ`-periodic, coarsely connected wire net, quasi-isometric to `G`;
  - the net must generate `Γ`, so it has at least `2(d(Γ)−1)/|B_(2D)|` vertices mod `Γ`;
  - if the cost of `G`'s odometer exceeds 1, the net occupies a fixed positive fraction of `G`, and the
    shift is irregular.
- **Neither answer is reached.** Nothing above is contradictory: nets that generate, are nested and
  escape look combinatorially available in every residually finite group, at positive density. So a
  kill must use a quantum certificate beyond two configurations, or measure-analytic input.
- A construction must supply a rigidity source for the hole-filling. None on main applies:
  - compression toward ends needs ends or a boundary;
  - determinism needs an amenable direction;
  - finite presentation of a boundary host, read backwards, needs a boundary.
- **Scope (bh-invent-16, via bh-ra-counter).** The bound constrains only Toeplitz shifts over `G`
  itself (Line F).
  - Time lifts over `Z^d × G` (Line I, `time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows`)
    have fixed price 1, because of the infinite amenable normal factor `Z^d` (Gaboriau; recalled). So the
    bound is 0 there, and thin nets are allowed.
  - In Line F, a profinite skew layer over `G`'s odometer is again equicontinuous
    (`profinite-skew-layers-collapse-into-the-equicontinuous-factor`, ca17dbe93). So the net lives
    directly over the odometer.
- **The cost of `G`'s odometers is unchecked.** It is the cheapest next test. If it is 1 (fixed price),
  thin nets are allowed. If it is greater than 1, the construction must fill holes of positive density
  rigidly.

## The cost of Osajda's odometers (bh-ra-proof, 2026-09-19)

**Which form is targeted.** (RA) itself is refuted on main by a non-free example
(`rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer`, over an exact group). A rigid Toeplitz
shift over `G`:
- refutes (RA′) if it is topologically free;
- refutes (RA_free) if it is free.

Toeplitz shifts over residually finite groups can be chosen free, along a normal chain with trivial
intersection (Krieger; Cortez–Petite; recalled).

**What governs the bound.**
- The builder chooses the period chain. So the relevant quantity is the infimum of the cost over
  normal chains `(Γ_n)` of `G` with trivial intersection.
- The profinite action along such a chain is free and measure-preserving (the stabilizer of every
  point is `⋂Γ_n = 1`).

**Bounds (recalled facts only).** For every such chain,

    1 + β₁⁽²⁾(G)  ≤  cost(G ↷ lim G/Γ_n)  ≤  d(G).

- The lower bound is Gaboriau's inequality `cost ≥ 1 + β₁⁽²⁾` for free measure-preserving actions.
- The upper bound comes from the generating graphing.

**Consequences.**
- **If `β₁⁽²⁾(G) > 0`,** every rigid Toeplitz shift over `G`, along every chain, has holes of density
  `≥ 2β₁⁽²⁾(G)/|B_(2D)|` at every level with `inj > 4D`.
- **If `β₁⁽²⁾(G) = 0`,** the bound is decided chain by chain. That is the fixed-price question for `G`,
  open for such groups in general.

**What is not computed.**
- `β₁⁽²⁾(G)` is not computed on main, and not here.
- `G` is infinitely presented. Its finitely presented stages `G_n` are small cancellation groups. There
  an aspherical presentation complex fixes `β₂⁽²⁾ − β₁⁽²⁾ = χ(G_n)` and leaves `β₁⁽²⁾` free.
- None of Gaboriau's fixed-price-1 criteria is visible for `G`: no infinite normal amenable subgroup,
  no product structure, and no chain of commuting infinite-order generators.

So **the cost of Osajda's odometers is open**. It lies between `1 + β₁⁽²⁾(G)` and `d(G)`.

**The next decisive computation is `β₁⁽²⁾(G)`.** If it is positive, Line F needs thick rigid hole-filling
at every level. If it is zero, Line F reduces to finding one chain of cost 1.

## Lesson for general BH

**A rigid Toeplitz shift pays for the rank of its periods.**
- All variation of a level class runs through one periodic wire net, and that net must generate the
  level subgroup.
- So the hole density is bounded below by the rank gradient, which is the cost of the odometer minus 1.
- Over amenable groups this costs nothing. Over free-like groups it forces irregular Toeplitz shifts
  with thick holes.
- At Osajda's group the door stays open. The first thing to compute is the cost of its profinite
  actions.

Credit: rank gradient is Lackenby's. Its equality with the cost of the profinite action is
Abért–Nikolov's. Fixed price results are Gaboriau's. The Toeplitz level-class framing follows
Krieger's and Cortez–Petite's work on Toeplitz subshifts over residually finite groups (recalled).

## Referee (bh-ref-q11, 2026-09-19): PASS, with one precision

I checked this given item 6 of `quantum-rigid-subshifts-are-determined-by-thick-collars` (the net `C_Γ` exists, is `2D`-connected, `Γ`-invariant and inside `H_Γ`), which I did not re-referee.

**Item 1: correct.**
- `inj(Γ) > 4D` and normality make `Λ → Γ∖Λ` injective on `2D`-neighbourhoods and surjective onto them, with no loops or multi-edges. So it is a regular covering of simple `2D`-graphs with deck group `Γ`.
- The full preimage of the induced subgraph `C̄_Γ` covers it. Its components are indexed by `Γ` modulo the monodromy image of `π_1(C̄_Γ)`, so connectedness gives `d(Γ) ≤ rank π_1 = |E| − |V| + 1`.
- The count holds. With degree `≤ |B_(2D)| − 1` it even gives the slightly better `|V| ≥ 2(d(Γ)−1)/(|B_(2D)| − 3)`.

**Item 2: correct**, by Schreier's monotonicity, Farber (normal chains with trivial intersection), and Abért–Nikolov.

**Precision.** "The Toeplitz shift is irregular" needs the chain to be the shift's own period structure, whose inverse limit is its odometer. That is implicit in "which is the Toeplitz shift's own odometer".
- The rank gradient depends on the chain in general: it is the cost of that profinite action, minus 1.
- So a large hole density along some other chain does not by itself contradict regularity.
- Also, "every level" should read "every level with `inj(Γ_n) > 4D`".

**Calibration.** The table (`Z^d`, amenable, `F_n`, surface groups, fixed price 1) and the Line F scope note are consistent with the recalled facts.
