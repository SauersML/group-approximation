---
rg: 2
id: rigid-seed-decorations-compute-only-where-rogue-walks-fill-space
kind: claim
title: An anticipation decoration of a rigid seed is rigid as soon as every non-halting walk in every point comes near every site, and it is not rigid when a non-halting basin stays far from another modification; periodic boundary points over Z^d (d ≥ 2) must be mortal, and over the tree seeds of free products of finite and cyclic groups and the product seeds of Z² every decoration computes only a finite-state output
distinct_from:
  anticipation-layers-convert-totality-into-isolation: that proves forcing, isolation and rigidity on the terminating part, and the two-far-basins obstruction; this closes the gap from both sides (a sufficient coarse-density criterion, a periodic-point theorem) and proves the finite-state bound on the tree and product families.
  seed-evaluation-is-bounded-by-the-forcing-radius: that bounds evaluation of a seed by its forcing radius; this bounds what a rigid decoration can add, geometry by geometry.
  seeds-record-every-bass-serre-pointer: that shows glued seeds read Bass–Serre pointers; here those readable pointers are what make every decoration of a tree-type seed a pushdown system.
---

**ESTABLISHED** (lane proof, bh-invent-18, 2026-09-18; elementary given the parent nodes and Büchi's
theorem; **not reviewed**; no priority claimed). Notation is that of
`anticipation-layers-convert-totality-into-isolation`:
- `Y = Y_0 ⋉_(σ,θ) T` is the decoration, with walk radius `r`;
- `Y_0` is `D`-quantum rigid, and `D' ≥ max(D, r + 1)`;
- a *rogue walk* is a non-terminating orbit in some point of `Y_0`.

## Theorem

1. **Sufficient criterion (coarse density).** Suppose that for all sites `q, u` and every `y ∈ Y_0`,
   the walk from `q` either terminates or comes within `2D'` of `u`. Then `Y` is `D'`-quantum rigid.
2. **Necessary criterion (clustering).** Suppose some `y ∈ Y_0` has a rogue basin `B` and some
   modification `x'` of `x = (y, τ)` in `Y` has `d(B, Δ(x, x')) > 2D`. Then `Y` is not `D`-rigid.
   Examples of such `x'`: a flip of another basin (item 5 of the parent), or a base modification far
   from `B`.
3. **Periodic points are mortal (A = Z^d, d ≥ 2).** If `Y` is `D`-rigid and `y ∈ Y_0` has
   finite-index stabilizer `L`, then every walk in `y` terminates within `[A : L]` steps.
4. **Tree seeds: decorations are regular.** Let the base be one of:
   - the tree seed of `F_n`;
   - the glued seed `X^+` of `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts` over a
     free product of finite cyclic groups and copies of `Z`, with `C_Z` on the `Z` factors.

   Then for every decoration, rigid or not, and every `t ∈ T`, the set `W_t` of sites whose walk in the
   forced base point halts at a terminal of type `t` is a regular language of normal forms. When the
   decoration is total, `τ_* = t` exactly on `W_t`, so `τ_*` is computed by a finite automaton.
5. **Product seeds over Z²: decorations are finite-state.** Take the product seed `C_Z ⊠ C_Z` with
   residue layers mod `p` (any seed over `Z²` whose points with both coordinates at infinity are
   periodic works). For every rigid, total decoration there are `R_0` and `P` such that:
   - `τ_*` at a site farther than `R_0` from both axes is a function of its `R_0`-pattern;
   - along each axis, `τ_*(i, j)` for `|j| ≤ R_0` is eventually periodic in `i` with period `P`.

## Proof

**0. The base algebra is classical.** In a `D'`-quantum family for `Y`, the base letters commute (the
base is rigid). Idempotents that commute generate a Boolean algebra `𝔅`.
- **The map from clopens.** Send each cylinder `[a at q]` to `E_a(q)`. This extends to a Boolean map
  from the clopen algebra of `Σ^A`.
- **Its kernel.** It contains every cylinder of a `D'`-pattern that does not occur, by (Q3). A clopen set
  missing `Y_0` is covered by finitely many such cylinders: by compactness, each of its points has a
  non-occurring `D'`-window, since `Y_0` is the SFT of its `D'`-windows once `D' ≥` its rule radius.
- **Consequence.** `𝔅` is a quotient of `Clop(Y_0)`. So any identity between clopen subsets of `Y_0`
  holds in `𝔅`, however far apart the sites involved are.

**1.**
- **The stopped paths.** Fix `q` and `u`. By compactness there is `k` such that every walk from `q`, in
  every point of `Y_0`, terminates or reaches `N_(2D')(u)` within `k` steps. The *stopped paths* (stopped
  at the first of these events) are finitely many, and they index a clopen partition of `Y_0`. By 0 their
  path projections `Π_γ` are orthogonal and sum to `1`.
- **The decomposition.** By the transport identity (parent, item 3),

      F_t(q) = Σ_γ F_t(q) Π_γ = Σ_(γ terminated) Π_γ Θ_t + Σ_(γ near u) Π_γ F_t(q_γ),

  with `d(q_γ, u) ≤ 2D'`.
- **Commutation with the base.** Let `b` be a base letter at `u`. The first sum lies in `𝔅`. In the
  second, `Π_γ F_t(q_γ) b = Π_γ b F_t(q_γ) = b Π_γ F_t(q_γ)`, using (Q2) and commutativity of `𝔅`. So every
  `F_t(q)` commutes with all of `𝔅`.
- **Commutation of labels.** Take `u = q'` and expand `F_t(q)` the same way.
  - The `𝔅`-terms commute with `F_(t')(q')`.
  - `Π_γ F_t(q_γ) F_(t')(q') = Π_γ F_(t')(q') F_t(q_γ) = F_(t')(q') Π_γ F_t(q_γ)`, by (Q2) and the previous
    step.
- **Conclusion.** Every letter `E_(a,t) = E^0_a F_t` commutes with every other. `∎`

**2.** This is Lemma 1 of `quantum-rigid-subshifts-cluster-the-modifications-of-each-point`, applied to
`x`, the flip of `B` (support `B`) and `x'`. `∎`

**3.**
- **Equivariance.** For `l ∈ L` the pattern at `lq` equals that at `q`, so `s_y(lq) = l s_y(q)`.
- **Bounded transients.** The walk descends to the finite set `A/L` of size `m`.
  - A walk that terminates does so within `m` steps: a repeated coset forces periodicity.
  - A rogue orbit from `q` reaches `p = s^(t_0)(q)` with `s^k(p) = p + v` for some `v ∈ L` and
    `t_0 + k ≤ m`. The lifted cycle is `Z_p = p + Zv + C`, with `C` finite, and its points all lie on one
    orbit.
  - So its basin `B` lies within `M = m·max|σ|` of `Z_p`: every site of the basin enters `Z_p` within `m`
    steps.
- **The far basin.**
  - Choose `l ∈ L` outside the line `Rv` (rank `L = d ≥ 2`). For `v = 0`, take any `l` of large length.
  - Then `d(Z_p, Z_p + nl) → ∞` as `n → ∞`. So `B` and `B + nl` are distinct rogue basins at distance
    `> 2D` for large `n`.
  - This contradicts item 5 of the parent. `∎`

**4.**
- **In the forced point the pattern is read from a suffix.**
  - Here the `r`-pattern at `q` is a function of the last `r` letters of the normal form of `q`, with
    `Z`-syllables spelled in unary, together with the finitely many normal forms shorter than `r`.
  - *Tree seed.* A vertex points to its parent, and its non-parent neighbours point to it.
  - *Glued seed.* A site `q = x_1 ⋯ x_m` lies in the piece of its last syllable, with exit `x_1 ⋯ x_(m−1)`,
    where the configuration is the vertex seed read at `x_m`. It is also the exit of its other piece. For
    `C_Z` only the sign of the last exponent and whether it is at most `r` are read.
- **The walk is a pushdown system.** One step reads the last `r` letters and appends or deletes one
  letter. So the walk is a canonical (prefix-, here suffix-) rewriting system with finitely many rules
  of bounded length, and a start marker handles the short words.
- **Büchi.** The terminals of type `t` form a regular set (a suffix condition). The set of words from which
  that set is reached is regular, by Büchi's theorem on regular canonical systems (J. R. Büchi, *Regular
  canonical systems*, Arch. Math. Logik Grundlagenforsch. 6 (1964) 91–111; recalled, not re-read). Since
  the walk is deterministic and stops at terminals, that set is `W_t`. `∎`

**5.**
- **The four orthant points are periodic.** The points of `Y_0` with both coordinates at `±∞` have
  stabilizer `(pZ)²`, so by 3 all their walks terminate within `p²` steps.
- **Bulk sites.** A site whose `R_0`-ball, with `R_0 = r(p² + 1)`, misses both axes sees such a point for
  those steps. Its walk therefore terminates within `p²` steps, inside its `R_0`-ball.
- **Near an axis.** Let the site be near the `x`-axis and far from the `y`-axis. Up to the time it
  approaches the `y`-axis, its walk agrees with the walk in the point `y_1` = (`±∞` horizontally,
  `C_Z` vertically), which is `pZ`-periodic horizontally.
  - In `y_1`, a walk that leaves the strip `|j| ≤ R_0` terminates within `p²` steps, by the bulk case.
  - Inside the strip the dynamics descends to a finite quotient. So every walk terminates within bounded
    time or becomes periodic with a horizontal drift `v`.
- **The drift points to the origin.** Totality of `y_*` forces `v` to point toward the `y`-axis. Zero or
  outward drift would give a walk of `y_*` that never terminates.
- **Eventual periodicity.** Periodicity in `y_1` makes the walks from `(i, j)` and `(i + P, j)` merge
  before they reach the origin region, with `P` a multiple of `|v|`. So `τ_*(i + P, j) = τ_*(i, j)` for
  large `|i|`. `∎`

## What this means for CB and CAP

**CB is now localized.** A rigid decoration with hard output needs all three of the following.
- **(i) No periodic boundary points with rogue walks.** Over `Z^d`, periodic points are mortal (3). So
  hard walks can only live in aperiodic parts of the boundary.
- **(ii) A base outside the tree/pushdown family.** Tree-type seeds give regular outputs (4), rigid or
  not.
- **(iii) Rogue walks that nearly fill space.** Item 1 is the target, and item 2 the limit.

**The product family is dead.** Product seeds over `Z²` give finite-state outputs (5).

**Where CB can still live.**
- Hierarchical, aperiodic bases (gate 4).
- Bases over groups that are neither tree-like nor virtually abelian, with seeds whose points at infinity
  are not periodic.
- The machine rung `(K_M, T'_M)` of the seed tower: there, (iii) says rogue runs must come near every
  site of `K_M`.

**For the seed tower (gate (c)).**
- **What is enough.** Exact transport plus pinned endpoints is not enough: the tree examples satisfy
  both and still carry no complexity.
- **The sufficient design rule.** Rigidity follows once every rogue run comes near every site (item 1).
  For instance, a machine that, while unhalted, sweeps its configuration space in a dovetailed spiral.
- **The necessary rule.** A rogue run must come within `2D` of every rogue run and every base
  modification (item 2).

**CAP (bh-star-a).** Items 4 and 5 are unconditional CAP-type bounds: decorations add nothing
computable beyond finite automata on two basic families of rigid seeds: tree-type gluings of finite and
cyclic groups, and product seeds over Z². Other recorded rigid seeds (locally finite splittings, real-cut
and order seeds, the scaling seed) are not covered.

## Lesson for general BH

A decoration of a rigid seed computes only where its unfinished computations fill space.
- **The mechanism.** Unfinished walks are what remain at infinity of any unbounded computation.
- **Two ways to fail.** Periodic points at infinity force them to finish, and tree geometry turns them
  into pushdown stacks with regular outcomes.
- **Consequence for the basic families.** On tree-type and product seeds, a decoration adds only
  finite-state information.
- **The one survivable design.** An aperiodic base on which each unfinished walk visits near every
  site: a sweeping machine at infinity. That is a concrete design rule for the machine rung of the seed
  tower, and a concrete kill test for CAP.
