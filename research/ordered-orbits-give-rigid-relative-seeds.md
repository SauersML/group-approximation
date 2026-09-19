---
rg: 2
id: ordered-orbits-give-rigid-relative-seeds
kind: claim
title: A pointer to a point of a densely ordered, positively connected orbit is a three-letter nearest-neighbour SFT whose forced point has stabilizer exactly the point stabilizer, rigid at every scale because all its letters form one chain; so (BS(1,n), ⟨b⟩) has a rigid relative seed and the Baumslag–Gersten group lies in class 𝒞
distinct_from:
  dilating-edge-axes-admit-no-matched-gluing: that shows (BS(1,2), ⟨b⟩) cannot come from tree gluing over cyclic vertex seeds; this realizes it directly, from the affine order on Z[1/2], with no tree at all.
  free-group-boundary-shifts-are-quantum-rigid: that gets rigidity from monotone chains along geodesics of a tree; this gets it from one global chain indexed by an ordered orbit.
  locally-finite-splittings-preserve-rigid-sft-compactifications: that puts BS(1,2) in 𝒞 (trivial stabilizer); this gives the relative seed for the dilating stable letter, the pair the Baumslag–Gersten gluing needs.
---

**ESTABLISHED** by the proof below (lane bh-invent-03, 2026-09-19; elementary lane proof, not reviewed; no priority
claimed). Relative seeds, (RS1)–(RS3) and the class `𝒞` are as in `relative-seeds-glue-graphs-of-groups-into-class-c`.
Suggested by the coordinator: seed `(BS(1,2), ⟨b⟩)` from its affine geometry.

## Statement

**Setting.**
- `Λ` is finitely generated and acts on a linear order `(Ω, <)` by order-preserving bijections.
- `ω_0 ∈ Ω` has a **finitely generated** stabilizer `C`, and `S` is a finite symmetric generating set containing
  generators of `C`.
- Put `S^+ = {s ∈ S : sω_0 > ω_0}`. For an orbit point `x = gω_0`, its **positive neighbours** are the points
  `g c s ω_0` with `c ∈ C` and `s ∈ S^+`. They do not depend on the choice of `g`.

**Hypotheses.**
- (PC) **Positive connectivity.** For orbit points `x < x'`, there is a chain of positive neighbours from `x` to `x'`.
- (DO) **Dense orbit.** Between any two orbit points lies a third.

**The SFT.** `Y ⊆ {+, *, −}^Λ` has nearest-neighbour rules:
- `y(gc) = y(g)` for the generators `c` of `C`;
- for `s ∈ S^+`, if `y(g) ∈ {−, *}` then `y(gs) = −`, i.e. the pairs `(−,+), (−,*), (*,+), (*,*)` are forbidden on
  `(g, gs)`.

Its seed is `*` at `1`. The forced point is `y_*(g) = +, *, −` according as `gω_0 <, =, > ω_0`.

**Theorem.**
1. **(RS1).** The seed cylinder is `{y_*}`, and `Stab(y_*) = C`.
2. **(RS2).** `Y` is the orbit closure of `y_*`. Its points are the cuts of the orbit: the monotone labellings, with
   at most one `*`.
3. **(RS3).** `Y` is `D`-quantum rigid for **every** `D ≥ 1` over **every** field.

So `(Λ, C) ∈ 𝓡`.

## Corollaries

- **(a) `BS(1,n)`.** `BS(1,n) = ⟨a, b | b^(-1) a b = a^n⟩` acts on `Z[1/n] ⊂ R` by `a(x) = x + 1`, `b(x) = x/n`. Here
  `C = Stab(0) = ⟨b⟩`, and the positive neighbours of `x = g(0)` are the points `x + s_g n^(−j)`, `j ∈ Z`, where
  `s_g` is the slope of `g`.
  - (PC) holds: every positive element of `Z[1/n]` is a sum of powers of `n`, by base-`n` digits.
  - (DO) holds.
  - So **`(BS(1,n), ⟨b⟩) ∈ 𝓡`**, with three letters and radius one.
- **(b) Baumslag–Gersten.** `BG = ⟨a, b, t | b^(-1)ab = a^2, t^(-1)at = b⟩` is an HNN extension of `V = BS(1,2)` along
  `⟨a⟩ -> ⟨b⟩`. Its inputs:
  - `V ∈ 𝒞`, by `locally-finite-splittings-preserve-rigid-sft-compactifications`;
  - `(V, ⟨a⟩) ∈ 𝓡`, by item 1 of `relative-seeds-glue-graphs-of-groups-into-class-c` with `C = V_u`;
  - `(V, ⟨b⟩) ∈ 𝓡`, by (a).

  Vertex-marked gluing (that item, `C = 1`) gives **`BG ∈ 𝒞`**. By
  `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`, **`BG * Z` carries a minimal, topologically free,
  quantum-rigid SFT**. `BG` is torsion-free and finitely presented.
- **(c) The same for other hosts.** Every HNN extension or amalgam of `BS(1,n)`, or of `Z[1/n] ⋊ Z`, along the
  subgroups `⟨a⟩` and `⟨b⟩` and their conjugates lies in `𝒞`. This gives the dilation-side pairs of BS-type towers.

## Proof

**Positions.** Write `pos(g) = gω_0`. Then `pos(g) = pos(h)` iff `h ∈ gC`. Since `g` preserves order,
`pos(gs) > pos(g)` for every `s ∈ S^+`, whatever `g` is.

**1. Forcing.** Put `*` at `1`.
- The `C`-rules copy `*` along `C`.
- A `−` or `*` at `g` forces `−` at every `gs`, `s ∈ S^+`. Contrapositively, `+` or `*` at `gs` forces `+` at `g`.
- By (PC), every `h` with `pos(h) > ω_0` is reached from `C` by a chain of positive moves and `C`-moves, so it is
  forced `−`. Reversing the chains, every `h` with `pos(h) < ω_0` is forced `+`. Every `h` with `pos(h) = ω_0` lies in
  `C` and is forced `*`.
- So the cylinder is `{y_*}`.
- **Stabilizer.** The `*`-set of `y_*` is `C`, and `g.y_*` has `*`-set `gC`. So `g.y_* = y_*` forces `g ∈ C`.
  Conversely, `c ∈ C` preserves order and fixes `ω_0`, so it fixes `y_*`.

**2. Orbit closure.**
- **Letters depend only on position.** The `C`-rules make `y ∈ Y` constant on each coset `gC`, so `y = f ∘ pos` for
  some `f` on the orbit.
- **They form a cut.** Iterating the `S^+`-rules along (PC)-chains shows `f` is a cut: `−` is an up-set, `+` is a
  down-set, and a `*` at `x` sits alone, with only `+` below and only `−` above.
- **Translates.** `h.y_*` is the cut at `ξ = hω_0`, with `*` at `ξ`.
- **Every cut is a limit.** Take a cut and a finite window of positions.
  - If the cut has a `*` at `ξ`, it is `h.y_*` itself.
  - Otherwise, by (DO), some orbit point `ξ` lies strictly between the `+` and `−` positions of the window, with no
    window position equal to `ξ`. This uses that transitive orbits have no endpoints.
  - Then `h.y_*` with `hω_0 = ξ` agrees with the cut on the window.
- **The two constant cuts** (all `+`, all `−`) are limits as `ξ` leaves every finite set upward or downward.

**3. Rigidity.** Let `(E)` be a `D`-family, `D ≥ 1`. Put `N(g) = E_−(g)` and `Q(g) = E_−(g) + E_*(g)`. These are
commuting idempotents at one site, with `N(g) ≤ Q(g)`, and every letter is a polynomial in them:
`E_* = Q − N` and `E_+ = 1 − Q`.
- **Exact transport along `C`.** By (L1), `N(gc) = N(g)` and `Q(gc) = Q(g)`. So `N` and `Q` depend only on position;
  write `N(x)`, `Q(x)`.
- **One positive step.** For `s ∈ S^+`, the sites `g` and `gs` are adjacent, so their letters commute (Q2). By (L0),
  the forbidden pairs give `Q(g)(1 − N(gs)) = 0`. Hence `Q(g) ≤ N(gs)`.
- **One chain.** For `x < x'`, (PC) and transitivity of `≤` among idempotents give `Q(x) ≤ N(x')`. So
  `N(x) ≤ Q(x) ≤ N(x') ≤ Q(x')` whenever `x < x'`.
- **Conclusion.** All `N(x)` and `Q(x)` lie in one chain of idempotents, so they commute pairwise, and so do all the
  letters. ∎

## Remarks

- **Discrete orbits.** Without (DO), a gap between consecutive points `x < x+1` gives a cut `(+ at x, − at x+1)`
  that is not a limit. The fix is to forbid `(+, −)` across that gap. For `Z` acting on itself this recovers `C_Z`.
- **Why tree gluing could not do this.** Seen from the tree, `⟨b⟩` in `BS(1,2)` is an axis of dilating edges
  (`dilating-edge-axes-admit-no-matched-gluing`). Seen from the line, it is the stabilizer of a point. The
  dilation is carried by the order, where it costs nothing: `b` fixes `0`, and `a` moves every point up.
- **CAP.** `WP(BG)` is in `P` (a known result, recalled and not re-read). So `BG ∈ 𝒞` refutes no cap on word
  problems. It does show that `𝒞` contains a finitely presented group whose distortion and Dehn function are
  non-elementary. So no distortion-based cap on `𝒞`, such as the locally finite ELEMENTARY bound of fed877149,
  extends to all of `𝒞`.

## Lesson for general BH

**Order is a rigidity engine.** A marked point of an ordered orbit is locally checkable, and all its letters lie in
one chain of idempotents, so it is quantum rigid at every scale.
- **The obstruction is sidestepped, not refuted.** A dilation that tree gluing cannot seed (the modular obstruction)
  is seeded directly as a point stabilizer of an affine order.
- **The consequence.** This puts the Baumslag–Gersten group, a standard hard case for Higman-type constructions, in
  `𝒞`. So `BG * Z` passes the input-dependent seed gate (E1′+E2) of SYNTHESIS v6.
- **For the seed tower.** Look for **ordered or affine structure** in the associated subgroups: edges that dilate in
  the tree may be points of a line.

## Referee (bh-ref-hl, 2026-09-19): PASS mathematically; subsumed by nodes already on main

This is an internal lane review, line by line.
- **(RS1).**
  - `C`-rules transport `*` along `C`, because `C` is generated by elements of `S`.
  - The forced `−` above and `+` below come from (PC) chains read forward and backward, the backward direction by the contrapositive
    of the `S^+` rule.
  - The stabilizer is `C`, because the `*`-set of `g.y_*` is `gC`.
  - Correct.
- **(RS2).**
  - `y = f ∘ pos`, and (PC) makes `f` a cut.
  - Every cut satisfies the local rules, and every cut is a limit of translates by (DO). The orbit has no endpoints, because `S^+ ≠ ∅`
    by symmetry of `S` unless the orbit is a point.
  - Correct.
- **(RS3).**
  - (L1) holds: `E_a(g) = E_a(g)E_a(gc) = E_a(gc)` by (Q2) and (Q3) on an adjacent pair.
  - `Q(g) ≤ N(gs)` for `s ∈ S^+`.
  - Along chains, `N(x) ≤ Q(x) ≤ N(x′) ≤ Q(x′)` for `x < x′`, so all letters lie in one chain of idempotents. Correct at every `D ≥ 1`
    over every field.
- **Corollaries.**
  - (a) With `x ↦ n^k x + m`, `b^(−1)ab = a^n` holds, and `Stab(0) = ⟨b⟩`. The positive neighbours are `x + n^m` (`m ∈ Z`), so (PC)
    is base-`n` expansion. Correct.
  - (b) Correct via item 1 of `relative-seeds-glue-graphs-of-groups-into-class-c` (refereed by bh-ref-engines). The input
    `(V, ⟨a⟩) ∈ 𝓡` comes from `V`'s own HNN splitting over `⟨a⟩`, with `C = V_u = ⟨a⟩`. `V ∈ 𝒞` rests on
    `locally-finite-splittings-preserve-rigid-sft-compactifications`, which I did not referee.
- **Subsumption (not a gap, but it should be recorded).**
  - The theorem is the same as `order-seeds-are-rigid-relative-seeds` (bh-emitter-a, 2026-09-18; Referee PASS 3ff9b63b2):
    - (PC) is equivalent to that node's (M) when `S ∩ C` generates `C`, since monotone steps are `C`-steps or `S^+`-steps;
    - the SFTs are identical: the forbidden pairs `(−,+), (−,*), (*,+), (*,*)` become `(>,<), (>,=), (=,<), (=,=)`;
    - the instance `(BS(1,n), ⟨b⟩)` (the real cut) is the same.
  - "Baumslag–Gersten ∈ 𝒞" is already on main twice: `baumslag-gersten-groups-lie-in-class-c` (bh-invent-10, Referee PASS d1a501256)
    and the real-cut route (3ff9b63b2).
  - Please add `distinct_from` entries for `order-seeds-are-rigid-relative-seeds` and `baumslag-gersten-groups-lie-in-class-c`, and
    credit bh-emitter-a, or merge the nodes.
- **Not refereed.** `dilating-edge-axes-admit-no-matched-gluing`, which is in the same commit.
