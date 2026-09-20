---
rg: 2
id: racg-generators-are-singular-over-their-wall-trees
kind: claim
title: In the right-angled Coxeter group of a graph of girth at least 5, a standard generator s whose link vertices each have a second neighbor is singular in the BBMZ horofunction host at two horofunctions over every limit point of its wall; so s has continuum many singular points as soon as its link has three vertices; the Petersen-graph group has an unbounded host, and the pentagon's four singular chains are recovered exactly
distinct_from:
  bbmz-singularity-is-a-recurrent-coincidence: that proves the recurrent-coincidence criterion (Theorem D); this verifies the criterion along every limit point of a generator's wall in girth-5 right-angled Coxeter groups, which settles boundedness for them.
  bbmz-hosts-with-higher-dimensional-boundary-are-unbounded: that sketches singularity along wall spheres of cocompact reflection groups of dimension at least 3; this is a complete proof in the 2-dimensional right-angled case, where boundaries are 1-dimensional.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - bbmz-singularity-is-a-recurrent-coincidence
```

**Status.**
- **ESTABLISHED** (lane proof, bh-q12-kazhdan, 2026-09-19; not reviewed). The proof is a direct verification of
  Theorem D of `bbmz-singularity-is-a-recurrent-coincidence`, which is refereed PASS.
- No computation was run, and no priority is claimed.
- Calibration: the proposition predicts 4 singular points per generator for the right-angled pentagon. That matches
  the exact computation in `gq-bh-finf-hyp-cone-matching-test.md`.

## Setting

- `Γ` is a finite graph of girth at least 5 (triangle-free, no 4-cycles), and `W = W_Γ` is its right-angled Coxeter
  group with standard generators.
- `W` is hyperbolic (Moussong: there are no induced squares). The Davis complex is a CAT(0) square complex, and the
  word metric counts separating walls.
- Fix a vertex `s`, with link `lk(s)` and star `st(s) = {s} ∪ lk(s)`. `W_0 = H_s` is the wall dual to the edge
  `(1, s)`.
- `lk(s)` is an independent set, so `W_{lk(s)}` is a free product of copies of `C_2`, with Bass–Serre tree `T_s`.
  The wall `H_s` is stabilized by `⟨s⟩ × W_{lk(s)}`, and its limit set is `ΛH_s = ∂T_s`:
  - two points if `|lk(s)| = 2`;
  - a Cantor set if `|lk(s)| ≥ 3`.

## Proposition F

Assume every vertex of `lk(s)` has a neighbor other than `s`. Then for every `ζ ∈ ΛH_s`, `s` is singular at the
horofunction `sσ_+`, where `σ_+` is the limit of the ray of `T_s` toward `ζ` (on the `1`-side of `H_s`). By symmetry
it is also singular at the corresponding point on the far side.

Consequently:
- if `|lk(s)| ≥ 3`, `sing(s)` has the cardinality of the continuum;
- if `|lk(s)| ≤ 2`, `sing(s)` is finite, by Theorem A, since the offset frontier of `s` lies in the finite set
  `ΛH_s` and `φ` is finite-to-one.

## Proof

**The ray.** Write the ray toward `ζ` as `u_0 = 1`, `u_{j+1} = u_j t_j`, with `t_j ∈ lk(s)` and `t_{j+1} ≠ t_j`.
- `C_{j+1}` is the wall dual to the edge `(u_j, u_{j+1})`. It crosses `H_s`, because `t_j` commutes with `s`.
- Consecutive walls `C_j, C_{j+1}` do not cross, because `t_{j−1}` and `t_j` do not commute. So the `C_i` are
  nested, and `C_1, …, C_j` are exactly the walls separating `1` from `u_j`.
- Hence `δ_1(C_{j+1}) = j + 1`. The walls separating `u_j` from `σ_+` are exactly `C_{j+1}, C_{j+2}, …`.

**Genericity and offsets.**
- The only wall separating `1` from `s` is `H_s`, and `r_0 = s`. So every `ζ ∈ ΛH_s` is generic in the sense of
  Theorem D.
- On the `1`-side, `d(s,v) − d(1,v) = 1`, so `a = ℓ_s(σ_+) = 1`.

**Condition (i) at depth `N = j + 1`.** Both `u_j` and `u_{j+1}` agree with `σ_+` on every wall of depth `≤ j`, by
the description of the separating walls. They lie on opposite sides of the crossing wall `C_{j+1}`, which has depth
`N`. So `C_{j+1}` cuts `Z_{N−1}(σ_+)`.

**Condition (ii) at depth `N = j + 1`.**
- **The outer wall.** Pick `x ∈ lk(t_j) ∖ {s}`. By girth `≥ 5`:
  - `x ∉ st(s)`; otherwise `s, t_j, x` would form a triangle;
  - `x ∉ lk(t_{j−1})` for `j ≥ 1`; otherwise `s, t_{j−1}, x, t_j` would form a 4-cycle.
- `O` is the wall dual to the edge `(u_j, u_j x)`. Since `x` commutes with `t_j`, it is also dual to
  `(u_{j+1}, u_{j+1}x)`. The following checks show it is a (+)-wall of depth `N`:
  - **It does not cross `H_s`**, because `x` and `s` do not commute.
  - **Its far halfspace lies on the `1`-side**, because `u_j` and `u_j s` lie on the same side of `O`.
  - **It does not cross `C_j`** (for `j ≥ 1`), because `x` and `t_{j−1}` do not commute. So its far halfspace lies beyond
    `C_1, …, C_j`.
  - **Its depth is `j + 1`**, because `|u_j x| = j + 1`: `x` is not a letter of `u_j`, and it does not commute
    with the last letter `t_{j−1}`.
- **Two points of the cylinder.** Let `Z'` be `Z_{N−1}(σ_+)` together with the constraints of all crossing walls
  of depth `N`.
  - `u_{j+1}` differs from `σ_+` only on `C_{j+2}, C_{j+3}, …`, all of depth `≥ j + 2`. So `u_{j+1} ∈ Z'`, on the
    near side of `O`.
  - `u_{j+1}x` differs from `σ_+` only on `O` and on `C_{j+2}, …`. `O` is not a constraint of `Z'`: it has depth
    `N` and is not a crossing wall. So `u_{j+1}x ∈ Z'`, on the far side of `O`.
- So `O` cuts `Z'`.

**Conclusion.** (i) and (ii) hold at every depth `N ≥ 1`. By Theorem D, `s` is singular at `s^{-1}σ_+ = sσ_+`.
- Distinct `ζ` give distinct `σ_+`, since `φ(σ_+) = ζ`.
- `∂T_s` is a Cantor set when `|lk(s)| ≥ 3`. ∎

## Examples

- **Pentagon.** Here `|lk(s)| = 2`, and both link vertices have a second neighbor. That gives two points of
  `ΛH_s`, two sides each, so 4 singular points per generator. This matches the 4 persistent chains computed exactly
  in `gq-bh-finf-hyp-cone-matching-test.md` (calibration).
- **Petersen graph.** It is 3-regular with girth 5, so every generator has continuum many singular points, and the
  BBMZ host of `W_Petersen` (and of `W_Petersen ∗ Z`) is not bounded.
  - Its boundary is expected to be the Menger curve, with no local cut points. This is recalled, not checked.
  - So a cubulated group whose boundary has the topology of a Kazhdan boundary has an unbounded host.

## Consequence for the Kazhdan program

- **The coincidence is supplied by walls.** In right-angled Coxeter groups every step of the wall tree `T_s` offers
  a crossing wall and a fresh outer wall of the same depth. Singularity is then inherited from the wall's own
  boundary `∂T_s`.
- **A Kazhdan group has no walls.** A group with property (T) has no codimension-one subgroup (Niblo–Roller 1998,
  recalled).
  - So Conjecture U for Kazhdan hyperbolic groups needs a wall-free coincidence mechanism. This proposition cannot
    transfer.
  - The triangle-complex analogue of Theorem D must describe atoms of the chamber graph through vertex-link data
    (the link girths 10, 8, 4 for `𝓗_31`) instead of wall cylinders.
- **Offsets are preferred sets (lemma, trivial).** Take the edge-group elements as generators, so the Cayley graph is
  the chamber graph, and let `a` fix the edge `e_a` of the base chamber `T`.
  - The 5 chambers around `e_a` are pairwise adjacent, so their gallery distances to any `v` differ by at most 1.
  - Hence `f(v) = d(v, aT) − d(v, T) = [aT ∉ P(v)] − [T ∉ P(v)]`, where `P(v)` is the set of chambers around `e_a`
    at minimal distance from `v`.
  - So `F'_a` is the set of boundary points whose fiber sees two preferred sets. This is the starting point for the
    analogue, which is open.

## Lesson for general BH

- **Walls make singular sets large, and walls are what (T) forbids.** In cubulated hyperbolic groups, the BBMZ host
  is unbounded through walls with non-elementary stabilizers (proved here for standard generators of girth-5
  right-angled Coxeter groups). The recurrent coincidence of Theorem D is then
  automatic along every ray of the wall tree.
- **So for Kazhdan groups the bounded-host question is genuinely open.** Neither boundary topology (the countable-sets
  lemma) nor the cubulated mechanism settles it. A wall-free description of horofunction atoms is the missing
  input.
