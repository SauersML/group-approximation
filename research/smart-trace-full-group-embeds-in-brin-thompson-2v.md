---
rg: 2
id: smart-trace-full-group-embeds-in-brin-thompson-2v
kind: claim
title: The topological full group of the SMART trace subshift embeds in Brin's 2V, so a Juschenko-Monod group (finitely generated, infinite, simple, amenable) lies in a finitely presented simple group
requires:
  - aperiodic-full-groups-lift-along-factor-maps
  - brin-thompson-groups-contain-full-groups-of-their-elements
  - derived-full-group-of-cantor-minimal-system-is-simple
  - minimal-cantor-full-groups-are-amenable
distinct_from:
  full-shift-topological-full-group-embeds-in-2v: that is the full group of the full shift, which is not minimal and not amenable; this is the full group of a minimal subshift, whose commutator subgroup is infinite, simple and amenable.
  bs13-embeds-in-brin-thompson-3v: that uses SMART's renormalization inside 3V to build BS(1,3); this uses SMART's minimality in 2V and a factor-lifting lemma to embed a whole topological full group.
  labbe-shift-derived-full-group-is-amenable: that asks whether one Z^2 full group is amenable (towards a finitely presented simple amenable group); this puts a known amenable simple group inside a finitely presented simple, non-amenable, host.
---

**ESTABLISHED** (lane proof below; not independently reviewed). Two inputs are imported without
reading the primary source: minimality and aperiodicity of SMART (read only in Callard–Salo's
statement), and Matui's finite generation theorem. **No priority claimed**: a bounded arXiv search
(queries on "topological full group" with "finitely presented simple" or Thompson or Brin–Thompson,
and all abstracts containing "Boone-Higman") found no earlier embedding of the full group of a
minimal subshift into a finitely presented simple group or into any `nV`.

## Statement

Let `S` be the moving-tape map of the SMART machine of Cassaigne–Ollinger–Torres-Avilés
(4 states `Q`, 3 tape letters `Γ`), a homeomorphism of `Y = Q × Γ^Z`. Let
`tr : Y -> (Q × Γ)^Z`, `tr(y)_t =` (state, letter under the head) of `S^t(y)`, and `X = tr(Y)`
with the shift `T`. Then:

1. `(Y, S)` is topologically conjugate to `(C^2, s)` for an element `s ∈ 2V` acting on all of
   `C^2 = {0,1}^N × {0,1}^N`.
2. `X` is an infinite minimal subshift, and `tr` is a factor map `(Y, S) -> (X, T)`.
3. `[[T]]` embeds in `[[s]]`, which is a subgroup of `2V`.
4. Hence `Γ_SMART := [[T]]'` is a finitely generated, infinite, simple, amenable group contained in
   the finitely presented simple group `2V`. So `Γ_SMART`, `[[T]]` and all their finitely generated
   subgroups satisfy the Boone–Higman conjecture.

## Proof

**Inputs.**
- (I1) SMART is reversible and aperiodic, and "its moving-tape dynamics is a minimal homeomorphism on
  the Cantor space" (Callard–Salo, arXiv:2208.00685v3, §1, quoting COT, J. Comput. System Sci.
  2017). Its head moves at most `O(log t)` cells in `t` steps (same paper, §1; also Jeandel: aperiodic
  machines have zero speed).
- (I2) Moving-tape reversible machines are elements of `2V` after coding (Callard–Salo Lemma
  `lem:TMin2V` and its proof, read from the TeX; Belk–Bleak).
- (I3) Matui, Internat. J. Math. 17 (2006): Theorem 4.9, `[[T]]'` is simple for a Cantor minimal
  system (node `derived-full-group-of-cantor-minimal-system-is-simple`); Theorem 5.4, `[[T]]'` is
  finitely generated when `(X,T)` is a minimal subshift (not re-read).
- (I4) Juschenko–Monod: `[[T]]` is amenable for Cantor minimal systems
  (`minimal-cantor-full-groups-are-amenable`).
- (I5) Brin: `2V` is simple (Geom. Dedicata 2004) and finitely presented (J. Algebra 2005).

**Item 1 (coding).** Choose complete prefix codes `E` of size `|Q|` and `D, D'` of size `|Γ|` in
`{0,1}^*`. Parse `(a, b) ∈ C^2` uniquely as `a = w_1 w_2 ...` with `w_i ∈ D'` and
`b = e v_0 v_1 ...` with `e ∈ E`, `v_i ∈ D`, and let `φ(a,b) = (e; ... w_2 w_1 . v_0 v_1 ...)`
(state `e`, cell `0` holding `v_0`, cell `-i` holding `w_i`). This is a homeomorphism `C^2 -> Y`.
One step of `S` reads the state and a bounded window around the head, rewrites that window and the
state, and shifts the tape by a bounded amount. Under `φ` this replaces a bounded prefix of each
coordinate by another, `(p a', q b') -> (p' a', q' b')`, with finitely many cases (moving a cell
across the head moves one code block from one coordinate to the other). So `s := φ^-1 S φ` is given
by finitely many box maps; it is a bijection because `S` is, so `s ∈ 2V`. This is the argument of
(I2) with the extra prefix code `E` for the state.

**Item 2.** `tr` is continuous and `tr ∘ S = T ∘ tr`, so `X` is a subshift and a factor of `Y`, and it
is minimal because `(Y,S)` is (I1). Suppose `X` were finite, so some `x = tr(y)` has period `p`.
The move and the written letter at time `t` are functions of `x_t`, so the head's displacement is
`p`-periodic in `t` with drift `D` per period.
- If `D ≠ 0`, the head moves `|nD|` cells in `np` steps, contradicting the `O(log t)` bound (I1).
- If `D = 0`, the head stays in a finite window `W` for all `t >= 0`, so the forward orbit of `y`
  lies in the finite set of configurations that agree with `y` off `W`. Then `S^a y = S^b y` for some
  `a < b`, and injectivity gives `S^(b-a) y = y`, contradicting aperiodicity (I1).
So `X` is infinite; being minimal, it has no periodic points.

**Item 3.** By `aperiodic-full-groups-lift-along-factor-maps` applied to `tr`, `[[T]]` embeds in
`[[S]] ≅ [[s]]`. By `brin-thompson-groups-contain-full-groups-of-their-elements` with `U = C^2`,
`[[s]] ≤ 2V`.

**Item 4.** (I3) gives finite generation and simplicity, `X` infinite gives `[[T]]'` infinite, (I4)
gives amenability, and (I5) gives the host.

## What it adds

- A Juschenko–Monod group (the first known kind of finitely generated infinite simple amenable
  group) inside a finitely presented simple group. Groups of intermediate growth were already known
  to be there (Röver), but no topological full group of a minimal subshift was, in the bounded search.
- `2V` contains a minimal homeomorphism of the Cantor square (item 1), and hence finitely generated
  amenable groups that are not elementary amenable.
- The mechanism is general: every aperiodic factor of `(U, g)`, for `g ∈ nV` and `U` clopen and
  `g`-invariant, has its full group inside `nV`. See
  `decidable-minimal-subshift-full-groups-satisfy-boone-higman` for the class this could reach.
