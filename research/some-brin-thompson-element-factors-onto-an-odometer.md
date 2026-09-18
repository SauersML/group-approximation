---
rg: 2
id: some-brin-thompson-element-factors-onto-an-odometer
kind: claim
title: For some k and m >= 2, some element of the Brin-Thompson group kV has the m-adic odometer as a topological factor
distinct_from:
  renormalizable-thompson-elements-are-odometer-codes: that proves every renormalizable element has such a factor; this asks whether any element of any kV has one at all.
  bs12-embeds-in-brin-thompson-2v: that asks for BS(1,2) in some nV; a negative answer here kills only the renormalization route to it, and a positive one does not give BS(1,2).
  three-v-contains-aperiodic-rationals: that uses a periodic-point-free SMART element of 2V; this asks whether some such element has continuous eigenvalues of unbounded order.
---

**OPEN.** There are `k >= 1`, `m >= 2`, `T ∈ kV` and a continuous surjection
`π: C^k -> Z_m` with `π ∘ T = π + 1`. Equivalently, for every `j` the space
`C^k` is split into `m^j` clopen sets that `T` permutes cyclically.

**Why it is a hole.** `renormalizable-thompson-elements-are-odometer-codes` proves
this is necessary for the renormalization route
(`renormalizable-thompson-elements-give-baumslag-solitar`) to
`bs12-embeds-in-brin-thompson-2v`. So a negative answer kills that route for
every `k` and `m`.

**Known constraints on a witness.**
- `T` has no periodic points, since `m^j` divides every period.
- This excludes the topological full group of the full shift, whose elements fix
  the constant configurations.
- Candidates must be periodic-point-free, such as SMART-type machines in `2V`
  (`three-v-contains-aperiodic-rationals`).

**Lead.** In Callard--Salo (arXiv:2208.00685v3) the level moves of SMART take
`f(k+1) = 3 f(k) + 4` steps. A SMART-type machine with exact tripling
`f(k+1) = 3 f(k)` is the natural candidate both for this claim and for a height-3
renormalization. Whether SMART itself has continuous eigenvalues was not
checked.

## Attempts

- 2026-09-17 (lane gq-nv-obstruct). **Not decided.** Four results and one tool.
  - *Necessary conditions*, `odometer-factor-witnesses-mix-coordinates` (ESTABLISHED). Every power of a
    witness is periodic-point-free, because `Z_m` is torsion-free. So no power lies in any `kV`-conjugate
    or coordinate-permutation image of the triangular subgroup `T_k`: triangular elements always have
    periodic points. In particular `k = 1` is impossible (`T_1 = V`), and a witness must mix
    coordinates.
  - *One-way machines die.* Suppose the head only ever moves one way along a coordinate, as in a
    Turing machine `τ ∘ β` that moves right at every step. Then the cells it leaves behind are frozen.
    On a constant input, its bounded active window runs through a finite automaton, so the window's
    period is bounded independently of the scale `j`. But `π mod m^j` must read the time `n mod m^j`
    from a window of bounded radius. That is a contradiction for large `j`. By the same argument, one
    coordinate alone cannot count: a deterministic pushdown run on unary input has an ultimately
    periodic top window. So the counting must use at least two coordinates as two-way memory, as in a
    Turing machine. This is a lane argument, not written as a node.
  - *Tool*, `brin-thompson-first-return-maps-lie-in-kv` (ESTABLISHED). The first-return map of an
    element of `kV` to a clopen set with bounded return times is, up to a brick-local conjugacy, again
    an element of `kV`. So SMART's per-level overhead can be deleted by inducing, provided the overhead
    configurations form a clopen set with bounded runs and removing them leaves the level moves exactly
    tripled. The candidate is then an element of `2V` with `f(k+1) = 3 f(k)` exactly.
  - *SMART itself.* SMART's moving-tape map `F ∈ 2V` is minimal and periodic-point-free, and its
    column shift is substitutive (Cassaigne–Ollinger–Torres-Avilés). The substitution was not
    obtained: the HAL and publisher pages refused access. Heuristic, not a proof: if the level lengths
    are `3^n c_a − 2` with the constant from `f(k+1) = 3f(k)+4`, Host's eigenvalue criterion is
    violated for `e^{2πi/3^j}` unless a coboundary absorbs the `−2`. So the exactly tripled induced map
    is the better candidate.
  - *Next step.* Read SMART's substitution from the arXiv e-print source of Callard–Salo
    2208.00685v3 (`distortion-1-smart.tex`, which lane e-nv-walls already read for the transition
    table). Then test whether the "turn" steps are locally recognizable. Inducing on their complement
    gives a constant-length-3 substitution in the column shift. By Dekking's theorem, a primitive
    aperiodic constant-length-3 substitution has `Z_3` in its maximal equicontinuous factor, and that
    would answer this claim YES.
