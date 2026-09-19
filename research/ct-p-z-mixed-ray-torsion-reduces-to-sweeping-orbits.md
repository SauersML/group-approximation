---
rg: 2
id: ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits
kind: claim
title: "Kourovka 19.46 on the mixed-sign ray: a finitely generated subgroup of CT_P(Z) with slopes in one γ^Z, γ and 1/γ non-integral (e.g. (3/2)^Z), is finite iff every point has a frozen tail iff it has finitely many slopes; a drifting return to an intersecting cylinder has infinite order; so an infinite periodic example needs an orbit whose tails sweep whole level segments"
distinct_from:
  periodic-k-graph-subgroups-with-ray-cocycle-are-finite: that settles the positive ray by pumping and nested cylinders; on a mixed-sign ray cylinders never nest, pumping fails, and this node records what survives.
  ct-p-z-mixed-ray-frozen-tails-force-finite-orbits: that is the orbit statement (Kourovka 20.44); this is the group statement (Kourovka 19.46).
  brin-thompson-2v-is-torsion-locally-finite: that is the open 2V barrier; this is its arithmetic, moving-head analogue in CT_P(Z).
---

**ESTABLISHED** (lane proof, not reviewed). Elementary. No priority claimed.
- **What is proved.** Items 1–3.
- **What stays open.** Kourovka 19.46 itself (S. Kohl: does CT(Z) have finitely generated infinite
  periodic subgroups?) stays **OPEN**, including on the mixed-sign ray.
- **The positive ray** is already done: bh-kourovka,
  `periodic-k-graph-subgroups-with-ray-cocycle-are-finite`.

## Setting

As in `ct-p-z-mixed-ray-frozen-tails-force-finite-orbits`:
- `H = ⟨S⟩ ≤ CT_P(Z)`, `P` finite, with tables of depth `D`;
- every piece has degree change in `Zv`, with `v` of mixed sign;
- tails, reading, frozen (non-consumable) degrees and `A(n)` are defined there.

The *cocycle* is `c(h, x) = t`, where `h` has slope `γ^t` at `x`.

## Theorem

1. **Finiteness criterion.** The following are equivalent:
   - (a) `H` is finite;
   - (b) the cocycle is bounded, i.e. `H` has only finitely many slopes;
   - (c) every point of `Ẑ` has a frozen tail.
2. **Periodic groups.** Let `H` be periodic.
   - Along each orbit `O = H·x`, `f(hx) = c(h, x)` is a well-defined *potential*, and
     `c(g, y) = f(gy) − f(y)`.
   - `H` is infinite iff some orbit has unbounded potential. By (c), such an orbit reads
     every depth: its tails *sweep* whole level segments.
3. **Hyperbolic returns.** Assume `v_p ≠ 0` for every `p ∈ P ∪ {2}` (true for `(3/2)^Z` in
   `CT_{{3}}(Z)`). Suppose `h ∈ CT_P(Z)` maps a cylinder `Z(τ)` onto a cylinder `Z(τ')` by one
   canonical map, with `d(τ') = d(τ) + rv`, `r ≠ 0` and `Z(τ) ∩ Z(τ') ≠ ∅`. Then `h` has a fixed
   point with slope `γ^r` there, and so `h` has infinite order.

## Proof

**1.**
- **(a) ⇒ (b).** A finite group has finitely many slopes.
- **(b) ⇒ (c).** Let `|c| ≤ B` on `H`. Choose `n` with `n_p ≥ D + B|v_p|` for all `p`.
  - Along any word, every prefix is an element of `H`, so the tail at `n` stays at degrees
    `n + tv` with `|t| ≤ B`. All of these are `≥ D·1`.
  - So no move reads it, and `n` is frozen at every point.
- **(c) ⇒ (a).** The sets `Y_n = {x : n frozen at x}` are clopen, since consumability of `n`
  depends on `x mod m_n Π^D`.
  - By compactness, finitely many of them, `Y_(n_1), …, Y_(n_r)`, cover `Ẑ`.
  - By item 1 of the frozen-tails node (its proof works for every point of `Ẑ`), every orbit
    on `Ẑ` has at most `A = max A(n_i)` points.
  - A finitely generated group has only finitely many subgroups of index `≤ A`, and all point
    stabilizers are among them. Their intersection is a normal subgroup of finite index that
    fixes `Ẑ` pointwise, so it is trivial, and `H` is finite. ∎
- **Where mixed sign is used.** Only in (c) ⇒ (a), through the finite segments that bound
  orbits of frozen points.
  - On a positive ray, frozen tails travel, and frozen points can have infinite orbits, e.g.
    the lines of `00 ↦ 0`, `01 ↦ 10`, `1 ↦ 11` in `V`.
  - That element is not frozen at its fixed point `0^∞`, where `00 ↦ 0` reads every depth.
    So it is no counterexample to (c) ⇒ (a) there.

**2.**
- **Well-defined.** If `hx = h'x`, then `k = h^(-1)h'` fixes `x` and has finite order `N`.
  - Its germ at `x` is `y ↦ x + γ^t(y − x)`, with `t = c(k, x)`. So `k^N = 1` forces `γ^(tN) = 1`,
    i.e. `t = 0`.
  - This is the germ fact of the CT(Z) cluster: germ groups at points of `Ẑ` are torsion-free.
    It is also the orbitwise-coboundary statement of `brin-thompson-torsion-has-clopen-fixed-sets`.
  - The cocycle identity gives the rest.
- **The equivalence.** The cocycle is bounded iff every potential is bounded, since
  `c(h, x) = f(hx) − f(x)` with base point `x`. Now use 1. ∎

**3.** Write `Z(τ) = ∏_p B_p`, a product of `p`-adic balls. On `Z(τ)`, `h` is
`A(y) = s + γ^r (y − r_τ)` in every coordinate, and `A(B_p) = B_p'` intersects `B_p`.
- **`r v_p > 0`.** `|γ^r|_p < 1`, so `B_p'` is a smaller ball meeting `B_p`, hence
  `B_p' ⊆ B_p`. `A_p` is a contraction of `B_p` into itself and has a fixed point `y*_p ∈ B_p`.
- **`r v_p < 0`.** `B_p' ⊇ B_p`, so `A_p^(-1)` maps `B_p` into itself as a contraction and again
  gives `y*_p ∈ B_p` with `A_p(y*_p) = y*_p`.
- **Conclusion.** `y* ∈ Z(τ)` and `h(y*) = y*`.
  - For `y ≠ y*` close enough to `y*`, `h^N(y) = y* + γ^(rN)(y − y*) ≠ y`.
  - So `h^N ≠ 1` for all `N ≥ 1`. ∎

## Why pumping stops here

- **The positive-ray proof.** Pumping takes record times of the height `Σ c`. Two of them land
  in one cylinder of a fixed degree `E`, and the subword maps that cylinder onto a nested
  subcylinder. This is the contraction lemma.
- **The mixed-sign replacement.** Item 3 replaces nesting by intersection plus a hyperbolic
  fixed point. But it needs the subword to act on `Z(τ)` by *one* canonical map, i.e. the tail
  at `E` must not be read in between.
- **The window.** On a mixed ray, an excursion of height `W` reads the tail unless `E` exceeds
  `W|v|` in the shrinking coordinates. Then the number of degree-`E` cylinders grows like
  `c^W`, while a band of width `W` supplies only about `W/K` record times.
- **Same obstruction as `2V`.** This is exactly the second-stack failure of bh-free-06's pumping
  in `2V` (`brin-thompson-2v-is-torsion-locally-finite`, Attempt 1).
- **Moving heads.** The mixed-sign ray is the arithmetic moving-head regime. A level segment
  `e_2 + e_3 = L` is a tape of length `L`, and the drift is the head. Barbieri–Kari–Salo
  (arXiv:2303.17270) prove the torsion problem undecidable for elementary Turing machines.

**So 19.46 on the mixed ray is equivalent to this:** find, or exclude, a finitely generated
periodic group whose orbit tails sweep level segments without ever making a drifting return
within the returning element's own reading depth.

## Lesson for general BH

**Torsion in full groups is governed by returns.**
- **Positive drift.** Returns nest, so they give infinite order (contraction), and pumping
  finds them. Tame.
- **Mixed drift.** Returns only intersect. They still give infinite order through a
  hyperbolic fixed point, but pumping cannot find them at a fixed resolution. This is the
  moving-head (2V, Turing-machine) regime.

**For Burnside-type BH hosts.** Infinite periodic groups can only live where returns are
invisible at bounded resolution: rank-two cocycles, or mixed-sign drift with sweeping orbits.
A construction should aim at head-sweeping dynamics, not at positive drift.
