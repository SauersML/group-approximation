---
rg: 2
id: counter-machine-hosts-have-no-distorted-elements
kind: claim
title: "Reversible counter-machine groups (piecewise translations of Z^N x E read off eventually periodic coordinate colourings) have no distorted elements, in every dimension N, so they contain no H_3(Z), no BS(1,m), no SL_3(Z) and no mV"
distinct_from:
  heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs: that kills orbit graphs of at most quadratic growth by counting; this kills a host class of every dimension N, where orbit growth is N and counting says nothing, by using that the pieces are eventually periodic in each coordinate.
  heisenberg-in-mv-reduces-to-zn-subshift-realization: that characterizes product hosts by product-coloured realizations with arbitrary colourings kappa_i; this shows that no product-coloured realization with eventually periodic kappa_i exists in any rank N, so a YES must use colourings with infinitely much tail information.
  fibred-v-towers-in-brin-thompson-groups-are-distortion-free: that shows towers built from V by wreaths are distortion-free; this is a different, coordinate-mixing host class (the displacement in each coordinate may depend on all coordinates), proved distortion-free by induction on the number of deep coordinates.
  brin-thompson-2v-embeds-in-no-zipper-group: that derives undistortion from a zipper action (and is OPEN); this derives it directly from tail periodicity, with no wall space.
  piecewise-translation-z2-enumerations-are-not-fp: that is about finite presentation of near-shift groups of Z^2 enumerations with polyhedral pieces; this is about distortion in coordinate-product pieces of every rank.
artifacts:
  - research/counter-machine-hosts-have-no-distorted-elements-proof.md
---

**ESTABLISHED** (lane proof, elementary, self-contained except the Callard–Salo import used only
in Corollary 3; not independently reviewed).

## Setting

- A **colouring** is a map `κ : Z → W` to a finite set. It is **eventually periodic** if there are
  `T ≥ 0` and `p ≥ 1` with `κ(t + p) = κ(t)` whenever `t ≥ T` or `t + p ≤ −T`.
- Let `N ≥ 0` and let `E` be a finite set. Put `X = Z^N × E`, with `|·|` the sup norm on `Z^N`.
- A bijection `g` of `X` is a **counter-machine map** if there are eventually periodic colourings
  `κ_1, …, κ_N`, a radius `r` and maps `D, G` such that
  `g(z, e) = (z + D(ω), G(ω))`, where `ω = (e, (κ_i(z_i + u))_{i ≤ N, |u| ≤ r})` is the
  radius-`r` window at `(z, e)`.
- `CM(N, E)` is the set of counter-machine maps. It is a group: combine the colourings of two maps
  into one product colouring (still eventually periodic), and note that compositions and inverses
  read larger, but still bounded, windows.
- A **CM-action** of a finitely generated group `Γ = ⟨S⟩` is a homomorphism `Γ → CM(N, E)`.
- `g ∈ Γ` has **sublinear growth** if `|g^n|_S = o(n)`. A **distorted element** is an element of
  infinite order with sublinear growth. The limit `lim |g^n|_S / n` exists by subadditivity, so this
  is the usual notion.

Examples:
- The step map of every reversible multi-counter machine (Minsky/Morita type) that is a total
  bijection of `Z^N × E` lies in `CM(N, E)`. Here `E` is the state set, and the tests are zero tests,
  sign tests and residues of the counters.
- Houghton-type groups of `Z` are in `CM(1, E)`.
- Lamplighter-type groups `Z ≀ Z` are in `CM(2, {pt})`: take `a` to be `z_1 ↦ z_1 + 1`, and `b`
  to add 1 to `z_2` when `z_1 = 0`.

## Statement

**Theorem.** In every CM-action of a finitely generated group, every element of sublinear growth
acts with finite order.

**Corollary 1.** For all `N` and `E`, no finitely generated subgroup of `CM(N, E)` has a distorted
element.

**Corollary 2.** For every `N` and `E`, none of these groups embeds in `CM(N, E)`:
- `H_3(Z)`, because `c = [a, b]` has `|c^M| ≤ 12√M`;
- `BS(1, m)` for `|m| ≥ 2`, because `a^{m^k} = t^k a t^{-k}`;
- `SL_n(Z)` or `GL_n(Z)` for `n ≥ 3`, because they contain `H_3(Z)`;
- any group containing one of these.

In every CM-action of `H_3(Z)`, some power `c^J` with `J ≥ 1` acts trivially.

**Corollary 3.** For `m ≥ 2`, `mV` embeds in no `CM(N, E)`. This uses the Callard–Salo distortion
element, `brin-thompson-mv-contains-a-distortion-element`.

**Corollary 4 (product hosts).** In `heisenberg-in-mv-reduces-to-zn-subshift-realization` (C),
item 2, there is no product-coloured realization of `H_3(Z)` in which every `κ_i` is eventually
periodic, whatever `N` is. Such a realization is exactly a CM-action on `Z^N` with a free orbit.

## Meaning

1. **A heuristic is falsified.** Reversible counter machines with two counters are already
   Turing-universal. The attempt of 2026-09-13 on `heisenberg-group-embeds-in-some-brin-thompson-group`
   ("counter encodings fail") recorded that one natural affine encoding fails. This theorem shows
   that every counter-machine realization fails, for every orbit geometry, every number of counters
   and every finite control. The obstruction is uniform: distortion.
2. **Where a YES must live.** For a construction of `H_3`, `BS(1, m)` or `GL_3(Z)` inside `nV`
   through a product-type host, at least one coordinate colouring must carry unbounded tail
   information. Examples are Toeplitz, Sturmian or full-shift tapes. Unary counters with finitely
   many tests are never enough. This matches Callard–Salo, whose distortion element uses genuine
   tapes.
3. **The proof mechanism.** Deep in the periodic tails, the machine commutes with a lattice. In the
   lattice quotient, a sublinear element must act trivially by induction on dimension. So it
   translates by a fixed lattice vector, and sublinear growth forces that vector to be `0`. What is
   left is a finite box.

## Not covered

- Pieces cut out by non-coordinate semilinear (Presburger) conditions such as `z_1 > z_2`. The same
  induction should run over the strata of the arrangement, but this is not written.
- Tapes that are not eventually periodic. The induction needs finitely many tail models.

**Proof.** `research/counter-machine-hosts-have-no-distorted-elements-proof.md`.
