---
rg: 2
id: cantor-cone-phase-atom-comparison-is-depth-uniform
kind: claim
title: "Cone-phase atom transport in C(C,Z) ⋊ V is depth-free: for an ε-almost invariant spectral law the atom μ{χ[U] = 0} differs from μ{χ[[0]] = 0} by O(ε) with a constant that does not grow with the depth of the proper nonempty clopen set U"
distinct_from:
  cantor-central-witnesses-have-active-cone-phases: that is the atom comparison `μ{χ[C]=0} ≥ 4μ{χ[U]=0} − 3 − Kε` with `K` absolute; its route proves only the form carrying an extra `16|h|_S ε`, where `h ∈ V` carries `[0]` to `U`. This is the one missing ingredient — a transport estimate whose constant does not grow with `|h|_S` — and it is what the "for every proper clopen `U`, `K` absolute" quantifier of that headline needs.
  cantor-central-witnesses-have-long-range-dependence: that lower-bounds the conditional TV-dependence of two cone phases, and its constants are likewise allowed to grow with the word lengths of the moving elements; this asks for the opposite, a transport bound with no word-length dependence at all, and says nothing about dependence.
  cantor-integer-maps-central-growth-criterion: that converts central growth into the existence of almost invariant spectral laws with no `1_C`-invariant vector; this is a quantitative uniformity statement about any one such law, and asserts no existence.
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

**OPEN.**

## Statement

Notation as in `cantor-central-witnesses-have-active-cone-phases`: `C = {0,1}^N`, `A = C(C,Z)`,
`G = A ⋊ V`, `S = S_V ∪ {±1_{[0]}}` the generating set of artifact §3(c), `π` a unitary
representation of `G`, `ξ` a unit vector with `ε = max_{s∈S}‖π(s)ξ − ξ‖`, and `μ` its
`A`-spectral law on `Â = Hom(A,T)`.

**Question.** Is there an absolute constant `K_0`, independent of `π`, of `ξ` and of `U`, with

  `|μ{χ[U] = 0} − μ{χ[[0]] = 0}| ≤ K_0·ε`

for every proper nonempty clopen `U ⊆ C`?

## Why it is needed

Transitivity of `V` on proper nonempty clopen sets (artifact §3(a)) gives `h ∈ V` with
`h[0] = U`, and the spectral TV estimate (artifact §3(f), third bullet) transports the atom at
cost `O(|h|_S·ε)`. That is the only transport available in the graph today, and `|h|_S` grows
with the depth of `U`: for `U = [w]` the best available bound is `|h_w|_S ≤ c(|w| + 1)`. So the
transported statement degrades as `U` gets deep, and a bound uniform over *all* proper clopen
`U` at a fixed `ε` does not follow.

This is exactly the gap that returned `cantor-central-witnesses-have-active-cone-phases` to
OPEN on 2026-09-18: its route proves

  `μ{χ[C] = 0} ≥ 4·μ{χ[U] = 0} − 3 − 40Lε − 16|h|_S ε`,

while the claim's headline states the same inequality with a single absolute `K`. With a
depth-free transport estimate the headline follows at once. Without one, the honest form of
every downstream consequence is restricted to cones of depth `o(1/ε)`, which is how
Corollary 2 of that node is in fact stated.

## Stakes both ways

- **Established:** the cone-phase atom `p = μ{χ[U] = 0}` becomes a genuine scale-free invariant
  of a witness law, and the uniform-in-`U` headline of
  `cantor-central-witnesses-have-active-cone-phases` follows. Every class-kill on
  `cantor-integer-maps-central-direction-has-relative-t` phrased as "the phase of a fixed cone"
  would then reach all depths simultaneously, not only depths `o(1/ε)`.
- **Refuted:** the cone-phase atom is not scale-free, and there is a witness law whose activity
  genuinely decays with depth. That is itself a strong structural statement about the surviving
  diffuse witnesses, and it caps every cone-phase kill on this node at depth `o(1/ε)`
  permanently.

## Attempts

- **2026-09-18 (e2-land-w2-nv-relative-t): recorded as the gap; the obvious attack dies.** The
  only transport in the graph is Lemma 1 of
  `cantor-central-witnesses-have-active-cone-phases-proof`: telescoping `h = s_1⋯s_n` along the
  generating set gives `‖π(h)ξ − ξ‖ ≤ |h|_S·ε` and then `D(h) ≤ 2|h|_S ε` from the spectral TV
  estimate. The telescoping is where the depth enters, and nothing in the argument recovers it:
  `ε` controls one generator at a time, so a group element of word length `n` is only controlled
  to `nε`. Getting a depth-free bound needs a transport that is not a word in the generators —
  for instance an averaging argument over the `V`-orbit of `[0]`, or a direct fixed-point
  estimate for the `V`-action on the atom function `U ↦ μ{χ[U] = 0}`. Neither is available:
  `U ↦ μ{χ[U] = 0}` is not known to be continuous for any topology `V` acts on equicontinuously,
  and `V` is not amenable, so no invariant mean is available to average against.
