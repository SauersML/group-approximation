---
rg: 2
id: brin-thompson-2v-embeds-in-no-zipper-group
kind: claim
title: "No group with a zipper action contains a distorted element, so 2V embeds in no SFT full group, no locally finitely determined group of local similarities and no group acting properly on a space with walls"
distinct_from:
  brin-thompson-mv-contains-a-distortion-element: that imports the Callard--Salo distortion element and their corollary that mV acts properly on no CAT(0) cube complex; this is the non-embedding of 2V into every group that Matui's and Hughes's zipper theorems cover, which is where the transplant of those theorems to nV dies.
  cubical-coset-proper-actions-capture-distorted-elements: that proves the bounded-or-linear dichotomy for commensurating actions and capture modulo a subgroup; this applies its item 1 to zipper actions and turns it into a non-embedding statement about named groups.
  brin-thompson-brick-charts-are-not-commensurated: that shows one concrete family of brick charts is not commensurated by nV; this shows that no zipper action on any set exists on any group containing 2V, whatever the charts.
  brin-thompson-nv-no-cubical-action-proper-mod-triangular: that forbids commensurating actions proper modulo an undistorted subgroup of nV; this is the case H = 1 transported to overgroups, stated for the zipper-action class of Matui and Hughes.
  sft-topological-full-groups-have-the-haagerup-property: that is Matui's positive theorem for SFT full groups; this says the positive theorem cannot reach 2V by embedding it into an SFT full group.
  input-encoded-sft-groupoid-hosts-are-not-universal: that excludes infinite Kazhdan groups from SFT full groups through the Haagerup property; this excludes 2V through distortion, where the Haagerup property gives no obstruction.
  baumslag-gersten-embeds-in-no-graph-almost-automorphism-group: that is a non-embedding of a different group into a different host class.
---

**OPEN** (demoted 2026-09-18 at landing: the referee stage returned no votes for this
result, so it has not survived review). The candidate proof is kept as the attempt artifact
`research/artifacts/brin-thompson-2v-embeds-in-no-zipper-group-proof-2026-09-18.md`. Not independently reviewed.

**Zipper action** (Hughes, arXiv:0804.0610, Definition 5.1, verbatim): "A discrete group
Γ has a zipper action if there is a left action Γ↷E of Γ on a set E and a subset Z⊆E
such that (1) for every g∈Γ, the symmetric difference gZ △ Z is finite, and (2) for every
r>0, {g∈Γ | |gZ△Z| ≤ r} is finite."

**Theorem.**

1. If a group `G` has a zipper action, then every infinite-order element of `G` is
   undistorted in every finitely generated subgroup of `G` that contains it.
2. For every `m ≥ 2`, the Brin–Thompson group `mV` embeds in no group with a zipper
   action. In particular `mV` is isomorphic to no subgroup of:
   - the topological full group `[[G_A]]` of any one-sided irreducible shift of finite
     type (Matui, arXiv:1210.5800, Theorem "Haagerup": "The action φ:[[G]]↷Ω is a zipper
     action");
   - any locally finitely determined group of local similarities of any compact
     ultrametric space (Hughes, Theorem ZipperExistence);
   - any group acting properly on a space with walls (Hughes–Farley appendix: "A
     discrete group Γ has a zipper action if and only if Γ acts properly on a space with
     walls").

Item 2 for proper actions on CAT(0) cube complexes is Callard–Salo's Corollary 1.2. The
cases of SFT full groups and of local-similarity groups follow from that corollary only
through the Sageev and Chatterji–Niblo/Nica cubulation of wall spaces. The proof here is
direct and uses only the dichotomy of `cubical-coset-proper-actions-capture-distorted-elements`.

## What this settles for the nV lane

The assignment "transplant Matui's SFT zipper, Hughes's local similarities or the
Lehnert/Farley zipper cocycle to `G_2^n`" is a single class. Every proof in it produces a
zipper action, and none can exist on `nV`.

- **Invariant.** Growth of `|f^N Z △ Z|` along the Callard–Salo element `f`, with
  `|f^N| = O(log^4 N)`.
- **Step where every member dies.** Matui's counting step (b) (arXiv:1210.5800,
  l.2134–2143): "φ_α([C_λ])=[WC_λ] is in Z if and only if there exists i such that C_λ
  is contained in C_{ν_i}", hence "#(Z∖φ_α^{-1}(Z)) … does not exceed the number of
  admissible words of length less than m(α), and hence is finite". The lower bound
  "≥ m(α)−1" is what gives properness.
  - **Dictionary to `G_2^n`.** `Ω_n` is the set of compact open `G_2^n`-sets with brick
    source, modulo right multiplication by products `U_{μ_1,ν_1} × … × U_{μ_n,ν_n}`.
    `Z_n` is the set of classes of bricks, and `α` acts by left multiplication by its
    bisection.
  - **Where the dictionary breaks.** The analogue of "C_λ not contained in any C_{ν_i}"
    is a brick `C_{λ^1} × … × C_{λ^n}` not contained in a piece. That forces only one
    coordinate to be short, say `|λ^1| < m(α)`, and leaves `λ^2, …` free. So step (b)
    counts infinitely many broken bricks, which are the codimension-one faces of
    `brin-thompson-brick-charts-are-not-commensurated`.
  - **No repair exists.** Item 2 of the Theorem shows that no other choice of `(Ω, Z)`
    works: a zipper action has `|f^N Z △ Z| ≥ N − C` for large `N`, but it is also at
    most `K |f^N|_L = O(log^4 N)`.
- **Consequences.**
  - Hughes's theorem cannot reach `nV` through any compact ultrametric structure on
    `C^n`, whatever metric is chosen. This settles the "not as stated" bullet on local
    similarities in `brin-thompson-groups-nv-are-a-t-menable`.
  - Matui's theorem cannot reach `nV` by embedding it into an SFT full group.
  - A Haagerup proof for `nV` needs a cnd function `ψ` with `ψ(f^N) → ∞` but
    `ψ(f^N) = O(log^8 N)`. No integer-valued wall count can do this. Only measured walls
    with non-atomic transverse measure, or a non-combinatorial cocycle, remain.

## Attempts

- **2026-09-18, zipper action as a commensurating action proper modulo the trivial
  subgroup (swarm-0917 e-land-nv-affine).** The worker's route (bounded-or-linear
  dichotomy of `cubical-coset-proper-actions-capture-distorted-elements`, restricted to
  the Callard--Salo distortion element of `2V`) is kept as the attempt artifact
  `research/artifacts/brin-thompson-2v-embeds-in-no-zipper-group-proof-2026-09-18.md`.
  Referee reason for demotion: no referee votes were returned for this established
  result (votes lost), so it did not survive review. Restore the route once a full
  referee pass survives.
