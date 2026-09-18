---
rg: 2
id: efficient-branch-selector-on-proved-2to1-instances
kind: claim
title: The proved imperfect-completeness 2-to-1 Grassmann instances admit a polynomial-time orientation whose YES lifts have value near 1
distinct_from:
  unique-games-conjecture: that asks for some reduction to near-1 versus near-0 unique games; this fixes the vertex set, constraint graph and soundness proof to those of the proved Khot--Minzer--Safra 2-to-1 instances and asks only for a per-edge branch bit, so it can fail while UGC holds.
  rich-2to1-games-conjecture: that demands a rich pairing law; this mentions no pairing law at all, since by orientation-lifts-sandwich-2to1-game-values richness and soundness are supplied for free once a selector exists.
  smooth-design-rich-2to1-hardness: that asks an outer PCP to realize t-wise uniform smooth pairing laws; this keeps the F_lin pairings of the proved instances and moves all open content into the completeness of a right bit.
  finite-moment-pairing-2to1-hardness: that bounds an average overlap count of sampled matchings; this is a completeness statement about branch statistics of YES labellings, and it implies that claim through the smooth-design route.
  unique-constraints-orient-at-most-half-of-a-fiber: that caps local unique gadgets at completeness one half; this asks for a globally computed orientation on a doubled right alphabet, where item (1) of the sandwich proves the random-bit floor one half and nothing caps it.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that kills affine-view verifiers with oblivious completeness; an orientation lift has no honest right label that is a view of one outer label, since its right bit depends on the edge, so it lies outside that theorem's hypotheses.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that evaluates the branch-blind coarsening on these instances; a selector must read exactly the branch information that coarsening discards.
artifacts:
  - experiments/orientation-lift-2026-09-17/check_orientation_lift.py
---

**OPEN.**

*Instances.* For `eta > 0` let `R_eta` be the polynomial-time reduction behind the
2-to-1 form of `two-to-two-games-theorem` (source footnote 2). It maps a 3LIN
instance to a bipartite 2-to-1 game `G = R_eta(x)` with `Gap-2-to-1[1-eta, eta]`.
Concretely these are the folded Dinur--Khot--Kindler--Minzer--Safra Grassmann
games described in `grassmann-composed-2to2-coarsenings-are-satisfiable`. An
A-class `(U, L)` with `dim L = l` joins a B-vertex `(V, L')` with `L' < L` of
codimension 1, and the constraint is restriction of the unfolded functional.

*Statement.* There is a function `eta'(eta) -> 0` as `eta -> 0` such that for every
`eta > 0` there is a polynomial-time orientation `o` of the edges of `R_eta(x)`
(item 5 of `orientation-lifts-sandwich-2to1-game-values`) with

```text
val( U_o(R_eta(x)) ) >= 1 - eta'(eta)      for every YES input x.
```

By item (5) of the sandwich, every orientation has the form
`o_e(s) = u_e(s)(x_e) xor g_e(u_e(s)|_(L'))`. Here `x_e in L \ L'` is fixed,
`u_e` is unfolding and `g_e` is arbitrary. So the statement asks this: on YES
instances, some near-satisfying labelling has, at the typical B-vertex, its
values on the **new directions** `x_e` of the neighbouring `l`-spaces predictable
up to one bit per B-vertex, by a polynomial-time rule `g_e` of what the B-vertex
sees.

**Why this is a genuine prerequisite.**

* **Sufficient.** Route `rich-2to1-via-branch-selector-on-proved-2to1-instances`
  derives `rich-2to1-games-conjecture` from this claim together with two
  established nodes. Route `smooth-design-rich-2to1-via-branch-selector` derives
  `smooth-design-rich-2to1-hardness`, and through the existing
  `finite-moment-hardness-from-smooth-design` it derives
  `finite-moment-pairing-2to1-hardness`.
* **Can fail on its own.** It concerns one fixed instance family. UGC could hold
  through a different outer construction while every polynomial-time `g_e` on
  these instances leaves the minority-branch mass bounded below. The selector
  must use the 3LIN right-hand sides only through `g_e`. By item (3) of the
  sandwich, the lift loses exactly that minority mass.
* **Graded.** Item (1) of the sandwich gives `val(U_o) >= (1 - eta)/2` for every
  `o`. A selector with YES lift value `>= c > 1/2`, uniformly in `eta`, already
  proves `Gap-UG[c, eta]` and `Gap-Rich-2-to-1[c, 2 eta]` NP-hard (consequence
  (a)). That is past the best recorded unique games gap
  `unique-games-hard-at-completeness-one-half`. So the first falsifiable
  milestone is any constant bias above `1/2`.

**Not already killed.**

* `linear-view-unique-verifiers-collapse-to-quotient-coarsening` and
  `grassmann-composed-2to2-coarsenings-are-satisfiable` kill affine-view
  verifiers with oblivious completeness. Its right bit changes with the edge, so
  it is not a view of the B-label or of any single A-label, and the collapse
  hypotheses fail.
* `left-preserving-local-richness-wrappers-are-affine-ug-merges` covers
  wrappers that add rich right vertices under affine local certificates. Here
  the richness comes from `Psi` after the lift, and the certificate question is
  replaced by the branch statistic.
* `perfect-completeness-rich-2to1-tractable-skeletons-are-in-p` is silent, since
  completeness is `1 - eta'`.
* Caution. On the honest YES labelling from DKKMS completeness, the branch at
  `e` is `A(x_e) xor g_e(A|_(L'))`. For `x_e` outside `L' + H_U`, `A(x_e)` is not
  determined by the B-label and the folding offsets. If `A` is drawn uniformly
  among linear maps consistent with those data, the new-direction values at
  neighbours with independent `x_e` are independent uniform bits. So their
  branch bias is `0` for every `g_e`. YES instances carry one specific
  assignment, not a random one. A selector must therefore exploit the structure
  of the actual satisfying assignments, the 3LIN right-hand sides, or non-honest
  YES labellings. This is a heuristic warning, not a kill.

## Attempts

* **Random or lexicographic orientation (2026-09-17).** It gives lift value
  `>= (1-eta)/2` and fully rich hardness at completeness one half
  (`rich-2to1-hard-at-completeness-one-half`). By item (1) of the sandwich it
  cannot exceed the floor on instances whose YES branches are balanced. Not a
  solution.
* **High-advantage decoding (2026-09-18).** This attempt is recorded in
  `high-advantage-selector-witnesses-decode-good-outer-labellings`, which is
  ESTABLISHED. At lift value near 1, Markov gives a uniform list-decoding rate
  `2^(-l)/192` at all but `O(xi + zeta + d)` of the target mass. So any outer
  labelling of value `>= 15/16` with a near-honest witness decodes.
  - Corollary A: on DKKMS instances, a polynomial-time orientation whose YES
    lift witnesses are `1/64`-close to a locally honest patchwork of dirt
    `<= 1/64` gives `NP in RP`.
  - Corollary B: this claim together with
    `dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` (OPEN) gives
    `NP in RP`.

  Under `NP not in RP`, this claim therefore requires the local rigidity node
  to fail. That means YES labellings of value arbitrarily close to 1 that are
  far from every patchwork. Not a solution. It is a decomposition into two
  prerequisites that cannot both hold.
* **Planted/NO-coset coupling (2026-09-18).** This attempt is recorded in
  `locally-read-witnesses-are-sound-on-planted-2to1-inputs`, which is
  ESTABLISHED. Take any witness map `Lambda` (orientation plus lift labelling,
  efficient or not) with read sets `S_e`, and any sound right-hand side `b0`.
  Then `E_t val(Lambda(Ht)) <= eta + mu_(b0)`, where `mu_(b0)` is the weight of
  the constraints whose read set `b0` locally refutes (`b0|S_e notin
  Im H_(S_e)`). A YES witness of value `>= 1 - eta'` must therefore read
  `b0`-refuting parity cycles on `>= 1 - eta' - eta` of the mass, for every
  sound `b0`. Tree-like reads are capped at `eta + w_cyc`. Need `207b4529` is
  reduced, not refuted: any class labelling realising it must encode
  cross-member parity cycles on its class read sets. Not a solution.
