---
rg: 2
id: kms-2to2-instances-are-padded-dkkms-selector-lecs
kind: claim
title: The proved Gap 2-to-2 instances are a linear 2-to-2 presentation of the DKKMS folded Grassmann game carrying (E) tau = 2^(l-1-2k), (M) K = 1 and (B) unchanged, so the honest-witness selector kill covers 2-to-2 selectors too
distinct_from:
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that checks (E), (M) and (B) for the DKKMS 2-to-1 game G_folded and its multi-edge form, and explicitly leaves the 2-to-2 instances untreated; this settles the 2-to-2 side by showing there is no separate 2-to-2 instance family in the literature, exhibiting the single missing presentation map (a free bit on Sigma_B) that neither paper writes, and checking that a 2-to-2 selector -- which gets both a matching choice per K_(2,2) block and a free seed bit, and which cannot be converted into a 2-to-1 selector -- is killed by running the decoder on the padded game directly.
  two-to-two-games-theorem: that is the imported statement of Theorem 1.4 of ECCC TR18-006, a hardness gap; this reads the same paper for its instances, finds none, traces them to ECCC TR16-198 Section 4.2, and annotates them, proving nothing about the gap itself.
  efficient-branch-selectors-list-decode-honest-outer-labels: that proves the decoding theorem for the abstract LEC class and records instance membership as an unchecked argument; this is a membership check against the paper text for the 2-to-2 presentation.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that builds gauge labellings of a branch-blind coarsening of the folded Grassmann instances to kill affine-view unique verifiers; this changes no constraint, only the right alphabet's size, and concerns orientation lifts rather than coarsenings.
  rich-2to1-hard-at-completeness-one-half: that uses the 2-to-2 theorem as a black box to get a fully rich 2-to-1 gap at completeness one half; this opens the box and annotates the instances.
artifacts:
  - experiments/kms-2to2-padding-2026-09-18/check_kms_2to2_padding.py
  - research/artifacts/kms-2to2-instance-provenance-2026-09-18.md
  - research/artifacts/kms-2to2-padding-attempt-2026-09-18.md
---

**OPEN.** Let `G_2:2` be the instance family that Theorem 1.4 of ECCC TR18-006
is about. The claim is that `G_2:2` is a presentation of the DKKMS folded
Grassmann game `G_folded` of ECCC TR16-198 Section 4.2 for which hypotheses
(E) and (M) of `efficient-branch-selectors-list-decode-honest-outer-labels`
hold with `tau = 2^(l-1-2k)` and `K = 1`, and (B) holds for every orientation
lift, so that the honest-witness selector kill covers 2-to-2 selectors.

This is the 2-to-2 half of live need `1cb0e45a`. The 2-to-1 half is
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`, which ends with
"**Not covered.** The KMS 2-to-2 instances, and any other composition, are not
treated." That half is settled; this one is **not**.

**Status, 2026-09-18.** This file was landed as ESTABLISHED with route
`kms-2to2-padding-selector-membership-proof`. All three referee lenses refuted
it at Part 1, the citation step, and the claim was returned to OPEN; the route
was demoted to
`research/artifacts/kms-2to2-padding-attempt-2026-09-18.md` and establishes
nothing. The reason is recorded under `## Attempts` below. **Parts 1 and 3 of
the text that follows are the refuted material and are kept only as the record
of the attempt.** Parts 2 and 4 survive as a theorem about the self-constructed
padded game `G_pad`, not about `G_2:2`.

## Part 1: there is no separate 2-to-2 instance family (citation) -- REFUTED

**This part is wrong.** See `## Attempts`. Reference `[12]` of TR18-006, never
examined below, is Khot--Minzer--Safra, *On Independent Sets, 2-to-2 Games and
Grassmann Graphs*, ECCC TR16-124, and it does construct a 2-to-2 game. The
enumeration below is therefore incomplete and its conclusion is unsupported.
The original text follows unchanged.

Khot, Minzer and Safra, *Pseudorandom Sets in Grassmann Graph have
Near-Perfect Expansion*, ECCC TR18-006, **constructs no game**. It proves the
Grassmann Expansion Hypothesis and nothing else. Verbatim:

* Abstract: "We prove that pseudorandom sets in Grassmann graph have
  near-perfect expansion as hypothesized in [4]. This completes the proof of
  the 2-to-2 Games Conjecture (albeit with imperfect completeness) as proposed
  in [12, 3], along with a contribution from [2]."
* Page 3: "The focus of this paper is the combinatorial hypothesis itself,
  which we are able to prove, in turn proving the 2-to-2 Games Conjecture,
  completing this line of work."
* Appendix C: "In [3], the authors formulated a Linearity Testing Hypothesis
  and showed that it implied the 2-to-2 Games Conjecture (with imperfect
  completeness)."
* Reference "[3] Irit Dinur, Subhash Khot, Guy Kindler, Dor Minzer, and Muli
  Safra. Towards a proof of the 2-to-1 games conjecture? Electronic Colloquium
  on Computational Complexity (ECCC), 23:198, 2016."

Reference [4] (ECCC TR17-094) is about expansion of Grassmann graphs and builds
no game; [2] (Barak--Kothari--Steurer) derives one hypothesis from another. So
**the proved 2-to-2 instances are the DKKMS instances of ECCC TR16-198,
Section 4.2** -- the same family for which (E), (M) and (B) are already
established.

## Part 2: the one presentation step neither paper writes

DKKMS Section 4.2 delivers a bipartite constraint graph with *two alphabets of
different sizes*: "We let `Sigma_A = {0,1}^l` and `Sigma_B = {0,1}^(l-1)`. ...
The constraint between `(U,L)` and `(V,L')` accepts pairs `(sigma,sigma')` iff
`sigma|_(L') = sigma'`. It is clear that this is a `2 : 1` constraint."

KMS Definition 1.3 wants **one alphabet on both sides**: "each constraint is of
the form `T_ij x_i (+) T'_ij x_j in {b_ij, b'_ij}`, `T_ij, T'_ij` are
`l x l` invertible matrices". The only remark on the passage between the two
shapes is footnote 2, which asserts it: "the constraints are easily
reinterpreted as being 2-to-1 constraints". That is the *opposite* direction,
and by the bus lemma of `e2-w2-audit-ugc1` on `two-to-two-games-theorem`
(2026-09-18) the generic per-constraint 2-to-2 -> 2-to-1 bipartization is not
gap preserving, so footnote 2 is not a generic transformation.

**The missing map, supplied here.** Pad the right alphabet with one free bit:

```text
Sigma_B^pad = Fun(L') x F_2  ~  F_2^l,
constraint(C, (V,L')) accepts (sigma, (sigma', c))  iff  A_sigma(U,L)|_(L') = sigma'.
```

Write `G_pad` for the result. Fix a basis `v_1,...,v_(l-1)` of `L'`, extend it
by `v_l = x` to a basis of `L`, and let `r : L -> R` be the folding bijection
`z = r(z) + y(z)`, `y(z) in H_U`, of Lemma 4.1 and Definition 4.2. Then

```text
(T sigma)_i = sigma(r(v_i)),   T' = I,   b_i = h_U(y(v_i)),   b' = b + e_l.
```

**Facts (checked exhaustively by the artifact, `k = 2`, `l = 2, 3`).**

1. The folded constraint is **exactly** 2-to-1, not less: all members of a
   class agree on `L'` (Claim 4.3 of TR16-198 with `D = L'`), so the aggregate
   does not collapse. 161280 and 2580480 triples, 0 splits.
2. `T` is linear and invertible, `b != b'`, and the padded relation is exactly
   the linear relation `T sigma + tau in {b, b'}`, which is exactly 2-to-2.
   107520 edges, 0 failures. So `G_pad` is an instance of KMS Definition 1.3,
   with the same `l`.
3. `OPT(G_pad) = OPT(G_folded)`, since the padded bit is unconstrained.

## Part 3: (E), (M), (B) for the 2-to-2 presentation

**Invariance.** (E) and (M) are properties of the edge law `mu` and the
annotation `(w_e, a_e, x_e)` only; neither mentions a label. The padding adds
no constraint, deletes none and changes no weight. Hence **for every
presentation of `G_folded` obtained by a per-vertex alphabet injection and a
transported constraint relation** -- the padding above, or any other reading of
what KMS Theorem 1.4's instances are -- the parameters of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` are inherited
verbatim:

* **(E)** `tau = 2^(l-1-2k)`. Given `(w_e, a_e) = ((V,L'), U)`, the direction
  `x_e` is uniform on `X_U \ (L' + H_U)`, at total variation distance exactly
  `2^(l-1+k)/2^(3k)` from uniform on `F_2^(3k) = F_2^m`, `m = 3k`.
* **(M)** `K = 1`. The law of `a_e = U` is uniform on legitimate `k`-tuples and
  equals `rho_A`, because the validity probability `Pr[L cap H_U = {0}]` does
  not depend on `U`.
* **`|Sigma_w| = 2^l`**, up from `2^(l-1)`; the decoding theorem's bound uses
  `|Sigma_w| <= 2^l`, so `p = gamma^3 2^(-l-2)` is unchanged.

**(B) with the free bit.** The padded honest encodings form a family indexed by
a bit at each `B`-vertex:

```text
hon_c(a)_C = a|_(R_C),     hon_c(a)_(V,L') = (a|_(L'), c_(V,L')).
```

The bit function of an orientation `o` is `g_e(sigma',c) =
A_(o_e(sigma',c))(U,L)(x_e)`. If `U` is clean for `a` and `hon_c(a)` satisfies
the oriented `e`, then `o_e(a|_(L'), c_w) = a|_R`, so
`g_e(hon_c(a)_(w_e)) = A_(a|_R)(U,L)(x_e) = <a, x_e> = <lambda^a_(a_e), x_e>`.
This holds for **every** `c`, every orientation, and even for choices that are
not perfect matchings. Artifact Part C: 13762560 clean satisfied cases, 0
failures; the dirty control fails in 10321920 of 82575360 cases, so the
dirty-mass term is not vacuous.

## Part 4: the kill, and why the 2-to-2 shape does not help

A 2-to-2 selector has strictly more freedom than a 2-to-1 selector: it chooses
a perfect matching inside each `K_(2,2)` block, and the witness chooses a free
bit at every seed vertex. There is **no** reduction from 2-to-2 selectors to
2-to-1 selectors: converting `o` into a 2-to-1 orientation
`o'_e(sigma') := o_e(sigma', c_(w_e))` needs the witness's bits `c`, which the
selector does not know. So the 2-to-2 case has to be run through the decoder
directly, and it can be, because the decoder never evaluates `hon`. From
`efficient-branch-selectors-list-decode-honest-outer-labels-proof`: "**Step 0**
builds the decoder from `G`, `g`, `mu` and the annotation alone. It never
evaluates `hon`." Consequently one decoder covers all `2^(|B|)` padded honest
encodings at once.

**Theorem.** Assume `NP not in RP`. Fix `gamma in (0,1/2]`, `l >= 2`, the
constant `q` of DKKMS Lemma 5.4 and an inverse-polynomial confidence `theta`.
Put `p = (gamma/2)^3 2^(-l-2)`, take `k` with `2^(l-1-2k) <= gamma/8` and
DKKMS Lemma 5.4's soundness `eps_k = exp(-k/exp(ql))` below `p^2/8`, and then
`eps_3 > 0` with `2k eps_3 <= min(gamma/2, p^2/8)`. Then for all large inputs
no randomized polynomial-time selector on the padded 2-to-2 instances `G_pad`
has the following property: on every YES instance of regular
`Gap3Lin(1-eps_3, s*)`, with probability `>= theta` over its coins, there are
an assignment `a` satisfying a `1-eps_3` fraction of `Eq` and a bit vector `c`
with orientation-lift value `val_(G_pad, g)(hon_c(a)) >= 1/2 + gamma`. The same
covers every lift labelling within constraint mass `gamma/4` of some
`hon_c(a)`, after running the parameters for `3gamma/4`.

## Consequences -- WITHDRAWN

The two bullets below were the advertised payoff and **do not hold**: they
quantify over "the proved 2-to-2 instances", and Part 1 does not identify that
family. What survives is the same pair of bullets with "the proved 2-to-2
instances" replaced by "the padded bipartite game `G_pad` constructed in Part
2". Kept as written for the record.

* **Need `1cb0e45a` is fully answered.** Both hypotheses (E) and (M) hold for
  the proved 2-to-2 instances, with the parameters `tau = 2^(l-1-2k)` and
  `K = 1` and the DKKMS folding convention of Lemma 4.1 and Definition 4.2. So
  `efficient-branch-selectors-list-decode-honest-outer-labels` applies verbatim
  to the instances behind `two-to-two-games-theorem`, in the 2-to-2
  presentation as well as the 2-to-1 one.
* **A whole escape is closed.** On route
  `rich-2to1-via-branch-selector-on-proved-2to1-instances` one could hope that
  working in the 2-to-2 presentation buys a selector something: an orientation
  is a matching, not a section, and the right labels carry an extra bit. It
  buys nothing. Both extra freedoms are invisible to the decoder, which only
  reads `g_e` as a function on `Sigma_(w_e)` and needs `|Sigma_(w_e)| <= 2^l`.
* **The surviving hole is unchanged and is H2.** Any completeness witness for
  a branch selector on the proved instances, in either presentation, must be
  far from `hon_c(a)` for every good `a` and every `c`. That is
  `view-local-selectors-beat-one-half-through-non-honest-witnesses`.
* **Scope.** This neither proves nor refutes UGC or the Rich 2-to-1 Games
  Conjecture, and it does not touch `efficient-branch-selector-on-proved-2to1-instances`
  except by removing the 2-to-2 presentation as a place to look for an honest
  witness.
* **One honest caveat.** Part 1 is a citation finding and Part 2 is a
  construction of ours: the papers assert the passage between the 2-to-1 and
  2-to-2 shapes (KMS footnote 2) without writing a map. The invariance
  statement in Part 3 is what makes the result independent of which map is
  meant: (E) and (M) survive *any* per-vertex relabelling, because they never
  mention a label.

## Attempts

1. **Eliminate the cited sources one by one, then pad `Sigma_B` with a free
   bit (2026-09-18, swarm-0917, calibrator lane).** **Refuted by all three
   referee lenses, at Part 1 / Step 0, the load-bearing citation step.** Text
   kept above and in the demoted route file
   `research/artifacts/kms-2to2-padding-attempt-2026-09-18.md`.

   - **The gap.** Part 1 argues "TR18-006 builds no game; `[4]` builds none;
     `[2]` derives one hypothesis from another; `[3]` = DKKMS TR16-198 builds
     `G_folded`; **therefore** the proved 2-to-2 instances are `G_folded`". The
     enumeration omits `[12]`, although the very abstract sentence quoted names
     it ("as proposed in `[12, 3]`") and Appendix C's chain arrow points at
     "`[12, 3]`". All three lenses fetched it: `[12]` is Khot--Minzer--Safra,
     *On Independent Sets, 2-to-2 Games and Grassmann Graphs*, ECCC TR16-124 /
     STOC 2017, whose abstract is "We present a candidate reduction from the
     3-Lin problem to the 2-to-2 Games problem", whose Definition 1.4 defines a
     *Transitive 2-to-2 Game* and whose Theorem 1.8 maps a regular
     `Gap3Lin(1-eps, s*)` instance to one. TR18-006's own Appendix C says "The
     Grassmann graphs and their potential application to the 2-to-2 Games
     problem were proposed in `[12]`." So a second, natively 2-to-2 instance
     family exists; the uniqueness premise is assumed, not established, and the
     "so" is unfilled.
   - **Part 2 solves a problem that may not exist.** TR16-124's `G_2:2` is
     already single-alphabet: vertices carry `l`-spaces of `F_2^l` with
     `dim(L ∩ L') = l-1` and restriction-type invertible maps, i.e. already in
     KMS Definition 1.3 shape with no padding. DKKMS TR16-198 page 2 describes
     `[18]` = TR16-124 as "a reduction from the 3-Lin problem to the 2-to-2
     Games problem", and of its own Test 1 says "note that Test 1 is 2-to-2 ...
     important for making the constraints of our test gain the desired property
     of being 2-to-1". The `Sigma_A` / `Sigma_B` asymmetry is therefore DKKMS
     deliberately moving *away* from a 2-to-2 test, not an accident of
     presentation that a free bit repairs. This is also why neither paper
     writes the map Part 2 calls "the one missing step".
   - **Part 3's invariance does not repair it.** The invariance is quantified
     only over presentations of `G_folded` obtained "by a per-vertex alphabet
     injection and a transported constraint relation" -- same vertex set, same
     edges, same weights, same annotation `(w_e, a_e, x_e)`. TR16-124's game is
     not such a presentation: single transitive vertex set rather than
     bipartite, a different edge law (uniform pairs of `l`-spaces meeting in an
     `(l-1)`-space, not the `L' < L` nesting from which `tau = 2^(l-1-2k)` is
     derived), `1`-to-`1` constraints inside cliques plus a transitivity
     requirement its soundness analysis uses, and an outer PCP with an advice
     feature and the `V ⊆ U` subsampling of its Definition 4.5 / Lemma 4.6. So
     (E) and (M) do not transport "with the DKKMS parameters unchanged", and
     `K` is load-bearing, since `c0 = p^2/K^2 - 2 eps`. The parent claim
     `efficient-branch-selectors-list-decode-honest-outer-labels` already
     records that family under "Scope of membership" with *different* numbers
     -- `tau <= 2^(l-1-3k)` plus a smoothness loss and `K = O(1)` -- and
     explicitly "as an argument, not as an established premise". This attempt
     asserted the family out of existence instead of discharging it.
   - **The padded game is degenerate, so Part 4's reading is not calibrated.**
     In `G_pad` the padded bit `c` occurs in **no** constraint of the instance,
     so both elements of every fiber differ only in a globally unconstrained
     coordinate and the 2-to-2 structure is inert by construction. Part 4's
     conclusion that the 2-to-2 shape "buys a selector nothing" is read off
     that degenerate game; in a genuine Definition 1.3 instance the pair
     `{b, b'}` is coupled to the rest of the instance through the other
     constraints at the same vertex, and `G_pad` is not in TR16-124's class at
     all (no `1`-to-`1` constraints, not transitive).
   - **Two secondary defects.** (i) Part 4 / Step 4 put in quotation marks two
     sentences attributed to
     `efficient-branch-selectors-list-decode-honest-outer-labels-proof`
     ("Step 0 builds the decoder from `G`, `g`, `mu` and the annotation alone.
     It never evaluates `hon`", and the Step 1 sentence); neither string occurs
     in that file. The Step 0 paraphrase is substantively right about the
     proof's Step 0, but it is a paraphrase presented as a verbatim quote.
     (ii) The runnable artifact asserts the disputed provenance in its own
     docstring rather than testing it; it checks only four structural facts
     about the padding, and cannot test the identification everything rests on.
   - **What survives.** Part 2's padding is correct: `(T sigma)_i =
     sigma(r(v_i))` is invertible because `r` carries a basis of `L` to a basis
     of `R`, `b' = b + e_l` makes the `l`-th coordinate free, the relation is
     exactly 2-to-2 and lands in KMS Definition 1.3, and `OPT` is unchanged.
     Part 3's transport is correct for that padding. Part 4's "one decoder for
     all `c`" use of Step 0 is legitimate. Together these are a theorem about
     `G_pad` alone. The artifact's four structural checks are green and are not
     in dispute.
   - **Minimum repair for whoever picks this up.** Read ECCC TR16-124 (and the
     2-to-2 statement of TR16-198 / TR17-094), identify the actual instance
     family behind Theorem 1.4 of TR18-006, and redo (E) and (M) for the A--A
     presentation with its own edge law, its `1`-to-`1` constraints and its
     subsampling. Until then the padded-bipartite result stands only as a
     statement about `G_pad`, and the 2-to-2 half of need `1cb0e45a` is open.
   - Referee verdicts posted to the live bus: `f1fe0fe9`, `02a65821`,
     `a79f48e6`.
