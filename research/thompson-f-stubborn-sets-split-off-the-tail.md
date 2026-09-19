---
rg: 2
id: thompson-f-stubborn-sets-split-off-the-tail
kind: claim
title: Stubborn sets for a monomial set S of the positive monoid of F split off the forest tail, so a private pivot order exists iff the K(S)-root prefix layers all have empty core and the published truncated windows were already complete
distinct_from:
  thompson-f-p22-monomials-admit-no-private-pivot-order: that defines stubborn sets, proves the peeling characterization, and exhibits a 1092-point core for S_(3,5) inside the truncated window M_(7,10); this proves the truncation is harmless, replaces the window by a canonical parameter-free universe, and turns every empty layer into a doubling certificate for all finite subsets of that layer.
  thompson-f-generator-sets-admit-no-private-pivot-order: that constructs stubborn sets by hand for the degree-one sets X_m; this says nothing new about X_m beyond removing the "computed only, inside M_(D, m+D)" caveat on the layers below D = m, and applies to every finite S of every degree.
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that computes the layer expansion ratio Lambda_S(D), whose definition already quantifies over every finite subset of the whole layer M_D; the doubling corollary here (item 4) is a re-derivation of Lambda_S(D) >= 2 from a different and strictly stronger hypothesis (an empty core), so it is not independent of that node — the separation that remains is items 1, 2 and 5, the fibrewise reduction of the stubborn/core predicate to the canonical prefix world P_a.
  thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs: that is the certificate whose hypothesis is being decided; this is a reduction of the decision problem.
artifacts:
  - experiments/thompson-f-pivot-orders-2026-09-18/README.md
  - experiments/thompson-f-pivot-orders-2026-09-18/forests.py
  - experiments/thompson-f-pivot-orders-2026-09-18/prefix_core.cpp
  - experiments/thompson-f-pivot-orders-2026-09-18/prefix_census.py
  - experiments/thompson-f-pivot-orders-2026-09-18/selftest.py
  - experiments/thompson-f-pivot-orders-2026-09-18/verify.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/survivors.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/family.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/law_test.py
  - experiments/thompson-f-pivot-orders-2026-09-18/law_test.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/selftest.out
  - research/artifacts/thompson-f-stubborn-tail-splitting-proof-2026-09-18.md
---

**OPEN** (demoted 2026-09-18 at landing: two of the three swarm-0917 referee lenses refuted **item
4** — the assertion that an empty core certifies doubling "strictly stronger than `Λ_S(D) >= 2`" —
and with it the `distinct_from` against `thompson-f-monomial-doubling-ratio-is-a-finite-computation`.
The proof is kept as the attempt artifact
`research/artifacts/thompson-f-stubborn-tail-splitting-proof-2026-09-18.md`. Both refuting lenses,
and the surviving lens, verified items 1, 2, 3 and 5 line by line and reproduced every computation,
so the reduction itself is expected to be restorable once item 4 is restated as "`Λ_S(D) >= 2` for
all `D <= A`, re-derived" or dropped. See `## Attempts`. Not independently reviewed; no priority
claimed.)

**Setting.** Notation as in `thompson-f-p22-monomials-admit-no-private-pivot-order`. `M` is the
positive monoid of `F`, seen as the monoid of forests of binary trees on the roots `0, 1, 2, ...`
with finitely many carets, where `x_j z` joins the roots `j` and `j+1` of `z`. `S ⊆ M_d` is a finite
set of normal forms of one degree `d`; for `w ∈ S M_D`, `N(w) = {z ∈ M_D : w ∈ S z}`; a finite
nonempty `Z ⊆ M_D` is *stubborn* if every `z ∈ Z` has at most one `w ∈ S z` with `N(w) ∩ Z = {z}`;
`core(Y)` is the largest stubborn subset of a finite `Y`, computed by greedy peeling. A stubborn set
in any layer kills every private pivot order for `S`, hence every triangular doubling certificate
built from `S` (item 1 there).

Put

    K(S) = max_{s ∈ S} max_{0 <= t < d} ( s_t + d − t + 1 )      for  s = x_(s_0) ... x_(s_(d−1)),

the number of leaves that `S` touches: every `s ∈ S` is the forest `s̄ ⊔ (trivial tail)` where `s̄`
has `K` leaves, `d` carets and `K − d` roots, and `K − 1` leaves do not suffice for the maximising
`s`. Write `z ∈ M` as `z = (u ; v)`, where `u` is the forest of the first `K` roots of `z` and `v` the
rest. Define the *prefix worlds*

    P_a(S) = { forests with exactly K roots and a carets },     |P_a| = f(K + a, K),

with `f(n, r) = (r/n) C(2n − r − 1, n − 1)` the number of ordered forests of `r` binary trees with
`n` leaves.

1. **Tail splitting.** For `s ∈ S` and `z = (u ; v)`,
   - `s z = (s̄ · u ; v)`, where `s̄ · u` is the forest with `K − d` roots obtained by grafting the
     `K` root trees of `u` onto the `K` leaves of `s̄`;
   - if `w = s' z'` with `s' ∈ S` and `z' ∈ M`, then `z' = (u' ; v)` with the **same** tail `v`, and
     `s̄' · u' = s̄ · u`.

   Consequently, for any `Z ⊆ M_D` and `z = (u ; v) ∈ Z`, the successors of `z` that are private for
   `z` in `Z` are exactly those coming from successors of `u` private for `u` in the fibre
   `Z_v = {u'' : (u'' ; v) ∈ Z}`, a subset of `P_(D − c(v))` where `c(v)` is the number of carets of `v`.

2. **Fibrewise criterion.** `Z ⊆ M_D` is stubborn iff every nonempty fibre `Z_v` is stubborn in its
   prefix world. Hence
   - the union of all stubborn subsets of `M_D` is `⨆_v core(P_(D − c(v))) × {v}`, over all tails `v`
     with at most `D` carets (`M_D` is infinite, so this union is not itself a finite stubborn set);
   - `core(M_D) ≠ ∅` iff `core(P_a) ≠ ∅` for some `a <= D`;
   - the least `D` with a stubborn subset of `M_D` is the least `a` with `core(P_a) ≠ ∅`;
   - **a private pivot order for `S` exists iff `core(P_a) = ∅` for every `a >= 0`.** This is a
     sequence of finite computations with no free parameter, one per degree.

3. **The published truncations are complete.** Every element of `P_a` has normal form with letters
   `<= K + a − 2`, and this is attained; `K + a − 2` is exactly the bound `R_S(a)` used by
   `experiments/thompson-f-2026-09-17/stubborn_census.py`. So `P_a ⊆ M_(a, R_S(a))` and
   `core(M_(a, R_S(a))) = ∅` implies `core(P_a) = ∅`; and `core(P_b) = ∅` for **all** `b <= a`
   implies `core(M_a) = ∅` (item 2 gives `core(M_a) ≠ ∅` iff `core(P_b) ≠ ∅` for *some* `b <= a`, so
   the whole prefix of the census is needed, not one row — every census row used below satisfies
   this, since the rows run consecutively from `a = 1` and stop at the first nonempty core, and
   `core(P_0) = ∅` whenever `|S| >= 2`). Every "no core" row of
   the published census is therefore a statement about the whole layer `M_a`, not only about a
   window. In particular the caveat of `thompson-f-generator-sets-admit-no-private-pivot-order`,
   item 2 — "the emptiness below `D = m` is still computed only, inside `M_(D, m + D)`" — is removed:
   `X_m` has **no** stubborn subset of `M_D` for `D < m`.

4. **An empty core re-derives layer doubling.** If `core(P_a) = ∅` for all `a <= A`, then
   `|S Y| >= 2 |Y|` for every finite `Y ⊆ ⋃_(D <= A) M_D`. (Item 3 of
   `thompson-f-p22-monomials-admit-no-private-pivot-order` gives this inside one finite window; tail
   splitting and additivity over layers give it on all of `M` up to degree `A`.)

   *Corrected at the 2026-09-18 referee pass (this is the refuted item; see `## Attempts`).* The
   node as first written claimed this was "strictly stronger than `Λ_S(D) >= 2`", on the reading
   that `Λ_S(D)` is the ratio of one extremal set inside a window. That reading is wrong:
   `thompson-f-monomial-doubling-ratio-is-a-finite-computation` defines
   `Λ_S(D) = inf { |S Y| / |Y| : Y ⊆ M_D finite nonempty }`, an infimum over **every** finite
   nonempty subset of the **whole** layer, and its item 1 proves the infimum is already attained
   inside the window `M_(D, R_S(D))`. Since `S` maps distinct layers to distinct layers,
   `|S Y| = Σ_D |S Y_D|`, so the conclusion above is *logically equivalent* to "`Λ_S(D) >= 2` for
   every `D <= A`" — not stronger. It is also not new: an empty census row `core(M_(D, R_S(D))) = ∅`
   already forces `core(Y) = ∅` for every `Y` inside that window, hence `|S Y| >= 2|Y|` there by item
   3 of `thompson-f-p22-monomials-admit-no-private-pivot-order`, and item 1 of the doubling-ratio
   node moves that to all of `M_D`. The hypothesis here is in fact strictly stronger than what
   `Λ_S(D) >= 2` needs, and on every set in the census it reaches strictly fewer layers: for
   `S_(3,5)` it stops at `A = 6` while the published exact `Λ` values give doubling of every finite
   `Y ⊆ M_D` for `D <= 12`. What the tail splitting does add to the published windows is item 3
   (the windows were complete, so the statements are about all of `M_a`), not a new certificate.

5. **A common left factor is invisible.** If `S = t S''` for a fixed `t ∈ M` and a finite
   `S'' ⊆ M_(d − deg t)`, then `w ↦ t^(−1) w` is a bijection `S M_D → S'' M_D` carrying `N_S` to
   `N_(S'')`, so `S` and `S''` have the *same* stubborn sets and the same cores in every layer. In
   particular, writing `X_m = {x_0, ..., x_m}` and

       S(m, d) = X_m X_(m+1) ... X_(m+d−1) = { x_(i_1) ... x_(i_d) : i_1 <= ... <= i_d, i_t <= m+t−1 },

   one has `S(0, d) = x_0 · S(1, d − 1)`, hence the first stubborn layer satisfies
   `a_min(S(0,d)) = a_min(S(1, d−1))` exactly.

6. **Computations** (`prefix_core.cpp`, exact integers, lattice-path ranking, no hash table; the core
   is re-verified from scratch after peeling; `selftest.py` checks the forest model and its defining
   relation, the constant `K(S)`, the letter bound of item 3, tail splitting itself on random data,
   agreement with the Python reference on 14 layers, identity with the published 1092-point core,
   and item 5 on `S(0,3) = x_0 · S(1,2)`; output in `selftest.out`).
   - *Reproduction.* Every row of `experiments/thompson-f-2026-09-17/stubborn_census.jsonl` is
     reproduced in this independent model (`verify.jsonl`): first core at `a = m` for `X_m`,
     `m = 1..6`, of sizes 2, 8, 40, 221, 1288, 7752; at `a = 4` for `S_(2,4)` (24 points); at `a = 7`
     for `S_(3,5)` (1092 points, `|S Z| = 5304`); at `a = 4` for `{x_0^2, x_1^2, x_2^2}` (8 points);
     at `a = 10` for `S_(4,6) = X_3 X_4` (81224 points, `|S Z| = 534820`). Both the core sizes and
     the image sizes agree with `stubborn_census.jsonl` on every row. The whole reproduction runs in
     10 s, against a universe smaller than the published windows by a factor that runs from 1.00
     (the first row of each set, and the whole `X_1` row) to 1.60 (`S_(4,6)` at `a = 10`, 1 225 785
     instead of 1 961 256); the `S_(3,5)` row is 13260 instead of 19448, a factor 1.47. (An earlier
     draft said "1.5 to 11 times smaller"; the 11 was wrong and is corrected here — see
     `## Attempts`.)
   - *The 1092-point `S_(3,5)` core lies in `P_7`*, 13260 forests, exactly as item 2 predicts, and
     is **the same set element by element** as the published word list
     `s35_stubborn_core_D7.txt`, which was produced by the other implementation
     (`selftest.py`, last item). That the published data has `core(M_(7,14)) = core(M_(7,10))` is
     explained by item 2: at the first stubborn degree `core(M_D) = core(P_D) × {trivial tail}`,
     since all lower prefix layers are empty, so the window cannot matter.
   - *New empty layers* (`survivors.jsonl`), each now a statement about all of `M_a` by item 3:
     - `T = {x_a x_b x_c : a <= 2, b <= 3, c <= 4} = S(2,3)`: `core(P_a) = ∅` for `a <= 12`
       (`|P_12| = 17 298 645`); the published census reached `a = 10`.
     - all 21 degree-2 monomials with letters `<= 5`: `core(P_a) = ∅` for `a <= 11`
       (`|P_11| = 14 567 280`); the published census reached `a = 9`.
   - *Staircase family* (`family.jsonl`, `law_test.jsonl`). Writing
     `S(m,d) = X_m X_(m+1) ... X_(m+d-1)`, the first stubborn layer is 1, 4, 7, 10, 13 for `d = 2`,
     `m = 0..4` (core sizes 2, 24, 1092, 81224, **7 470 184**, the last on a layer of 121 580 760
     forests), 4 and 13 for `d = 3`, `m = 0, 1`, and 13 for `d = 4`, `m = 0`. The `d = 3, m = 0` core
     is the `S(1,2)` core itself and the `d = 4, m = 0` row reproduces the `d = 3, m = 1` row exactly,
     as item 5 forces. The law these obey is
     `thompson-f-staircase-sets-have-stubborn-layers` (OPEN).

**Scope.**
- This decides neither `thompson-f-is-amenable` nor doubling of any `S`. It makes the pivot-order
  question a canonical sequence of finite computations and removes the truncation gap from the
  published ones. It does **not** add a doubling certificate: item 4 re-derives `Λ_S(D) >= 2`, which
  `thompson-f-monomial-doubling-ratio-is-a-finite-computation` already computes, and it reaches
  fewer layers than that node does.
- Item 4 gives certificates only up to the degree computed; nothing here bounds the degree at which
  a core appears. The conjectured law for the staircase family is
  `thompson-f-staircase-sets-have-stubborn-layers`, which is OPEN.
- Nothing here bears on doubling certificates that are not orders (Hall matchings, flows). It is
  worth recording, though, that the flow lane reached the same shape of statement independently on
  the same day: in the observation-gate language of
  `thompson-f-flow-certificate-observation-gate`, an observation that reads the exact shapes of every
  tree past a bounded prefix has shadow defect zero, so a flow certificate too can only live on a
  bounded prefix of the forest (swarm-0917, lane `e2-w2-f-shadow-defect`; that node is not a
  prerequisite here and nothing above depends on it). Both certificate classes therefore localise to
  the first `K` roots, and the tail is inert for both.

Attempted proof (demoted to an attempt artifact at landing):
`research/artifacts/thompson-f-stubborn-tail-splitting-proof-2026-09-18.md`.

## Attempts

- **2026-09-18: direct proof via the route `thompson-f-stubborn-tail-splitting-proof` (refuted by
  two of three referee lenses at landing; kept as an attempt).** The route now lives at
  `research/artifacts/thompson-f-stubborn-tail-splitting-proof-2026-09-18.md`, and the
  re-implementation in `experiments/thompson-f-pivot-orders-2026-09-18/` remains as its computational
  artifact. All three lenses agree that Step 0 (`K(S) = max_(s,t) (s_t + d − t + 1)`), item 1 (tail
  splitting and the same-tail factorisation, from right-cancellativity of `M ⊆ F` and the fact that
  every `s ∈ S` presents exactly `K − d` roots), item 2 (privacy is antitone in `Z`, so stubborn
  sets are union-closed, the core is well defined and the fibres are independent), item 3's letter
  bound `K + a − 2 = R_S(a)`, and item 5 (a common left factor is invisible) are correct, and two of
  them rebuilt `prefix_core.cpp` and reproduced `verify.jsonl`, `core_atoms.json`, the letters-2
  census and the headline new layers independently. **What was refuted is item 4** and the
  `distinct_from` that rests on it, on the quantifier of the cited node; the body of item 4 above
  has been restated accordingly, but the node is parked OPEN until it is re-refereed with the
  corrected statement (or item 4 is dropped). The three lens verdicts, in summary:
  - *Lens 1 (refuted=false).* Found no load-bearing step that fails. Reproduced `verify.jsonl`
    exactly (9.7 s, 46/46 rows), `core_atoms.json` byte-identically, the letters-2 census
    identically, and recomputed the headline new layers independently: `S(1,3)` empty at `a = 12`
    and core 134160 at `a = 13` (`|S.core| = 818220`); `S(4,2)` empty at `a = 11, 12` and core
    7 470 184 at `a = 13` on 121 580 760 forests (1.71 GB, 1142 s); `T = S(2,3)` empty at `a = 12`
    (17 298 645); all degree-2 letters `<= 5` empty at `a = 11` (14 567 280). Its strongest check is
    independent of the new code: the *old* word-rewriting implementation
    (`experiments/thompson-f-2026-09-17/stubborn_core.cpp`) confirms the fibre theorem's own
    prediction `core(M_(D,L)) = core(P_D) + (#1-caret tails admitted by L) · core(P_(D−1))` —
    `X_2` at `D = 3` gives 34 at `L = R_S(3) = 5` then 42, 50, 58, 66 stepping by exactly
    `core(P_2) = 8`; `S(1,2)` at `D = 5` gives 144 at `L = 7` then 168, 192, 216, 240 stepping by
    exactly `core(P_4) = 24`; `X_1` at `D = 2` gives 7 at `L = 3` then 9, 11, 13, 15, 17 stepping by
    `core(P_1) = 2`. Cosmetic defects it did find, all now fixed or recorded: the attainment witness
    for item 3's letter bound is the *last* root, not the first (for `K = 5, a = 4` the right vine as
    first root gives max letter `a − 1`, not `a`); the `core(P_a) = ∅ ⟹ core(M_a) = ∅` chain needs
    all `b <= a` (now stated); item 6's "1.5 to 11 times smaller" is wrong, the measured ratio over
    all 46 rows runs 1.0 to 1.6 (now corrected); the route calls the infinite union `C` "stubborn"
    although stubborn is defined only for finite sets; `forests.py`'s docstring formula
    `K = 1 + max(last letter + 1)` disagrees with the code's correct `K_of` on sets like
    `{x_0 x_5 x_5}` (8 vs 7); and `law_test.jsonl`'s `(1,3)` and `(0,4)` rows lack the
    `expected`/`law_holds_here` fields and the `a_min − 1` rows that the committed `law_test.py`
    loop emits (that emptiness is recorded in `family.jsonl` instead).
  - *Lens 2 (refuted=true), the citation/quantifier lens.* "REFUTED at item 4 ... and its
    `distinct_from` against `thompson-f-monomial-doubling-ratio-is-a-finite-computation`. The cited
    node defines `Λ_S(D) = inf { |S Y| / |Y| : Y ⊆ M_D, finite, nonempty }` — an infimum over EVERY
    finite nonempty subset of the FULL layer `M_D`, and its item 1 is precisely the theorem that the
    window is lossless: `Λ_S(D) = min over Y ⊆ M_(D, R_S(D))`. So both differentiating adjectives
    are false as quoted: `Λ` already quantifies over every subset, not 'the extremal one', and it is
    already a statement about the whole layer, not a window. And since `S` maps distinct layers to
    distinct layers, `|S Y| = Σ_D |S Y_D|`, so item 4's conclusion is *logically equivalent* to
    '`Λ_S(D) >= 2` for every `D <= A`', not strictly stronger. WORSE, THE COROLLARY IS NOT NEW: a
    census row `core(M_(D, R_S(D))) = ∅` forces `core(Y) = ∅` for every `Y` inside that window, so
    `|S Y| >= 2|Y|` there by item 3 of `thompson-f-p22-monomials-admit-no-private-pivot-order`, and
    item 1 of the doubling-ratio node says the infimum over all of `M_D` is attained in exactly that
    window. Hence `Λ_S(D) >= 2`. So the fourth advertised corollary — one of the four in the title
    and the one propagated into the root node bullet, into
    `thompson-f-staircase-sets-have-stubborn-layers` consequence 3 and into the `monomial-sets`
    calibration — is a restatement of an already-established finite criterion, and the
    `distinct_from` that keeps the two nodes apart rests on misquoting the cited quantifier. ... It
    should be demoted to 'item 4 = `Λ_S(D) >= 2` for all `D <= A`, re-derived' (or dropped, with the
    `distinct_from` rewritten) before the node keeps ESTABLISHED status for its stated content."
    Secondary defects it names, all repairable and all now fixed above: the `core(P_a) = ∅ ⟹
    core(M_a) = ∅` quantifier slip; item 6's "1.5 to 11 times smaller", whose own artifact gives
    ratios 1.000 to 1.600 (`S_(4,6)` at `a = 10`, 1 961 256 vs 1 225 785) with nothing near 11; and
    the root-node bullet saying "all eleven computed cases" and then enumerating fourteen. It
    explicitly records that "the mathematics of items 1, 2 and 5 is correct and correctly imported"
    and that `verify.jsonl` reproduces every published core size and image size.
  - *Lens 3 (refuted=true), the calibration lens.* Same failing step, with the direction of the
    comparison measured: "item 4's conclusion is exactly '`Λ_S(D) >= 2` for all `D <= A`' ...
    identical, not stronger, and derived from a strictly stronger hypothesis. The direction is in
    fact reversed on every set in the census: for `S_(3,5)` item 4 reaches only `A = 6` (core at
    `a = 7`) while the published exact `Λ` values give doubling of every finite `Y ⊆ M_D` for
    `D <= 12` (min 3456957/1295921 ≈ 2.667); for `S_(2,4)`, `A = 3` vs `D <= 10`; for `X_2`, `A = 1`
    vs `D <= 2`." It also downgrades the novelty of item 1: tail splitting is Lemma A of the
    ESTABLISHED route `thompson-f-monomial-doubling-ratio-finite-universe-proof` (2026-09-13)
    restated in the forest model — "letters above `R_S(D)` are never passed", hence `s w = (s a) b`
    and `S Y = ⊔_b (S Y_b) b` — so what is genuinely new is the fibrewise criterion with the smaller
    canonical universe `P_a` (item 2) and item 5. It rebuilt `prefix_core.cpp` and re-ran
    `selftest.py` and `prefix_census.py verify` in a scratch copy: all selftests PASS (including
    equality with the published 1092-point `s35_stubborn_core_D7.txt`) and every first-core row
    reproduces; `|P_a|` matches `f(K+a,K)` exactly (8 947 575, 33 266 625, 31 865 925, 121 580 760).
    On the assigned calibration it finds no error: the proof does use what separates this monoid
    from the calibration targets (right-cancellativity of `M ⊆ F`, the degree grading,
    left-cancellativity in item 5), and the non-unimodular calibration does not bite, since in the
    amenable `BS(1,2)` the submonoid `⟨t, at⟩` is free, so `S = {t, at}` has `|S Y| = 2|Y|` for every
    `Y` and admits a private pivot order while the ambient group is amenable — the step that must
    separate groups from monoids is item 1 of `thompson-f-nonamenable-iff-some-monomial-set-doubles`
    (`F = M M^(−1)` is an Ore group of fractions, so finite subsets of `F` push into `M`; a free
    submonoid is not cofinal), and this node correctly never invokes it. It records the end-fixing
    calibration as a warning rather than an error: tail inertness is the same bounded-prefix
    phenomenon as the already-dead finite-state and end-rigid certificates
    (`thompson-f-finite-state-flows-cannot-prove-nonamenability`,
    `thompson-f-end-rigid-schreier-graphs-are-amenable`), so item 4's "doubling certificate" framing
    invites exactly the over-reading that the false `Λ` comparison then commits.
- **What a restoration needs.** Nothing computational: the artifacts stand and were reproduced
  twice, independently and in a third implementation. The node needs a referee pass on the corrected
  text — item 4 as a re-derivation of `Λ_S(D) >= 2`, the `distinct_from` against the doubling-ratio
  node rewritten around items 1, 2 and 5, and item 1's relation to Lemma A of
  `thompson-f-monomial-doubling-ratio-finite-universe-proof` stated rather than implied.
