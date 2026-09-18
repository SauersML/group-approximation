---
rg: 2
id: bmw-44-sat-survivor-parity-kernels-not-left-orderable
kind: claim
title: The three degree-(4,4) BMW classes whose positive-cone instances stay satisfiable have non-left-orderable parity kernels, or are reducible
distinct_from:
  bmw-degree-44-53-parity-kernels-not-left-orderable: that is the established census theorem, which excludes exactly these three classes; this is the open statement for them
  irreducible-tree-product-lattices-are-not-left-orderable: that asks about boundary-2-transitive projection closures; these three classes have intransitive local actions (S_3 fixing one letter) on both trees, so even if irreducible they fall outside it
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that covers degrees (3,3), (4,3) and torsion-free (4,4), where every class not certified reducible is refuted
artifacts:
  - experiments/bmw-census-left-orders-2026-09-17/README.md
  - experiments/bmw-census-left-orders-2026-09-17/census_40_40.json
  - experiments/bmw-census-left-orders-2026-09-17/out_40_40.jsonl
  - experiments/bmw-census-left-orders-2026-09-17/bigsat.py
  - experiments/bmw-census-left-orders-2026-09-17/bigsat.log
  - experiments/bmw-census-left-orders-2026-09-17/bigsat10.log
  - experiments/bmw-census-left-orders-2026-09-17/bigsat193.log
  - experiments/bmw-census-left-orders-2026-09-17/bigcap.py
  - experiments/bmw-census-left-orders-2026-09-17/bigcap.log
  - experiments/bmw-census-left-orders-2026-09-17/localact.py
  - experiments/bmw-census-left-orders-2026-09-17/localact.log
  - experiments/bmw-census-left-orders-2026-09-17/irred.py
  - experiments/bmw-census-left-orders-2026-09-17/irred_q.py
  - experiments/bmw-census-left-orders-2026-09-17/irred_q.log
  - experiments/bmw-census-left-orders-2026-09-17/irred_kps.py
  - experiments/bmw-census-left-orders-2026-09-17/irred_tw.py
  - experiments/bmw-census-left-orders-2026-09-17/halftree.py
  - experiments/bmw-census-left-orders-2026-09-17/selfrep.py
  - experiments/bmw-census-left-orders-2026-09-17/klev.py
  - experiments/bmw-census-left-orders-2026-09-17/klev.log
  - experiments/bmw-census-left-orders-2026-09-17/klev193V.log
  - experiments/bmw-census-left-orders-2026-09-17/kkps.py
  - experiments/bmw-census-left-orders-2026-09-17/ksig.py
  - experiments/bmw-census-left-orders-2026-09-17/kindex.py
  - experiments/bmw-census-left-orders-2026-09-17/kstab.py
  - experiments/bmw-census-left-orders-2026-09-17/kcoset.py
  - experiments/bmw-census-left-orders-2026-09-17/klt.py
  - experiments/bmw-census-left-orders-2026-09-17/klt.log
  - experiments/bmw-census-left-orders-2026-09-17/kltc.py
  - experiments/bmw-census-left-orders-2026-09-17/l2rep.py
  - experiments/bmw-census-left-orders-2026-09-17/l2rep.log
  - experiments/bmw-census-left-orders-2026-09-17/kernel.py
  - experiments/bmw-census-left-orders-2026-09-17/abel.py
  - experiments/bmw-census-left-orders-2026-09-17/morse.py
---

**OPEN.** Let `Γ` be the BMW group of degree (4,4) in class `40_40#193`, `#281` or `#332` of
`census_40_40.json`. All eight letters are involutions. Then either `Γ` is reducible, or its parity
kernel `Γ^+` (index 4, torsion-free) is not left-orderable.

**Why these three.** They are the only classes of degree (3,3), (4,3), (4,4) or (5,3) that are neither
certified reducible nor refuted by a positive-cone SAT instance
(`bmw-degree-44-53-parity-kernels-not-left-orderable`). A proof would finish the census theorem in
these degrees. An irreducible counterexample would be an irreducible BMW lattice with a left-orderable
finite-index subgroup. Such a lattice is not Kazhdan, but it would be a new candidate
ingredient for `infinite-left-orderable-kazhdan-group` through the constructions discussed in
`small-degree-irreducible-bmw-parity-kernels-not-left-orderable`.

## What is known about the three classes

**SAT persists.** The positive-cone CNF for `Γ^+` is satisfiable, with CaDiCaL 1.5.3 and Glucose 4
agreeing:
- at radius 4, 6 and 8 in the pipeline (`out_40_40.jsonl`);
- at radius 8 with one factor of length at most 4, 5756592 clauses (`bigsat.log`);
- at radius 10 with one factor of length at most 2, 9373692 clauses (`bigsat10.log`, `bigsat193.log`).

Among the four classes that needed radius 8 (short 4), the two refuted ones became UNSAT there,
and these three did not.

**Reducibility is not certified.** The images `⟨A⟩ → Aut(T_V)` and `⟨B⟩ → Aut(T_H)` have minimal
automata above the cap even at 60000 states (`bigcap.log`).

**Local actions.** On both trees the local action is `S_3` acting on four letters and fixing one of
them (`localact.log`). That fixed letter `f` is fixed at every vertex by every element of `H_x`.

**The invariant-subtree quotient `K`** (`selfrep.build`, `klev.py`).
- The reduced vertical words `l_0 f l_1 f l_2 ...` with `l_j ≠ f` form an `H_x`-invariant subtree.
- On it `H_x` acts through a 4-state automaton group `K` on the ternary tree `{letters ≠ f}^*`. So `K`
  is a quotient of `H_x`, and `K` infinite implies `Γ` irreducible (Burger–Mozes, Prop. 1.2).
- For `#281` (V side, and identically on the H side), with `X = {0,1,2}`, the generators are:
  - `a_0 = (a_1,a_1,a_1)`
  - `a_1 = (12)(a_0,a_2,a_2)`
  - `a_2 = (12)(a_2,a_0,a_0)`
  - `τ = (01)(τ,τ,τ)`

  So `D = {1,a_0,a_1,a_2} ≅ V_4`, with `a_2 = a_0a_1`, and `τ` applies `(01)` to every letter. `K`
  is a quotient of `V_4 * Z/2`.
- The orders of `K` on levels 1–5 are `6, 324, 8748, 236196, 6377292`, which is `4·3^{3n-2}` for
  `2 ≤ n ≤ 5`.
- The derived series of the level-5 image is `6377292, 1594323, 177147, 2187, 1`. So `K/K'` is
  `V_4`, and the level images of `K'` are 3-groups.
- Sampled elements of `K'''` have order 3 and elements of `K''` have order 9, stably in the level.
  This suggests `K` is an infinite torsion group of Gupta–Sidki type, which is why the
  infinite-order-element certificates below find nothing.
- `#332` gives level orders `6, 324, 12754584, 1.3·10^17` (V) and `6, 1296, 1.6·10^9, 3.3·10^27` (H).
  `#193` gives `6, 1296, 3.3·10^9, 6.5·10^27, 5.2·10^82` (V, `klev193V.log`).
- `K` acts transitively on every level through level 8 (orbit 6561) for `#193` V/H, `#281` V and
  `#332` V/H.

**Other invariants.**
- `b_1(Γ^+) = 2` for all three (`abel.py`, Reidemeister–Schreier plus Smith form), with torsion `Z/2`
  for `#281`. The refuted `#176` and `#256` also have `b_1 = 2`, so this does not separate the
  survivors.
- `morse.py` finds no Bestvina–Brady Morse function pattern.

**Heuristic.** A reducible lattice is virtually `F_k × F_l`, and in the census 5819 of the 5836
certified-reducible classes have a satisfiable radius-4 instance. So persistent SAT is what
reducibility would predict. On
the other hand, `K` is transitive through level 8 and grows like `3^{3n}`. If `Γ` is reducible then
`H_x` is finite, with `|H_x| ≥ |K_5|`: at least `6.4·10^6` for `#281` and `5·10^82` for `#193`. The
second is implausible for a vertex stabilizer, which favours irreducibility at least for `#193`.

## Attempts

- (w3-107, 2026-09-18) **Irreducibility certificates, all null on the three classes.**
  - Finiteness cap 60000 (`bigcap.py`).
  - An infinite-order element of `H_x` from a section `(g^L)|_u = g^{±1}` (`irred.py`), or conjugate to
    `g^{±1}` (the Klimann–Picantin–Savchuk orbit-signalizer idea: `irred_kps.py` on `H_x`, `ksig.py`
    on `K`), and the quotient-graph version for `H_x` as a quotient of `E * ⟨τ⟩` (`irred_q.py`,
    22–374 nodes, no cycle).
  - Half-tree fixator (`halftree.py`, no certificate within the timeout).
  - Self-replication of `K` (`selfrep.py`): `φ_v(Stab_K(v))` is a proper subgroup of index 3 modulo
    level 3, so `K` is not fractal and this certificate cannot work.
  - Index certificates `[K : φ_v(Stab_K(v))] < |K v|` (`kstab.py`, `kindex.py`, `kcoset.py`).
  - Thompson–Wielandt (`irred_tw.py`), which does not apply since the local actions are not
    2-transitive.
  - The level-transitivity chain `L_{i+1} ≤ φ_v(Stab_{L_i}(v))` closed by an exact containment
    (`klt.py` with 6 steps, products of 3, level 4; `kltc.py` with canonical short words). The chain
    stabilises modulo level 3 at a subgroup `L_2` of order `4·3^{3n-4}` on level `n` (`n = 3,4,5`).
    But the exact closing identity was not found, because the generators of `L_i` lengthen at each
    step (`kltc.py`, `#281` V, `v = 0`: 4, 5, 8, 20, 56 generators; ball radius 9 times out).
  - Exact self-replication of `L_2` for `#281` (`l2rep.py`, `l2rep.log`). `L_2` has eight generators
    of length at most 11, order `19131876` modulo level 6, and moves `v = 0` (orbit `{0,1,2}`). In the
    radius-4 ball of `L_2` (2379 elements modulo level 6), exact preimages under `φ_0` were found for 4 of
    the 8 generators. Four more would give `L_2 ≤ φ_0(Stab_{L_2}(0))`, hence `L_2` infinite and `Γ`
    irreducible by the weak cycle lemma (`kltc.py` header).
  - **Obstruction.** Every certificate aimed at an element of infinite order is expected to fail if
    `K` is torsion, which the element orders suggest. What remains is a hand proof that `L_2` is
    self-replicating, in the style of Gupta–Sidki.
- (w3-107, 2026-09-18) **Left-orderability, not attempted beyond SAT.** A left order on `Γ^+` would
  need an argument like Rolfsen–Zhu's for free-by-free groups or a Bergman-type construction. Neither
  was tried. Extracting a consistent order from a radius-10 model is not a proof.
- (w4-107, 2026-09-18) **`#281` is irreducible (ESTABLISHED, `bmw-40-40-281-is-irreducible`).**
  - The planned Gupta–Sidki step is false. `L_2` is not self-replicating at `0`: modulo level 5,
    `φ_0(Stab_{L_2}(0))` has index 3 in `L_2`, and generators 4, 6 and 7 lie outside it
    (`experiments/bmw-281-linear-model-2026-09-17/l2test.log`). The whole section chain
    `G_{k+1} = φ_0(Stab_{G_k}(0))` strictly decreases (`chain.log`: `|G_k|` on level `m` is
    `4·3^{max(3m−2−k, 2m−1)}`).
  - Instead, `K` is linear. An explicit contracting coordinate system `Φ : X^ω → F_3[[s]]` conjugates
    `a_0, a_1, a_2, τ` to `σ`, `−σ`, `−z` and `T(z) = (u−z)/(1−suz)`, where `σ : s ↦ −s` and
    `u = 1/(1−s)`. The proof is twelve rational-function identities, checked exactly by
    `mobius281.py`.
  - `τa_2` becomes `z ↦ (z+u)/(suz+1)`, of infinite order. So `K` is infinite and not torsion, and
    `Γ` is irreducible. The earlier Gupta–Sidki torsion reading is wrong.
  - For `#281`, this claim is now exactly: `Γ^+` is not left-orderable.
- (w5-107b, 2026-09-18) **Resolved for all three classes, unconditionally (ESTABLISHED via
  `bmw-44-sat-survivor-dichotomy-via-unconditional-certificates`).** `Γ^+` is not left-orderable for
  `#193`, `#281` and `#332` (`bmw-40-40-193-281-332-parity-kernels-not-left-orderable`), so the dichotomy holds
  without deciding reducibility. The "SAT persists" section above is superseded by this result.
  - **Witness.** Take the subgroup `M = ⟨x, y, f x^{-1} f, g y^{-1} g⟩` with `x = v_i v_j` and `y = h_k h_l`:
    `(x, y, f, g) = (v0v1, h0h1, v3, h3)` for `#281` and `#332`, and `(v1v3, h1h2, v2, h3)` for `#193`.
    Take the positive-cone instance on the ball of radius 4 in these four generators, with short factor 2 (3169
    elements). It is UNSAT, with a deletion-minimal core of 333 elements and 420 relations (`cert_<c>.json` in
    `experiments/bmw-44-survivor-left-orders-2026-09-17/`).
  - **Check.** `verify_cert.py` uses only the census squares. It checks confluence and unique normal forms,
    then every relation, then UNSAT with three solvers and a self-checked DRUP proof.
  - **Why the letter balls stayed SAT.** The certificate elements have up to 14 letters, and many relations
    have both factors 6 or 8 letters long.
  - **Calibration.** The product class `#0` gives 0 UNSAT among the same 144 subgroup shapes.
  - **How it was found.** The kernel `N = ker(Γ^+ → Z²) = A ⋈ B` gave a first UNSAT on `N_1`, and the core was
    then shrunk to four generators.
  - **Not duplicated.** This is independent of the Möbius model and of the relative-convexity route of w4-107.
- (w5-107, 2026-09-18) **Exact self-replication certificates for `#332` and `#193` are blocked; #332 is reduced to an orbit property of a dual transducer.**
  - **Obstruction (ESTABLISHED, `bmw-332-193-self-similar-certificates-need-new-relation`).**
    - For `K(332V)`, `K(332H)`, `K(193V)` and `K(193H)`, `K` is a quotient of a virtually free amalgam
      `A`: `V_4 * C_2` or `C_2^3 *_{C_2} S_3`.
    - `K` and `A` have the same cyclically reduced relations of length `≤ 12`, and the wreath recursion
      descends to `A`.
    - `G_1 = φ_0(St(0))` lies in the preimage of an index-3 subgroup `M` of `A`, under a map
      `ρ : A → S_3` that is not a level quotient. The missing letter is not in `M`.
    - Hence "express letter 3 (resp. 1) as a word in `G_1`", branching `N × N × 1 ≤ ψ(N)`, and
      section-chain closure all need a relation of `K` of length `≥ 13` that fails in `A`. All three are
      impossible if `K ≅ A`, which is exactly the case in which `Γ` is irreducible.
    - The earlier "letter 3 is in `G_1` modulo levels 5–6" is an artefact of the non-congruence of `ρ`.
  - **Reduction (ESTABLISHED implication, `bmw-40-40-332-irreducible-if-dual-orbit-parity`).**
    - Sections of alternating words `τd_n⋯τd_1` are read by the 3-state dual transducer `B`, and the
      sign of the root permutation is `(−1)^{#a_0}`.
    - So if every `⟨B⟩`-orbit on `{a_0,a_1,a_2}^n` contains an odd-`a_0` sequence (e.g. `⟨B⟩`
      level-transitive), then `K(332V) ≅ V_4 * C_2`, `#332` is irreducible, and this claim for `#332`
      becomes left-orderability of `Γ^+`.
    - `⟨B⟩` is transitive through level 8, so `K(332V)` and `V_4 * C_2` agree on all words of length
      `≤ 17`.
    - `B` contains the `#281` `V_4` (relabelled). But `B` meets the same index-3 non-congruence
      obstruction, so its self-replication is not the route either.
  - **Dead:**
    - the largest `B`-invariant even-`a_0` set as a regular language (2, 12, 648 states, then above
      2 GB);
    - words of length `≤ 13` for `c_1 ∈ φ_2(St_B(2))`.
  - **Next:** prove level-transitivity of `⟨B⟩` (or just the orbit-parity condition) without
    self-replication. For example:
    - find a spherically transitive element, or an odometer-type conjugacy of a suitable product;
    - or find an invariant compatible with `ρ`.
    For `#193` and `332H`, the analogous duality has three independent `D`-letters generating
    `C_2^3` and the `S_3` relation `(τc)^3 = 1`, so it needs its own parity lemma.
- (w6-107c, 2026-09-18) **Hand proof, no SAT (`bmw-40-40-193-281-332-klein-chain-proof`).** For all
  three classes `Γ^+` contains four elements, each a two-letter word or a letter conjugate of one, with
  `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}` cyclically.
  - In a left order, `a b a^{-1} = b^{-1}` forces `|b| < |a|`. So the cycle gives
    `|x_1| < |x_2| < |x_3| < |x_4| < |x_1|`.
  - For #281 and #332 the cycle is `h0h2, v3v0v2v3, h3h1h2h3, v1v2`.
  - For #193 it is `h0h1, v0v3, h3h0h2h3, v2v0v1v2`.
  - The dichotomy is thus proved by hand, independently of the DRUP certificate.
  - **Remaining open for these classes:** irreducibility of #332 and #193 (the dual-orbit parity of
    `bmw-40-40-332-irreducible-if-dual-orbit-parity`). It no longer matters for orderability.
- (w6-107c, 2026-09-18) **The Klein-chain method covers the census
  (`bmw-census-sat-free-klein-chain-certificates`).**
  - **Scan.** `kpure.py` searches the pure-word inverting graph of every census class that is not
    certified reducible: 2 classes of `30_30`, 27 of `40_30`, 190 of `50_30` and 301 of `40_40`.
    Words have length at most 6, or at most 8 for the `50_30` #470 and `40_40` #176 reruns.
  - **Result.** 33 classes get a four-element cycle, with a SAT-free rewriting check
    (`verify_census_X.log`). They include all five `40_40` classes that stay satisfiable through
    `R8s2` (#176, #193, #256, #281 and #332) and the `50_30` survivor #258.
  - **No cycle found.** `50_30` #470 has no cycle up to length 8 (366952 inverting pairs, acyclic).
    Patterns with transposed letters (`pA` or `pB` > 0) are not handled.
- (w6-107c, 2026-09-18) **Level-transitivity of `⟨B⟩` (for #332 irreducibility): bounded search, nothing
  found.**
  - **Setting.** The stabilizer of `0` in `⟨B⟩` has Schreier generators
    `b1'b0, b1'b2, b1³, b2b1, b0b1, b1b2b1', b1b0b1'`. Its section group at `0` contains `b1'b0`,
    `b1'b2` and `b0b1` exactly, by word identities checked with the automaton word problem.
  - **No letter.** No letter `b_i`, and none of the other four generators, was found in that section
    group. The test compared level-4 permutations over a ball of 2·10⁵ elements.
  - **No self-replicating subgroup.** There is no 2-generated self-replicating subgroup `⟨x, y⟩`
    transitive on level 1 with `|x|, |y| ≤ 3` and stabilizer words of length `≤ 5`.
  - GAP computes the level-3 group of order 1632586752 and runs out of memory at level 4.
  - This is consistent with the index-3 non-congruence obstruction above. Level-transitivity stays open
    and needs a non-self-replicating argument.
- (w7-107, 2026-09-18) **Klein-power chains: `50_30` #470 and the transposed-letter patterns without a
  SAT solver (`bmw-census-klein-power-chain-certificates`).**
  - **Certificate.** A cycle may now mix inverting steps (K) with power steps (R): `x_i = r^e` and
    `x_{i+1} = r^f` with `1 ≤ |e| < |f|`, which force `|x_i| ≤ |x_{i+1}|` in any left order. These are
    checked by `verify_klein2.py`, which handles transposed letters, and re-checked by `crosscheck2.py`.
  - **#470.** Let `u = v0v1` and `t = h0h1h0`. The chain is
    `v2uv2 → (v2uv2)² → t h2h4 t → v0v2 u v2v0 → (v0v2 u v2v0)² → t h3h2 t → v2uv2`. It has two (R)
    steps and four (K) steps, and all words have length at most 8. The four (K) identities are checked
    by hand in §4 of the proof. It is a Promislow-type configuration: `t h2h4 t` inverts `x²` but not
    `x`.
  - **Transposed patterns.** At pure length 6, 167 of the 681 candidate classes of the sixteen
    patterns `31_*`, `41_*`, `42_*`, `50_31`, `51_*` and `52_*` are certified. So are the reducible
    Promislow-type classes `41_40` #1174 and `41_41` #486, #541.
  - **No pure inverting pair.** `31_30` #26 and `31_31` #12 have none up to length 8.
  - **Structure.** Every Klein pair `a b a^{-1} = b^{-1}` in `Γ^+` is `Γ`-conjugate to a pair of one
    pure `v`-word and one pure `h`-word. The proof uses the two tree actions: `b` is hyperbolic on
    exactly one tree, and `a` reflects its axis. So pure scans of growing length, together with
    conjugation, find every Klein chain.
  - **Not attempted.** Irreducibility of #332 by a route other than self-replication. It does not affect
    orderability of the three classes, which the pure four-term chains already settle.
