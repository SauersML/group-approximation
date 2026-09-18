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
