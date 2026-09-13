
## 34. The ternary V gate at <x_0, x_1, s>: mixed-prime breaks, generation, weakly finite images (w7-v-gate-c3; f5b2406fa, artifact `ternary-v-gate-joint-configuration-2026-09-12.md`)

I re-derived this at tip cd50958ab. The artifact (blob fe0a327b) is that of f5b2406fa. Since then the node has changed
only through w7-v-cycle-c3's scope fix a886f33f26 (34.6), which leaves the w7-v-gate-c3 entry unchanged.

### 34.1 Section 1 (which relation breaks the models): PASS

* **Claim 1.1.** `exp_2(t u) = 1 + t u`, so `1 − [tau_1] = −t u` has normalized rank `1/2`, and its square is `0`.
  [CG] Corollary 1.2 at `p = 3` gives `(1 − α)(3 − j)/3`. At `j = 2` this forces `α = 1`, and then `j = 1` gives
  `0 != 1/2`.
* **Claim 1.2.**
  * `1 − exp_3(t u) = −t u(1 + t u/2)`, and its square is `t^2 u^2` times a unit. The ranks are `2/3` and `1/3`, the
    regular profile, so `α = 0`.
  * The column `(1 − [tau_1], 1 − [tau_2])` kills exactly `u^2 L`, so the model's joint fixed rank is `1/3`.
  * On `F_3[E_2]` the same column kills only the constants, so Theorem 1.1 with `α = 0` gives `1/9`.
  * `E_2` alone suffices: `1 − [tau_1]` has regular rank `6/9`, which already forces `α = 0`.
* **Section 1.3.** `1 + [t] -> lambda e_12` has rank `1/2`, the regular value for `Z/2`, so `α = 0`. The column
  `(lambda_1 e_12, lambda_2 e_12)` kills `e_1`, so the fixed rank is `1/2`, not `1/4`.
* **Finite configuration.** With `q = 5` fixed, the contradiction lives on one finite `B ⋊ G`, but only through
  [PC] Section 1 (`k` cycles per piece, error `3n(|G| + 1)(1 − α) 5^(-k)`). [CG] Section 1 has error `2n|G|/q` and
  needs `q -> infinity`. For Claim 1.1, `n = 1` and `|G| = 3`, so `j = 2` needs `12 · 5^(-k) < 1/3`, and `k = 3`
  suffices. At `j = 1` the error carries the factor `1 − α = 0`.
* **Premises.** (R1)–(R3) are relations inside `B ⋊ G`. (R4), the torsion law, uses single-element `V`-conjugacy of
  clopen `q`-cycles through arbitrary conjugators in `V`. So "no `x_0`/`x_1` word" is right for identities, and the
  artifact's (R4) states the conjugacy premise correctly.
* **Section 1.4.** `t rk_sofic + (1 − t) rk_aug` satisfies Theorem 1.1 with `α = 1 − t` on the finite subgroups of a
  sofic `K`, and (T) with `a_q = 1 − t`. These relations separate the tree models from the mixtures, and they can't
  force `α in {0, 1}`.

### 34.2 Section 2.1 (generation): PASS, one wording slip

* **Item 1.** Every element of `F` sends the first leaf `0^a` to a first leaf and the last leaf to a last leaf, so it
  fixes `0^∞` and `1^∞`. The example `s` fixes `[11]`, so `<x_0, x_1, s> <= Stab_V(1^∞)`, which is proper.
* **Item 2.**
  * In binary, `x/2 + 3/4`, `2x − 1` and `x − 1/4` are `0w -> 11w`, `10w -> 0w` and `11w -> 10w`, so `C^3 = 1`.
  * Refining gives `c' = (00 -> 110 -> 100)` and `c'' = (01 -> 111 -> 101)`, disjoint, with `c' c'' = C`.
  * `<A, B, C> = T` is [CFP] Section 5, taken as cited.
  * Item 1's `s` sends `(00, 01, 10, 11)` to `(01, 10, 00, 11)`. That isn't a rotation, so `s` is not in `T`, and
    `T != V`.
* **Slip.** `C` is not a clopen 3-cycle in the node's sense.
  * Its three cylinders cover `X`, so it has no fixed points.
  * `Fix(h s h^(-1)) = h Fix(s)`, so `C` isn't `V`-conjugate to a clopen 3-cycle.
  * Where to fix it: the artifact's "a clopen 3-cycle whose three cylinders cover X" and the node entry's
    "(a clopen 3-cycle)" should say "a product of two disjoint clopen 3-cycles".
  * The law still applies to `C`, through Theorem 1.1 on `<C>`.
* **Observation, not in the artifact.** `T` contains no clopen 3-cycle.
  * A nontrivial finite-order orientation-preserving circle homeomorphism has no fixed point. If it fixed a point,
    cutting there would give an increasing interval map, and `f(x) > x` gives `f^n(x) > x`.
  * A clopen 3-cycle fixes a nonempty clopen set.
  * So `c'` and `c''` lie outside `T`. For a matrix over `F_3[T]`, the Theorem 1.1 input is `<C>` and the other finite
    subgroups of `T`. The Next lead's sentence about `<c', c''>` is true in `V`, but it gives no entries of `F_3[T]`.
* **Criterion.** The clopen 3-cycles with nonempty complement form one class ([TS] Lemma 1.1). So they generate a
  nontrivial normal subgroup, which is `V` by simplicity, and the "iff" holds. The example `00w -> 11w -> 01w -> 00w`
  moves both endpoints and is not in `T`.

### 34.3 Sections 2.2–2.3: PASS as a record

* **Convexity.** The equivalence "gate iff `phi_V in {0, 1}`" was re-derived in §33.4.
* **Excluded list.** It matches [FW] (§31) and [FR] Section 3.2 (§30).
* **Linear soficity.** An ultralimit of normalized ranks over `F_3` is a rank function on `F_3[V]`. The rank-distance
  bound gives `rk(1 − [g]) > 0`, so `phi_V < 1` by [FR] Corollary 1.3(3).
* **Citation slip.** The Notation paragraph cites §33.4 for Theorem 1.1. That theorem is verified in §32.1. The second
  derivation is §33.2, and §33.4 is the ternary-gate section.
* **Stale remark.** The Splitting paragraph says `w7-v-rank-split` has no landing at ff83a99a9. That lane landed
  3756340b8 (node `v-rank-functions-split-as-augmentation-plus-reduced`). I haven't re-derived it.

### 34.4 Section 3 (what a phi_V < 1 model would do): PASS, two wording notes

* **Claim 3.1(1)–(2).**
  * **The ideal.** `I` is a two-sided ideal, by subadditivity and `rk(ab) <= min(rk a, rk b)`. `rk` descends to
    matrices over `W_V`.
  * **Weakly finite.** If `XY = I_n` over `W_V`, then `YX` is idempotent, and `rk(YX) >= rk(XYXY) = n`. So
    `rk(I_n − YX) = 0`, and each entry `e_i^T (I_n − YX) e_j` lies in `I`. `1` is not in `I`, so `W_V != 0`.
  * **Injective on V.** `{g : rk(1 − [g]) = 0}` is closed under products (`1 − [gh] = (1 − [g]) + [g](1 − [h])`),
    inverses and conjugation. By Corollary 1.2 at `j = 1` it misses a clopen 3-cycle, so it is trivial. Then
    `[g] − [h] = [g](1 − [g^(-1) h])` has positive rank for `g != h`.
* **Claim 3.1(3).**
  * **Moves z.** The embedding `E ⋊ V -> V` sends `z` to `sigma_0`. Theorem 1.1 on `<sigma_0>` over `F_3` gives
    `rk(1 − [sigma_0]) = (1 − phi_V)/2 > 0`.
  * **The factor.** Over `F_3`, `eps_- = (1 − [z])/2 = [z] − 1` is a central idempotent. The factor `eps_- W'` of the
    null quotient `W'` of `F_3[E ⋊ V]` is a nonzero quotient of `eps_- F_3[E ⋊ V]`. It is weakly finite as a direct
    factor of `W'`.
  * **Contrapositive.** A proof that `eps_- F_3[E ⋊ V]` has no nonzero weakly finite quotient proves the gate. This
    sharpens line 61 of `ternary-anti-central-summand-has-no-weakly-finite-image`.
* **Claim 3.2.** This is a non-implication, and it is accurate. [VX] Sections 1.2–1.3 and Corollary 5.1 are taken as
  cited.
* **Claim 3.3.**
  * **The cases.** They are [VX] Proposition 5.2 (artifact lines 359–376).
  * **Injective on `PG_3`.** This uses [VX]'s statement that the normal subgroups of `G_3` are `1`, `<z>` and `G_3`,
    taken as cited.
  * **Wording.** In the first case, the nonzero weakly finite quotient of `S_-` is the image `rho(S_-)`. The corner
    `rho(eps_-) W rho(eps_-)` contains it and is weakly finite, since `XY = e` gives `(X + 1 − e)(Y + 1 − e) = 1`, but
    the corner itself isn't a quotient.
  * **Wording.** "Any weakly finite obstruction has to use letters of `G_3` outside `E ⋊ V`" overstates. An
    obstruction confined to `E ⋊ V` isn't excluded. It would prove the gate, and with it non-soficity of `V`.

### 34.5 Scan, node display and verdict

* **Scan.** I ran `git grep` over `research/*.md` at tip, without truncation, for "weakly finite image of V", "null
  quotient" (19 files), `Stab_V` (12), "Cannon–Floyd" (23), "x_0, x_1, C", "mixing two primes|mixed-prime" and
  `rk(a) = 0}`.
  * **ESTABLISHED hits.** `two-root-gate-lower-bounds-hold-for-matrix-states` (a null quotient of matrix states on the
    Leavitt side), plus `bleak-quick-finite-presentations-of-thompson-v` and
    `thompson-v-small-windows-have-finite-separations` (presentations).
  * **Result.** None covers Claims 1.1–3.3.
* **Node display.** The entry matches the artifact, apart from the "(a clopen 3-cycle)" slip of 34.2.
* **Not decision-level.** No rank function on `F_3[V]` is built, and no identity is proved.
* **Verdict: partial.** Sections 1–3 are re-derived, except the cited inputs: [CFP] `T = <A, B, C>`, [VX] Sections
  1.2–1.3, Corollary 5.1, Proposition 5.2 and the normal subgroups of `G_3`.
  * Claims 1.1 and 1.2 and the Section 1.3 computation: PASS.
  * Section 1.4 and Sections 2.2–2.3: PASS.
  * Claim 2.1 (items 1–2) and the criterion: PASS, with the wording fix for `C`.
  * Claims 3.1–3.3: PASS, with the two wording notes.
  * `thompson-v-ternary-rank-functions-are-augmentation` stays OPEN.
