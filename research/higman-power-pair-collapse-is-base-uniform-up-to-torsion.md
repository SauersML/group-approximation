---
rg: 2
id: higman-power-pair-collapse-is-base-uniform-up-to-torsion
kind: claim
title: The power-pair collapse of Higman's group uses base two only through torsion, and for odd bases there are nontrivial quotients with infinite virtually cyclic edge image
distinct_from:
  higman-elementary-amenable-edge-images-collapse: that proves the dichotomy and the collapse for base two; this proves that the dichotomy and the power-pair closure hold verbatim for every base n, that for base n they force torsion generators rather than collapse, and that for odd n this is sharp.
  nontrivial-higman-quotients-keep-all-four-bs-subgroups: that is the base-two torsion lemma; this locates it as the only base-two input in the whole descent-chain programme.
  higman-bounded-derived-length-edge-images-collapse: that certifies derived length at most 11 for base two; this is a calibration across bases and does not reprove any derived-length case.
artifacts:
  - experiments/higman-base-n-calibration-2026-09-18/base_n_quotients.py
  - experiments/higman-base-n-calibration-2026-09-18/base_n_quotients-output.txt
---

**ESTABLISHED** (proposed) by `higman-power-pair-collapse-is-base-uniform-up-to-torsion-proof`.

**Setting.** For `n >= 2` let
`H4(n) = < a, b, c, d | b^a = b^n, c^b = c^n, d^c = d^n, a^d = a^n >` (`x^y = y^-1 x y`), so
`H4 = H4(2)`. For a quotient `Q` put `A_M = <a^M, c^M> <= Q` and `A = A_1`. Let `X` be the class of
`higman-elementary-amenable-edge-images-collapse` (the closure of finite, abelian and
free-subgroup-free locally indicable groups under extensions and directed unions; it contains every
elementary amenable group).

**Statement.**
1. **Base-uniform dichotomy.** For every `n >= 2`, every quotient `Q` of `H4(n)` and every `M >= 1`,
   `A_M` is free on `a^M, c^M` or `A_M / A_M'` is finite.
2. **Base-uniform closure.** For every `n >= 2`: if `A` lies in `X`, then some `A_M` is finite, and all
   four generators of `Q` have finite order.
3. **Base two.** For `n = 2` the last conclusion forces `Q = 1`. This is the only place in the
   dichotomy, the closure and the collapse where `n = 2` is used.
4. **Sharpness for odd bases.** For every odd `n >= 3`, `a, c -> (x,y) |-> (-x,y), (1-x,y)` and
   `b, d -> (x,y) |-> (x,-y), (x,1-y)` define a quotient `Q = D_oo x D_oo` of `H4(n)` whose edge image
   `A = <a,c>` is the infinite dihedral group: infinite, virtually cyclic, amenable, with `A/A'` finite
   and `A_2 = 1`. For every `n >= 3`, `(Z/(n-1))^4` is a quotient with nontrivial finite edge image.
5. **Structure of the base-two residue.** If `Q` is a nontrivial quotient of `H4` whose edge image `A` is
   not free-on-every-power (for example `A` amenable), then for every `M`: `A_M'` has finite index in
   `A_M`, so it is finitely generated; `A_M / A_M''` is virtually free abelian of finite rank; and
   `a, c` have infinite order while no `A_M` is finite.

**What it kills.** The whole descent-chain programme (tower invariants, the chain, the parity flip, the
dichotomy and the power-pair closure) is a theorem about `H4(n)` for every `n`. In base `n` odd it
cannot prove more than "the generators are torsion", because `D_oo x D_oo` exists. So:
- no argument that only uses the substitution lemma `ev(iota_b(w)) = b^-1 ev(w) b` and properties of
  `A` can prove that an infinite amenable (even virtually cyclic) edge image collapses;
- every extension of the collapse to amenable edge images must use base two, and through the
  power-perfect regime with **infinite-order** generators. The only known base-two input is the
  smallest-prime torsion lemma, which the chain reaches only after some `A_M` is finite.
- Hence the remaining case is exactly the base-uniform question: *does every amenable power-perfect pair
  `(A; a, c)` realized in a quotient of some `H4(n)`, with `a, c` of infinite order, have a finite power
  subgroup?* A counterexample in an odd base would show that base two must enter a second time.

**The finer invariant it points to.** By item 5 the next invariant is `b_1(A_M') = rank(A_M'/A_M'')`,
the rational abelianization of a finite-index subgroup. The chain controls `A_M/A_M'` (it is finite).
Showing `b_1(A_M') = 0` for all `M` is the next rung. It would still not collapse perfect edge images such
as simple amenable groups, which is why item 4's base-uniformity matters.

## Attempts

- **w9-053 (question (a), odd base).** Landed `higman-edge-closure-absorbs-b-powers` (00bd4a967).
  - In every finite or profinite image, a relation `w` of `A_M` puts `b^(n^|e_a(w)| - 1)` and
    `d^(n^|e_c(w)| - 1)` into the closure of `A_M`.
  - So if a profinite image (for example `Aut(T)`) has no power of `b` in `cl(A)`, then `A` is free.
  - Consequences for (a):
    - odometer, level-separated, independent-tree and matched-pair (exact-factorization)
      constructions all give free `A`;
    - a residually finite counterexample must be "diagonal", with `b^(n^Y - 1)` in `cl(A)`.
  - Dead ends: linear quotients (all generators torsion) and topological full groups of minimal
    Z-systems (only finite orbits).
  - Evidence:
    - the universal pro-2 quotients of `H4(3)`, `H4(5)`, `H4(7)` up to class 6 are exact products
      `A_k B_k`;
    - in `H4(3)/<<[a,c]^2>>`, the least `s` with `b^(2^s)` in `A_k` stabilizes at the predicted
      `v_2(3^16 - 1) = 6`, while `ord(a)` keeps growing and `A^ab = (Z/16)^2`.
  - Next: decide whether the residually-2 image of `H4(3)/<<[a,c]^2>>` has infinite-order
    generators and an amenable edge image, or prove the pro-2 exact-product theorem.
- **w10-053 (question (a): discrete absorption and a host obstruction).** Landed
  `non-free-higman-edge-images-contain-bs1n-subgroups` (claim and proof route).
  - Discrete absorption. In `Q` itself, not only in a closure, a relation `w` of `A` with
    `e_a(w) = Y != 0` puts `b^(n^N (n^|Y| - 1))` into `A`. The same holds for `d`, and by the
    cyclic symmetry for `B`.
  - So a non-free `A` whose generators have infinite order contains `<a, b^m> ≅ <c, d^m'> ≅ BS(1,n)`.
  - Consequences:
    - `A` has no faithful action of subexponential orbit growth. This kills `[[X, T]]` for every
      `Z^d`-action (all minimal Cantor `[[T]]` included), `IET`, `W(Z^d)`, and groups of
      intermediate growth as hosts for (a). The w9-053 dead end becomes a theorem.
    - The spark is proved in general: if `H4(n)` maps to a group of subexponential orbit growth,
      the generators map to torsion elements, and for `n = 2` the map is trivial.
  - One-directional reduction. An amenable counterexample to (a) yields an amenable quotient of
    `H(n^k', n^L, n^k, n^L)` inside `A ∩ B` that is generated by `b^L, d^L`.
  - Data. `experiments/higman-diagonal-pro2-2026-09-18/diag_tower.g` and
    `diag_tower-output.txt` compute `H4(3)/<<[a,c]^2>>`, universal pro-2 quotients, classes 1 to 11.
    - The log2 orders of `(a, b, c, d)` at classes 9, 10, 11 are `(6,6,6,6)`, `(6,7,6,7)`,
      `(7,7,7,7)`.
    - `A^ab = (Z/16)^2` from class 4 on.
    - `log2|A_k|` is `114, 179, 291`, against `log2|B_k|` of `281, 494, 883`.
    - `B^ab` goes `(Z/64)^2`, then `Z/64 x Z/128`, then `(Z/128)^2`, so it does not stabilize.
    - The least `s` with `b^(2^s)` in `A_k` is 6 from class 6 on, and `b^64` is nontrivial once
      `ord(b) = 128` (classes 10 and 11). No nontrivial power of `a` lies in `B_k` through class 11.
    - `b_pair_free.g` finds `B_k` below the free pro-2 orders from class 7 on
      (`log2|B_7| = 94` against 96).
  - Reading. `A` looks amenable-like (bounded abelianization, slower growth), `B` looks free-like, and
    the diagonal absorption predicted by item 1 is visible. Infinite order of the generators is still
    undecided.
  - Dead: p-adic analytic images, where ad-nilpotency forces torsion generators, and every host of
    subexponential orbit growth.
  - Next: a candidate for (a) must live in an exponential-activity host.
    - Option 1: build an automaton or `Aut(T_2)` model of `H4(3)/<<[a,c]^2>>` in which `BS(1,3)`
      sits inside `A`.
    - Option 2: prove continuity of the matched-pair transducer action of `H4(n)` on
      `(Z_2 * Z_2)`-words with `Z_2` exponents.
- **w12-053 (question (a): the edge-group Freiheitssatz is false).** Landed
  `higman-edge-relator-twist-breaks-tree-lattice-freiheitssatz` (claim and proof route).
  - Reduction tested. The w11 reduction asks that `<a,c>/<<[a,c]^2>>` embed in
    `<a,b,c>/<<[a,c]^2>>` inside `Gamma(3, 2^e)`, for infinitely many `e`.
  - Result: the embedding fails for every `m = 2^e >= 8`.
    - Conjugating by `b` gives `b^-1 [a,c] b = a^-1 c^-lambda a c^3`, where `lambda = 3^(3^-1 mod m)`
      and `lambda = 3 mod 8`.
    - So `S = (a^-1 c^-lambda a c^3)^2` is a conjugate of `R` that lies in `<a,c>`.
    - `S` survives in a class-7 2-quotient of `<a,c | a^8, c^8, [a,c]^2>`.
  - The same twist proves the w9/w10 observations as bounds. In every quotient with 2-power-order
    generators:
    - `A^ab` is a quotient of `(Z/16)^2`;
    - `b^64` and `d^64` lie in `A`, because `e_c(S)` has 2-adic valuation 4.
  - For `e >= 7`, `<<R>>` is not inside `A`, and no splitting over the image of `A` keeps index `m`.
  - Dead: every argument that routes `ord(a) = 2^e` through the A-splitting.
  - Next: the B-splitting Freiheitssatz, that `<d,a,b>` embeds in `Gamma(3,2^e)/<<[a,c]^2>>`.
    Over `<b,d>`, `R` is an exponent-2 proper power of length 8. Alternatively, pro-2 growth of
    `ord(a)` compatible with `b^64 in A`.
- **w11-053 (question (a): the torsion regime is a family of tree lattices).** Landed
  `higman-torsion-generator-quotients-factor-through-tree-lattices` (claim and proof route).
  - Universality. Every quotient of `H4(n)` whose four generators are torsion, with lcm of orders
    `m`, has `m | n^m - 1` and factors through `Gamma(n,m) = H4(n)/<<a^m,b^m,c^m,d^m>>`.
  - Structure. `Gamma(n,m) = K1 *_A K2 = L1 *_B L2`, with vertex groups `Z/m ⋊_n Z/m` and
    `A ≅ B ≅ Z/m * Z/m` of index `m`. It is a uniform lattice in `Aut(T_m) x Aut(T_m)`, and its
    generators have order exactly `m`. Item 4 here (`D_oo x D_oo`) is the case `m = 2`, and the
    base-two torsion lemma is the arithmetic fact that `m | 2^m - 1` forces `m = 1`.
  - Reduction for (a) with `R = [a,c]^2`. If `A/<<R>>` embeds in `K_i/<<R>>` for `m = 2^e` and
    infinitely many `e`, then `a` has infinite order in `H4(3)/<<[a,c]^2>>`. This holds when
    `m | n + 1` (Kaloujnine–Krasner coordinates), so `Gamma(3,4)/<<[a,c]^2>>` is an amalgam and `a`
    has order 4 there. At `m = 8, 16` the induced representation is certified not to kill `R`.
  - Data. `Gamma(3,2^e)` is virtually torsion-free for `e <= 5`: all four vertex groups inject into
    a finite 2-quotient. In `Gamma(3,2^e)/<<[a,c]^2>>`, `ord(a) = 2^e` for `e <= 5`.
  - Dead: short self-similar models. All 8450 cyclically symmetric wreath recursions on `T_2` with
    sections of length at most 2 give `ord(a) <= 2` at level 10. By universality, every
    finite-level image is a quotient of some `Gamma(3,2^e)`.
  - Next: prove a Freiheitssatz for the proper power `[a,c]^2` over `K1 = G(a,b) *_<b> G(b,c)` for
    `m = 2^e >= 8`, that is, `A/<<R>>_A` embeds in `K1/<<R>>_K1`. With the proof's Lemma 6.1 and
    Corollary 6.2 this settles infinite order in (a). Amenability of `A` stays open.
- **w13-053 (question (a): the B-splitting, via the tree kernels).** Landed
  `higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7` (claim and proof route).
  - For every `e >= 3`, `b^(m/4)` and `d^(m/4)` fix all of `T_B`. So the kernel `Lambda_B` of the
    B-tree action is infinite. As a consequence, `L1 = <d,a,b>` never embeds in `Gamma/Lambda_B`,
    and the B-splitting Freiheitssatz cannot be reached through the tree action.
  - For `e <= 7`, `Gamma(3,2^e)` is a reducible lattice (virtually `F x F`), with
    `[B:Lambda_B] = 2^2, 2^4, 2^6, 2^9, 2^13`.
  - Reduction. If each B-twist of `R` has its B-part in `Lambda_B`, then `A` embeds in
    `Qbar_B = Gamma/Lambda_B<<R>>` as the explicit 2-generator group `Abar_e` of index
    `|B/Lambda_B|`.
  - Certified for `e = 3..6`: `ord(a) = 2^e`, an independent route to the known bound.
  - Obstruction: for every `e >= 9` the hypothesis fails. The w12 relation `b^64 in Abar` forces
    `m/4 | 64`, and `beta = b d` gives `beta'' = b^320` at `e = 9`.
  - Dead: irreducibility via infinite-order sections, and GAP Reidemeister–Schreier presentations of
    `<a,c> <= Qbar_B`.
  - Next: describe `<<R>>_{Q_B}`, which is no longer inside `A` for `e >= 9`, together with a
    subgroup `A · Bbar_0` containing it. Separately, decide reducibility of `Gamma(3,2^e)` for
    `e >= 8`.
- **w14-053 (question (a): relative Freiheitssatz at e = 9, reducibility at e = 8, 9).** Landed
  `higman-b-twist-hypothesis-holds-exactly-for-e-at-most-8` (claim and proof route).
  - `Bbar_e = B/Lambda_B` is a finite self-similar group on the `m`-ary word tree, and is computed
    exactly with every level verified. Its order is `2^6, 2^9, 2^13, 2^17, 2^22` for `e = 5..9`.
    So `Gamma(3,256)` and `Gamma(3,512)` are reducible lattices.
  - w13's twist hypothesis `(H_e)` holds if and only if `e <= 8`: all `beta'' = 1` at `e = 7, 8`.
    So `Abar_e` embeds in `Qbar_B` with index `|Bbar_e|` for `e <= 8`.
  - At `e = 9`, `<<[a,c]^2>>_(Q_B)` lies in `A ⋊ <b^64, d^64>`, where `<b^64, d^64> = (Z/2)^2` is
    the minimal choice. So the edge image has index exactly `2^20` in `Qbar_B`, with an explicit
    2-generator presentation. This embedding is exact and gives no bound by itself.
  - `ord(a) >= 2^7` in `Gammabar_e` for all `e >= 7`.
  - At `e = 9`, every 2-quotient of class at most 10 has `ord(a) <= 2^8`. The `d^64` relation is
    what caps it.
  - Next: decide whether that cap persists in all classes (ANUPQ with a larger budget, and the
    `e = 10` analogue).
- **w15-053 (question (a): ord(a) = 2^e for e <= 10; the d^64 cap is not class-uniform).** Landed
  `higman-a-has-order-2e-in-gamma-3-2e-mod-r-for-e-le-10` (claim and proof route).
  - Method: the standalone ANU p-Quotient Program (ANUPQ 3.3.3). It computes the largest
    lower exponent-2 class-`k` quotient of `Gammabar_e = Gamma(3,2^e)/<<[a,c]^2>>` directly, with a
    budget of hours instead of 1200 s. Any finite quotient with `a^(2^(e-1)) != 1` certifies
    `ord(a) = 2^e`, even if extra relators were added.
  - `e = 10`: add to `Gammabar_10` 500 short B-tree relators, found by a table-free level-3 search
    (`evalk.py`, `ballk.py`). The class-18 quotient then has order `2^10034` and `a^512 != 1`. So
    `ord(a) = 2^10`.
  - `e = 9`: `Gammabar_9`'s class-16 quotient has order `2^21418` and `a^256 != 1`. `Qbar_B` gives
    the same independently: class 16, order `2^3521`, using 1000 relators whose largest
    2-quotient is exactly `Bbar_9`.
  - `e = 8`: class 14, order `2^6510`, and `Qbar_B` at order `2^1272`.
  - Hence `ord(a) = 2^e` in `Gammabar_e` for every `e <= 10`, and `ord(a) >= 2^10` in
    `H4(3)/<<[a,c]^2>>` (previously `2^7`).
  - The brief's alternative is decided on the "break" side. w14's `Etest2` reaches `ord(a) = 2^9` at
    class 13 (order `2^918`); it keeps `2^8` at classes 11–12.
    - The same holds with `U^2`, `V^2` and `[U,V]` added.
    - `Etest10` gives `2^9` at classes 15–16.
    - `Gammabar_9`'s own ceilings are: `2^8` through class 15, and `2^7` through class 13.
  - First certifying class: `9, 11, 14, 16, 18` for `e = 6..10`. At `e = 10`,
    `ord(a) = 2^(k/2+1)` for even `k = 12..18`.
  - Dead: `Gammabar_9` at class 17 (about `2^38000`). Adding relators of a truncated level can
    kill `a`: level-2 relators give `2^6` at `e = 9`.
  - Next: `e = 11`, which needs class 20, at about `2^29000`. That is beyond 2 GB, so it needs
    more `Bbar_11` relators checked at level 4–5, or a larger workspace. For all `e`, look for a
    uniform family of finite 2-group quotients read off from the class-18 presentation.
- **w16-053 (question (a): uniform models of ord(a) = 2^e need exponential rank).** Landed
  `higman-order-2e-models-need-exponential-rank` (claim and proof route).
  - Proved, for every quotient of `H4(3)`:
    - If `2^e | ord(a)`, then `2^(e-2) | ord(d)`, `2^(e-4) | ord(c)` and `2^(e-6) | ord(b)`.
    - Every linear representation over any field in which `a` keeps order `2^e` has degree at least
      `2^(e-2)`. In characteristic 2 the bound is `2^(e-1) + 1`.
    - A model of level `e` (a finite quotient of `Gammabar_e` with `a^(2^(e-1)) != 1`) has order at
      least `2^(2e-2)`.
  - So no family of models of unbounded level lies in `GL_n` of fixed `n` over any fields. The
    brief's "p-adic analytic family" is dead at finite level. A uniform family must be of wreath or
    Sylow type, with linear rank at least `2^(e-2)`.
  - Computed (GAP on ANUPQ exports, greedy): monolithic models obtained by killing hyperplanes of
    `Omega_1(Z)`.
    - Smallest orders `2^8`, `2^12` and at most `2^50` for `e = 3, 4, 5`.
    - Faithful irreducible degrees `8 = 2^e` (at `e = 3`) and `32 = 2^(e+1)` (at `e = 4`).
    - Core-free permutation degrees 32 and 256. `a` is always semiregular.
    - Order profiles are balanced, never near the extreme `(e, e-6, e-4, e-2)`.
  - Not attempted: `e = 11`. The host ran at load 30 on 4 cores, and a class-20 pq run gets about 5%
    of a core inside the 1200 s cap.
  - Dead: fixed-degree matrix, arithmetic and affine families, and `GL_n(Z/p^j)` with `p` odd.
  - Next: embed the `e = 3, 4` models (in `mono3.g`) into `W_5` and `W_8` via their core-free
    actions (`perm.g`), and read off the wreath sections of `a, b, c, d`. Then look for a recursion
    `Q_(e+1) -> Q_e wr C_2`, which would be a self-similar model beyond w11's length-2 search.
    Separately, run `e = 11` at class 20 when the host is idle.
- **w17-053 (question (a): self-similar models with a as odometer).** Landed
  `higman-h4-3-has-no-odometer-models-beyond-level-five` (claim and proof route).
  - Blocked step. The brief asked to embed the `e = 3, 4` monolithic models in `W_5, W_8` and find a
    recursion `Q_(e+1) -> Q_e wr C_2`. In those models `a` is semiregular with `2^(k-e)` cycles. The
    natural recursion makes `a` level-transitive (the adding machine `a = (1, a) s`), and that is
    impossible.
  - Computed (exhaustive, exact `F_2`-linear lifting level by level in `W_k`, up to conjugation by
    `<a>`): no homomorphism `H4(3) -> W_k` with `k >= 6` sends a generator to a `2^k`-cycle, even
    without `R`.
    - Equivalently, no finite 2-quotient has an exact factorization `<x> H` with `ord(x) >= 64`.
    - So no action of `H4(3)` on `T_2`, self-similar or not and with sections of any length, has a
      level-transitive generator. This extends w11's length-2 dead end.
    - Odometer models: with `R`, `8, 32, 192, 1536, 11776` raw at levels 1 to 5 (classes
      `8, 16, 48, 192, 736`). Without `R`, `8, 32, 288, 4352` raw at levels 1 to 4 (classes up to
      9728 at level 5). None at level 6.
    - Raw counts agree with an independent GAP enumeration.
  - Proved: in any odometer model `d(x) = 3x + t`, of order `2^(k-2)` or `2^(k-1)` as `t` is even or
    odd.
    - At level 5 every model has `t` even, `ord(d) = 8` and `ord(b), ord(c) <= 4`. These are very
      unbalanced models of degree 32, unlike the balanced monolithic ones.
    - A conceptual proof of the level-6 wall is open. The order ladder alone does not give it.
  - Dead: odometer, adding-machine and every level-transitive self-similar model of `H4(3)` or
    `H4(3)/<<[a,c]^2>>`.
  - Next: tree models in which `a` has infinite order but is not level-transitive. The first family
    is the `j`-odometer `x -> x + 2^j`.
    - For `j = 1` (`bfs2.py`, with `R`) there are 96, 752, 9152 and 229376 classes at levels 2 to
      5, with max log2 orders `(4, 3, 4, 4)` at level 5. This family is alive and growing where the
      odometer family has 736 classes and dies.
    - Level 6 and beyond (the question is whether `ord(a) = 2^(k-1)` persists) needs a C
      implementation or the full `W_1 x| translations` symmetry.
    - If the `j`-odometer counts also die, the next families are elements `a` that are
      level-transitive only on some subtree, and trees of degree `2^s`.
