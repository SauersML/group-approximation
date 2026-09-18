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
