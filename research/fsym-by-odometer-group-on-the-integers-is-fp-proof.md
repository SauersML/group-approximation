---
rg: 2
id: fsym-by-odometer-group-on-the-integers-is-fp-proof
kind: route
title: Present FSym(X) by all transpositions with conjugation relations, let Q permute them with finitely many orbits, and check the orbit and stabilizer conditions for the odometer group on the integers by prefix surgery near 0 and -1
target: fsym-by-odometer-group-on-the-integers-is-fp
requires:
  - odometer-prefix-groups-have-fg-index-kernels
  - thompson-v-binary-shell-action-passes-both-germ-gates
  - odometer-kernel-preimage-is-strongly-shift-similar
  - houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group
  - finitary-mixing-of-fp-highly-transitive-groups-is-fp
---

Lane proof, elementary, not independently reviewed.

## 1. The lemma

This is the semidirect-product presentation method of Martínez-Pérez–Matucci–Nucinkis (Lemma A.1, as described
in Nucinkis–St. John-Green arXiv:1412.7715 §4, used there for `Q~V`). Here it is written out for `FSym`.

- **Presentation of FSym(X).** Generators are all transpositions `τ_p`, one for each 2-subset `p`. Relations are
  `τ_p^2 = 1` and `τ_p τ_q τ_p = τ_(τ_p(q))`. For finite `X` these relations imply the Coxeter relations on
  adjacent transpositions, and every `τ_p` is a conjugate of those. So they present `S_n`; take the direct limit.
  This presentation is also used in `finitary-mixing-of-fp-highly-transitive-groups-is-fp`, Step 3.
- **The presented group B~.**
  - Choose representatives `p_1, ..., p_r` of the `Q`-orbits of 2-subsets (finitely many by the `X^4` hypothesis).
  - Generators: a finite generating set `S` of `Q`, and letters `t_1, ..., t_r`.
  - (R1) a finite presentation of `Q` on `S`;
  - (R2) `[t_i, u] = 1` for `u` in a finite generating set of `Q_(p_i)`, the setwise stabilizer;
  - (R3) `t_i^2 = 1`;
  - (R4) for one representative `(p, q)` of each `Q`-orbit of ordered pairs of 2-subsets (finitely many, being
    images of 4-tuples), the relation `τ~_p τ~_q τ~_p = τ~_(τ_p(q))`. Here `τ~_p = w^-1 t_i w`, where `w` is a
    fixed word with `w(p) = p_i`.
- **Step 1.** `Q~ = <S> <= B~` is a quotient of `Q` by (R1), and it maps onto `Q`. So `Q~ ≅ Q`.
- **Step 2.** Suppose `w, w' ∈ Q~` both send `p` to `p_i`. Then `w' w^-1 ∈ Q_(p_i)`. By Step 1 it is a product of
  the (R2) generators, so it commutes with `t_i`. Hence `τ~_p = w^-1 t_i w` is well defined for every `p`, and
  `q τ~_p q^-1 = τ~_(q(p))` for all `q ∈ Q~`.
- **Step 3.** By `Q~`-equivariance, (R4) holds for every ordered pair `(p, q)`, and (R3) gives `τ~_p^2 = 1`. So
  `K~ = < τ~_p >` is a quotient of `FSym(X)`. It maps onto `FSym(X)` by `τ~_p -> τ_p`, so `K~ ≅ FSym(X)`.
- **Step 4.** `K~` is normalized by `Q~` and contains every `t_i`, so `B~ = Q~ K~`. If `qk` maps to `1` in
  `FSym(X) ⋊ Q`, then projecting to `Q` gives `q = 1`, and then `k = 1`. So `B~ ≅ FSym(X) ⋊ Q`. ∎

## 2. The odometer group on Z

- **B preserves Z.** A table entry `u z -> v a^c(z)` sends eventually constant `z` to eventually constant
  sequences, and so does its inverse. `a` is `n -> n+1` on the 2-adic expansions.
  - *Faithful, meeting FSym(Z) trivially.* `Z` is dense, and `b ≠ 1` moves a nonempty open set. So `b` moves
    infinitely many integers.
  - So `FSym(Z) B <= Sym(Z)` is the semidirect product `FSym(Z) ⋊ B`.
- **Orbits.** Let `Z_+ = {n >= 0}` (eventually 0) and `Z_- = {n < 0}` (eventually 1).
  - *Tuples of a fixed type.* Take `k` distinct points, and choose `m` beyond the last digit change of each. Their
    length-`m` prefixes are distinct, and each point is its prefix followed by a constant tail.
  - The type of a point (which of `Z_+`, `Z_-`) is its tail. `V` preserves types. The `V` argument of
    `odometer-kernel-preimage-is-strongly-shift-similar-proof` §2(b), with `k` prefixes instead of 2, sends any
    such `k`-tuple to any other `k`-tuple of distinct points with the same type pattern.
  - So `V`, and hence `B`, has finitely many orbits on `Z^4`: at most one per coincidence pattern and type pattern.
- **Transitive on ordered pairs.** Let `x ≠ y`.
  - If `x > y`, then `a^(-y-1)` sends `(x, y)` to `(x-y-1, -1)`, which lies in `Z_+ x Z_-`.
  - If `x < y`, first apply `a^t` to make both negative, then an element of `V` reversing their order inside `Z_-`
    (`V` is 2-transitive there), then the previous case.
  - Finally `V` is transitive on `Z_+ x Z_-`. So `B` has one orbit on ordered pairs, and one orbit of 2-subsets,
    represented by `{0, -1}`.
- **Stabilizer of (0, -1).** Let `b` fix `0 = 0^∞` and `-1 = 1^∞`.
  - The leaf of `b` containing `0^∞` is some `0^m`, with entry `0^m z -> v a^c(z)`. Since `a^c(0^∞)` is the 2-adic
    integer `c`, fixing `0^∞` forces `c = 0` and `v = 0^(m')`. Likewise at `1^∞` the entry is `1^l z -> 1^(l') z`,
    because `a^c(1^∞) = c - 1`.
  - So `b -> (m' - m, l' - l)` is a homomorphism onto `Z^2`, with kernel `K_0 = ∪ B[U_(m,l)]`. Here
    `U_(m,l) = {0,1}^N \ (0^m ∪ 1^l)`, and `B[U]` is the subgroup supported in `U`.
  - Let `x_0 ∈ V` be `000z -> 00z`, `001z -> 010z`, `01z -> 011z` on the cone `0`, and the identity on the cone `1`.
    Let `x_1` be the same with the digits exchanged. Then `x_0 U_(m+1,l) = U_(m,l)` and
    `x_1 U_(m,l+1) = U_(m,l)` for `m, l >= 2`. So every `B[U_(m,l)]` is conjugate into `B[U_(2,2)]` by powers of
    `x_0` and `x_1`.
  - `U_(2,2)` is the union of the cones `01` and `10`, and `B[U_(2,2)] ≅ V_(2,2)(<a>)`. That group is of type
    `F_infinity`, hence finitely generated (Belk–Hyde–Matucci Theorem 2.12, via
    `odometer-prefix-groups-have-fg-index-kernels`, which states it for all `V_(h,r)(<a>)`).
  - So `Stab_B(0) ∩ Stab_B(-1) = < B[U_(2,2)], x_0, x_1 >` is finitely generated. It has index at most 2 in the
    setwise stabilizer.
- **Conclusion.** `B` is of type `F_infinity`, so it is finitely presented. The lemma gives `L_od` finitely
  presented. `a` acts on `Z` as the translation, so `<FSym(Z), a> = FSym(Z) ⋊ Z = H_2`.

## 3. Copies inside H_n(G_od)

- **c normalizes B.** `c` conjugates `V` to itself (it complements prefixes) and `a` to `a^-1`. So `cBc = B`, and
  `chi(cbc) = -chi(b)`: both sides are homomorphisms agreeing on `V` and `a`.
- **The embedding.** Let `X_ij = ({i} ∪ {j}) x N`, with `(i,m) -> m` and `(j,m) -> c(m) = -1-m`, so `X_ij ≅ Z`. Let
  `eps_ij` transport `L_od` to `Sym(X_ij)`, extended by the identity.
  - Each `eps_ij(f b)` preserves every ray up to finitely many points.
  - Its germs are `b̄` on ray `i` and `(cbc)‾` on ray `j`, both in `B = Ĝ_od`, with indices summing to 0. So the
    germ tuple lies in `Q_n(B)`.
  - `H_n(G_od)` contains `FSym([n] x N)` and maps onto `Q_n(B)` by ray germs
    (`houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group` item 1, with
    `odometer-kernel-preimage-is-strongly-shift-similar` item 4).
  - So it is the set of all permutations that preserve each ray up to finitely many points and have germ tuple in
    `Q_n(B)`. Hence `eps_ij(L_od) <= H_n(G_od)`.
- **Generation for n >= 3.** Write `Δ_ij(b)` for the germ tuple of `eps_ij(b)`.
  - For distinct `i, j, k`, the commutator `[Δ_ij(b), Δ_ik(b')]` is `[b, b']` on ray `i` and `1` elsewhere. Since
    `[B,B] = K` (`odometer-kernel-preimage-is-strongly-shift-similar` item 3), `K^n` lies in `Γ = < Δ_ij(B) >`.
  - Modulo `K^n`, `Q_n(B)` is the zero-sum lattice in `Z^n` (via `chi`), and `Δ_ij(a)` maps to `e_i - e_j`.
  - So `Γ = Q_n(B)`. The subgroups `eps_ij(L_od)` contain `FSym(X_ij)`, which together generate
    `FSym([n] x N)`. Hence they generate `H_n(G_od)`.
- **n = 2.** `Q_2(B)` is generated by `Δ_12(B)` and `K x 1`: given `(b_1, b_2)`, put `x = c b_2 c`. Then
  `(b_1, b_2) = (b_1 x^-1, 1) · (x, cxc)`, and `chi(b_1 x^-1) = chi(b_1) + chi(b_2) = 0`. The preimage of `K x 1`
  is `G_od x 1` times finitary permutations. ∎
