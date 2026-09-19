---
rg: 2
id: pro-unipotent-magnus-steps-put-one-relators-in-h-proof
kind: route
title: Solving the Magnus relator for its top letter degree by degree in the completed free Lie algebra of the window, where the leading coefficient is e_m, gives a shift automorphism with linear part the companion matrix of f, so the Magnus HNN maps to a residually-torsion-free-nilpotent-by-Z group injectively on its edge; torsion-freeness of normal abelian layers kills a in every Baumslag–Gersten map to 𝒮
target: pro-unipotent-magnus-steps-put-one-relators-in-h
requires:
  - edge-injective-quotients-give-hughes-free-division-rings
  - vertex-injective-quotients-give-hughes-free-division-rings
  - malcev-root-steps-put-commutator-root-one-relators-in-h
---

## Inputs

- **(C)** `𝓗` is closed under subgroups, extensions and directed unions, and contains every residually
  torsion-free nilpotent group. Item 1 of [[vertex-injective-quotients-give-hughes-free-division-rings]].
- **(E)** The edge-injective quotient lemma, item 1 of [[edge-injective-quotients-give-hughes-free-division-rings]]:
  a graph of groups with vertex groups in `𝓗` is in `𝓗` if it has a homomorphism to a group in `𝓗` that is
  injective on every edge group.
- **(M)** Magnus–Moldavanskii. If `t` has exponent sum `0` in `r` and the cyclically reduced rewrite
  `r' ∈ F(a_0, …, a_m)` involves `a_0` and `a_m`, then `G = <a, t | r>` is the HNN extension of
  `B = <a_0, …, a_m | r'>` with `t^{-1} a_i t = a_{i+1}` for `0 ≤ i < m`. The associated subgroups
  `<a_0, …, a_{m-1}>` and `<a_1, …, a_m>` are free on those letters (Freiheitssatz).
- **(P)** The completed free algebra. Let `R = Q<<X_0, …, X_{m-1}>>`, graded by degree, `R_{≥d}` the closed ideal
  of series of order at least `d`, and `L̂ ⊂ R_{≥1}` the closure of the free Lie algebra `L`.
  - `R` is a complete Hopf algebra with the `X_i` primitive. `L̂` is its set of primitive elements and
    `Û = exp(L̂)` its group of group-like elements. `exp` and `log` are inverse bijections `L̂ <-> Û`, and
    `log(e^x e^y) = BCH(x, y)` (Baker–Campbell–Hausdorff) lies in `L̂`.
  - `Û_{≥d} = exp(L̂ ∩ R_{≥d})` is a normal subgroup, `Û/Û_{≥d}` is the rational Mal'cev completion of the free
    nilpotent group of class `d − 1` and rank `m`, hence torsion-free nilpotent, and `∩_d Û_{≥d} = 1`.
    So `Û` is residually torsion-free nilpotent. The layers `Û_{≥d}/Û_{≥d+1} ≅ L_d` are `Q`-vector spaces.
  - Magnus: `e^{X_0}, …, e^{X_{m-1}}` freely generate a free subgroup of `Û`. Magnus' map `x_i ↦ 1 + X_i` embeds
    the free group in `R^×`, and composing with the continuous algebra automorphism `X_i ↦ e^{X_i} − 1` of `R`
    sends `x_i` to `e^{X_i}`.

## Proof of item 1

Assume `m ≥ 1` and `e_0 e_m ≠ 0`. Write `r'` as a cyclic word `∏_k a_{i_k}^{ε_k}`.

**Step 1: the top letter.** For `W ∈ L̂` put
`Λ(W) = log r'(e^{X_0}, …, e^{X_{m-1}}, e^W) ∈ L̂`.
By BCH, `Λ(W)` is `Σ_{i<m} e_i X_i + e_m W` plus a series of Lie brackets, each of which contains at least two
entries from `{X_0, …, X_{m-1}, W}`. So if `W ∈ L̂ ∩ R_{≥1}` and `V ∈ L̂ ∩ R_{≥d}`, then

    Λ(W + V) ≡ Λ(W) + e_m V   (mod R_{≥d+1}),

because every bracket containing `V` has degree at least `d + 1`. Define `Z_1 = −(1/e_m) Σ_{i<m} e_i X_i` and,
for `d ≥ 2`, `Z_d = −(1/e_m) Λ(Z_1 + … + Z_{d-1})_d`, the degree-`d` part. Each `Z_d` is homogeneous of degree
`d` and lies in `L_d`, since `Λ` takes values in `L̂`. By induction `Λ(Z_1 + … + Z_d) ∈ R_{≥d+1}`: for `d = 1`,
`Λ(Z_1) ≡ Σ e_i X_i + e_m Z_1 = 0` modulo `R_{≥2}`, and the congruence gives the step. So `Z = Σ_d Z_d ∈ L̂`
satisfies `Λ(Z) = 0`, that is

    r'(e^{X_0}, …, e^{X_{m-1}}, e^Z) = 1.

The same congruence shows `Z` is unique.

**Step 2: the shift.** The assignment `X_i ↦ X_{i+1}` (`i < m − 1`), `X_{m-1} ↦ Z` sends each generator to a
primitive element of `R_{≥1}`. So it extends to a unique continuous algebra endomorphism `T` of `R`. `T` is a
Hopf map, so it preserves `L̂` and `Û`, and on `Û` it is a group endomorphism with `T(e^x) = e^{T x}`.
- `T` preserves the filtration, and on `R_{≥1}/R_{≥2} = Q^m` it acts by the matrix `M` with `M x_i = x_{i+1}`
  (`i < m − 1`) and `M x_{m-1} = Z_1`. This is the companion matrix of `x^m + (e_{m-1}/e_m) x^{m-1} + … +
  e_0/e_m = f(x)/e_m`, so `det M = (−1)^m e_0/e_m ≠ 0`.
- On `L_d = gr_d L̂` the map `gr T` is the degree-`d` part of the free Lie functor applied to `M`, which is
  invertible because `M` is. A filtered endomorphism of a complete, separated filtered vector space whose
  associated graded map is bijective is bijective. So `T` is an automorphism of `L̂`, and of `Û`.

**Step 3: the map.** Let `Q = Û ⋊ <s>` with `s^{-1} u s = T(u)`. Define `φ(a) = e^{X_0}` and `φ(t) = s`. Then
`φ(a_i) = s^{-i} e^{X_0} s^i = e^{T^i X_0}`, which is `e^{X_i}` for `0 ≤ i ≤ m − 1` and `e^{T X_{m-1}} = e^Z`
for `i = m`. So `φ(r)`, a conjugate of `r'(φ(a_0), …, φ(a_m))`, is `1` by step 1, and `φ` is a homomorphism
`G -> Q`. On the edge group `A = <a_0, …, a_{m-1}>` of (M) it sends the free basis to `e^{X_0}, …, e^{X_{m-1}}`,
which is a free basis of its image by (P). So `φ|_A` is injective. The other associated subgroup is
`t^{-1} A t`, on which `φ` is injective too.

**Step 4: the target is in `𝓗`.** `φ(G) ∩ Û` is a subgroup of the residually torsion-free nilpotent group `Û`,
so it is in `𝓗` by (C). The quotient `φ(G)/(φ(G) ∩ Û)` embeds in `<s> ≅ Z`, which is in `𝓗`. By extension
closure, `φ(G) ∈ 𝓗`.

**Step 5: conclusion.** If `B ∈ 𝓗`, then (E) applied to the HNN extension of (M) and to `φ: G -> φ(G)` gives
`G ∈ 𝓗`. Conversely, `B ≤ G`, so `G ∈ 𝓗` gives `B ∈ 𝓗` by subgroup closure.

**The case `m = 1`.** `L̂ = Q X_0` is abelian, `Û ≅ (Q, +)`, `Z = −(e_0/e_1) X_0`, and `T` is multiplication by
`−e_0/e_1`. For `BS(2, 3) = <a, t | t^{-1} a^2 t a^{-3}>` this gives `r' = a_1^2 a_0^{-3}`, target
`Q ⋊_{3/2} Z`, and base the trefoil group `<a_0, a_1 | a_1^2 = a_0^3>`.

## Proof of item 2

`prounipotent_step_certify.py WORDFILE 6` checks the hypotheses of item 1 for every letter of exponent sum
`0`: span `m ≥ 1` and `e_0 e_m ≠ 0`. It also checks that `B` is free, witnessed by a letter `a_j` that occurs
once in the cyclic word `r'`. Then `r' = 1` solves for `a_j`, `B` is free on the other letters, and `B ∈ 𝓗`.
Item 1 then gives `G ∈ 𝓗`, and this uses no computation. The script also carries out steps 1 and 2 in
`Q<X>` truncated above degree 6 as a check on the arithmetic. It confirms that the relation holds to degree 6,
that `Z` is primitive (unshuffle coproduct test) and that `det M ≠ 0`. Output: `ruleS-L14-L15.txt`.
- For the 128 words of `w313-L15.txt`, `occ = (3, 1, 3)` and the free letter is `a_1`, with `e_1 = ±1`,
  `e_0, e_2 ∈ {±1, ±3}`. All 128 are certified.
- `frontier-L15.txt` is these 128 plus 8 words with `e = (0, −3, 0)`, for which (S1) fails.
- The 18 words of `frontier-L14.txt` fail (S1). Eight of them have a letter of exponent sum `0`, and give
  `e = (0, ±2, 0)`. The other ten have exponent sums `(±2, ±2)` or `(±4, ±2)`. After a Nielsen move
  (`a ↦ a b^{±1}`, or `b ↦ b a^{±1}` or `b ↦ b a^{±2}`) one letter has exponent sum `0`, and the rewrite again
  has `e = (0, ±2, 0)`.
- **Rule S applies in no basis to the 26.** `H_1(G; Q) = Q`, so the surjection `G -> Z` is unique up to sign,
  and its kernel `N` has a well-defined `Λ`-module `H_1(N; Q)`, with `Λ = Q[x^{±1}]`. For any presentation
  whose relator has a letter `t` of exponent sum `0`, Fox calculus gives `H_1(N; Q) ≅ Λ/(∂r/∂a)` (the image of `∂r/∂t`
  vanishes by the fundamental formula), and `∂r/∂a` maps to `f(x^{-1})` up to a unit. If `e_0 e_m ≠ 0` with `m ≥ 1`, then `f` has degree `m` and nonzero constant term,
  so `dim_Q H_1(N; Q) = m ≥ 1`. For the 26 words the computed rewrite has `f = ε x`, a unit, so `H_1(N; Q) = 0`.
  So no Nielsen basis satisfies (S1).

## Proof of item 3

Let `φ: G(1, k) -> P` with `P ∈ 𝒮`, and let `1 = P_0 ≤ P_1 ≤ … ≤ P_n = P` be a series of normal subgroups
of `P` with torsion-free abelian factors. Suppose `φ(a) ≠ 1`, and let `j ≥ 1` be least with `φ(a) ∈ P_j`.
- `P_j` is normal in `P`, so `c = φ(a^b) ∈ P_j`.
- In the abelian group `P_j/P_{j-1}` the relation `c^{-1} φ(a) c = φ(a)^k` reads `φ(a) = φ(a)^k`, so
  `φ(a)^{k-1} ∈ P_{j-1}`.
- `P_j/P_{j-1}` is torsion-free and `k ≠ 1`, so `φ(a) ∈ P_{j-1}`. This contradicts the choice of `j`.

So `φ(a) = 1`, and `a ≠ 1` in `G(1, k)` shows `G(1, k)` is not residually 𝒮. For `k = 2` this is also a case of
[[bg-shift-chains-die-in-residually-linear-alphabets]]. Membership of `G(1, k)` in `𝓗` is item 1 of
[[baumslag-gersten-group-is-hughes-free-embeddable]].

For the last bullet: `Q = Û ⋊ <s>` of item 1 has the normal subgroups `Û_{≥d}` (they are `T`-invariant, because
`T` preserves `R_{≥d}`). `Q/Û_{≥d}` has the normal series `Û_{≥e}/Û_{≥d}` (`1 ≤ e ≤ d`) followed by `Q/Û`,
with factors `L_e` and `Z`, all torsion-free abelian. So `Q/Û_{≥d} ∈ 𝒮`, and `Q` is residually 𝒮 because
`∩_d Û_{≥d} = 1`. The same holds for any `T` that preserves a filtration of this kind. By item 3 of
[[malcev-root-steps-put-commutator-root-one-relators-in-h]], every map from the 26 groups to such a `Q` kills
the interior letters, hence `a`, so no such target works for them.

## Proof of item 4

Suppose `φ: G -> Q` has `φ(t)^3` commuting with `φ(a)`. Then `φ(a_{i+3}) = φ(a_i)` for all `i`. The relations
`t^{-k} r' t^k = r'(a_k, a_{k+1}, a_{k+2}) = 1` then become the three relators of `N_3` with indices mod 3,
so `φ` restricted to `<a_0, a_1, a_2>` factors through `N_3`. `periodic_quotient.py 3 Phi3` writes the GAP
input. GAP (`TzGoGo`) eliminates `a_2`, and for each of the 8 `Φ_3` words it prints two nonempty freely
reduced relators in the surviving generators `f1 = a_0`, `f2 = a_1`, with abelian invariants `[0, 0]`. Those
relators are nontrivial elements of `F(a_0, a_1)` in the kernel of `F(a_0, a_1) -> N_3`, so `φ|_A` is not
injective. In item 1's target for these words `M` has characteristic polynomial `Φ_3 = x^2 + x + 1`, so
`M^3 = 1` and `T^3` is unipotent on `L̂`. It is not the identity, since otherwise `φ(t)^3` would centralise
`φ(a)`, which was just shown to be impossible.
