---
rg: 2
id: leavitt-st20-cone-bound-half-rounding-proof
kind: route
title: Read hyperlinearity of the simple group Delta off the head alone, shadow asymptotic representations by genuine cover representations through a set section, and in the converse glue half-roundings across the finite edge and pass the relator bound to the head
target: leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding
requires:
  - binary-leavitt-elementary-group-is-simple
  - leavitt-steinberg-map-iso-from-rank-three
  - leavitt-cuntz-cone-halves-have-rf-amalgam-cover
  - flexible-rounding-glues-across-finite-edge-amalgams
  - nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
  - infinite-hyperlinear-kazhdan-group-is-not-hs-stable
  - ershov-jaikin-kassabov-steinberg-groups-have-property-t
---

Notation as in the target. `||X||_(2,d) = d^(-1/2) ||X||_HS` on `M_d(C)`, and `tr = Tr/d`. For
unitaries `u, v, w` we use, without further mention:

```text
||uv - 1||_2 <= ||u - 1||_2 + ||v - 1||_2,   ||w u w* - 1||_2 = ||u - 1||_2 = ||u^(-1) - 1||_2,
||u - 1||_2^2 = 2 - 2 Re tr(u).                                                       (U)
```

**Inputs.**
- `binary-leavitt-elementary-group-is-simple` and `leavitt-steinberg-map-iso-from-rank-three` give that
  `Delta = St_20(R) = EL_20(R) = GL_20(R)` is simple and nontrivial. It is non-abelian, since `x_12(1)`
  and `x_23(1)` do not commute.
- `leavitt-cuntz-cone-halves-have-rf-amalgam-cover`, items 1–3, gives the following:
  - the halves `Delta_+-`, with `Delta_0 = Delta_+ ∩ Delta_- = SL_20(F_2)^2`, which contains `z`;
  - the residually finite amalgam `Gamma`, the onto map `p`, and `K = <<k_1, ..., k_r>>`;
  - the automorphism `θ(g) = (g^*)^(-1)`, which exchanges `Delta_+` and `Delta_-`. It is a
    homomorphism because `*` is an anti-involution of `R`, so `(gh)^* = h^* g^*`.
- `z = x_13(q)` with `q = s_1 t_1`. Since `char R = 2`, `z^2 = x_13(2q) = 1`, so `P_z = (1-z)/2` is a
  projection, and it is nonzero because `z != 1`.

## (a) Hyperlinearity is read off the head

**Claim (a).** Let `g_0 in Delta \ {1}`. `Delta` is hyperlinear iff some asymptotic representation
`σ_n` of `Delta` has `||σ_n(g_0) - 1||_2` not tending to `0`.

*Proof.* (⇒) Suppose `Delta` is hyperlinear. Then it has an asymptotic representation with
`tr σ_n(g) -> 0` for every `g != 1`, and by (U), `||σ_n(g_0) - 1||_2 -> sqrt 2`.

(⇐) Suppose `||σ_n(g_0) - 1||_2 >= c > 0` on an infinite set `N_0`.
1. **Pass to an ultraproduct.** Choose a free ultrafilter `ω` containing `N_0`, and let
   `(M, τ) = Π_ω (M_(d_n), tr)`. Then `π(g) = [σ_n(g)]` is a group homomorphism
   `Delta -> U(M)`, by asymptotic multiplicativity, and `π(g_0) != 1`.
2. **Injectivity.** `ker π` is a normal subgroup other than `Delta`. Since `Delta` is simple,
   `π` is injective.
3. **No scalar values.** If `|τ(u)| = 1` for a unitary `u`, put `λ = τ(u)`. Then
   `||u - λ||_2^2 = 2 - 2 Re(conj(λ) τ(u)) = 0`, so `u = λ` by faithfulness of `τ`. The set
   `S = {g : π(g) is scalar}` is a normal subgroup, because scalars are central. The group
   `π(S) ≅ S` is abelian. Since `Delta` is simple and non-abelian, `S = {1}`. Hence
   `|τ(π(g))| < 1` for every `g != 1`.
4. **Tensor powers.** `||A^(⊗k) B^(⊗k) - C^(⊗k)||_2 <= k ||AB - C||_2` for unitaries, by
   telescoping and `||X ⊗ Y||_2 = ||X||_2 ||Y||_2`. So each `σ_n^(⊗k)` is an asymptotic
   representation, and `tr σ_n^(⊗k)(g) = (tr σ_n(g))^k`, whose `ω`-limit is `τ(π(g))^k`.
5. **Diagonalize.** Enumerate `Delta \ {1} = {g_1, g_2, ...}`. For each `m`:
   - choose `k_m` with `|τ(π(g_j))|^(k_m) < 1/(2m)` for `j <= m`;
   - then choose `n_m` in `ω`-large sets, and hence increasing, such that
     `|tr σ_(n_m)(g_j)|^(k_m) < 1/m` and the multiplicativity defects of `σ_(n_m)` on
     `{g_i, g_j, g_i g_j : i, j <= m}` are `< 1/(m k_m)`.

   Then `σ_(n_m)^(⊗ k_m)` is an asymptotic representation with `tr -> 0` off `1`, so `Delta` is
   hyperlinear. □

**Corollary (a').** If `Delta` is not hyperlinear, then every asymptotic representation of `Delta`
satisfies `||σ_n(g) - 1||_2 -> 0` for every `g in Delta`. For `g != 1` this is (a). For `g = 1`,
`||σ_n(1) - 1||_2 = ||σ_n(1)σ_n(1) - σ_n(1)||_2 -> 0`, and this holds for every asymptotic
representation.

## (b) Shadowing: cover representations with small relators give asymptotic representations

**Section.** `p` is injective on the subset `Delta_+ ∪ Delta_-` of `Gamma`. It is injective on each
half. If `p(a) = p(b)` with `a in Delta_+` and `b in Delta_-`, then `p(a) ∈ Delta_+ ∩ Delta_- = Delta_0`
inside `Delta` (definition (CC1) of the cover node), so `a = b in Delta_0`. Fix a set map
`s : Delta -> Gamma` such that:
- `p ∘ s = id`;
- `s` inverts `p` on `p(Delta_+ ∪ Delta_-)`, and in particular `s(1) = 1` and `s(z) = z`;
- `s` is arbitrary elsewhere.

For `g, h in Delta`, the element `c(g,h) = s(g)s(h)s(gh)^(-1)` lies in `K`. Write it as a product of
`L(g,h)` conjugates of the elements `k_i^(+-1)`. By (U), for every genuine unitary representation `ρ`
of `Gamma`,

```text
||ρ(s(g))ρ(s(h)) - ρ(s(gh))||_2 = ||ρ(c(g,h)) - 1||_2 <= L(g,h) · max_i ||ρ(k_i) - 1||_2.     (SH)
```

**Lemma (b).** If `ρ_n` are genuine representations of `Gamma` with `max_i ||ρ_n(k_i) - 1||_2 -> 0`,
then `σ_n = ρ_n ∘ s` is an asymptotic representation of `Delta`. It agrees with `ρ_n` on
`Delta_+ ∪ Delta_-`, and in particular `σ_n(z) = ρ_n(z)`. □

**Nonhyperlinear ⇒ (QC), and item 2.**
1. Suppose `(QC)` fails. Then there are `ε > 0` and genuine `ρ_n` with `max_i ||ρ_n(k_i) - 1||_2 -> 0`
   and `||ρ_n(z) - 1||_2 > ε`.
2. Lemma (b) turns them into an asymptotic representation with `||σ_n(z) - 1||_2 > ε`.
3. By (a) with `g_0 = z`, `Delta` is hyperlinear.

This is item 2's first sentence. For its second sentence, `(LNC3)` is a unital star homomorphism
`A(B_loop) -> P_z C[Delta] P_z`, where `B_loop` has no Connes-embeddable tracial state. By
`nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear`, with `q = P_z` a nonzero projection,
`(LNC3)` forces `Delta` to be non-hyperlinear. So failure of `(QC)` refutes `(LNC3)`.

**Nonhyperlinear ⇒ (HR).** By (a'), `σ_n(x) -> 1` for every `x`. Take `D_n = d_n` and `λ_n` the
trivial representation `1_(d_n)` of `Delta_+`. □

## (c) (QC) and (HR) imply non-hyperlinearity

Let `σ_n : Delta -> U(d_n)` be any asymptotic representation. By (a) with `g_0 = z`, it suffices to
show `||σ_n(z) - 1||_2 -> 0`.

1. **Both halves round.**
   - `(HR)` rounds `σ_n|Delta_+`.
   - `σ_n ∘ θ` is again an asymptotic representation of `Delta`. `(HR)` applied to it gives genuine
     `λ'_n` on `Delta_+` rounding `(σ_n ∘ θ)|Delta_+`.
   - Since `θ` maps `Delta_-` onto `Delta_+`, `λ'_n ∘ θ|Delta_-` is a genuine representation of
     `Delta_-` rounding `σ_n|Delta_-`.
   - The same argument shows the mirror statement, item 4.
2. **Glue.** `σ̃_n = σ_n ∘ p : Gamma -> U(d_n)` is an asymptotic representation of `Gamma`, since
   `p` is a homomorphism. It agrees with `σ_n` on `Delta_+-`.
   - `Gamma = Delta_+ *_(Delta_0) Delta_-` is residually finite and `Delta_0` is finite. So some finite
     quotient of `Gamma` is injective on `Delta_0`.
   - `flexible-rounding-glues-across-finite-edge-amalgams` gives genuine `ρ_n : Gamma -> U(M_n)` with
     `M_n/d_n -> 1` and `||σ_n(p(x)) - P ρ_n(x) P*||_(2,d_n) -> 0` for every `x in Gamma`.
3. **Relators become small upstairs.** Since `p(k_i) = 1` and `σ_n(1) -> 1` by (a'),
   `||P ρ_n(k_i) P* - 1_(d_n)||_(2,d_n) -> 0`. By Cauchy–Schwarz,
   `|Tr(X - 1_d)| <= d ||X - 1_d||_(2,d)`. Hence, with `E = P*P`,

   ```text
   Re Tr ρ_n(k_i) = Re Tr(P ρ_n(k_i) P*) + Re Tr((1-E) ρ_n(k_i) (1-E))
                  >= d_n - o(d_n) - (M_n - d_n)  =  M_n - o(M_n),
   ```

   using `|Tr((1-E) u (1-E))| <= M_n - d_n` for unitary `u`. By (U),
   `||ρ_n(k_i) - 1||_(2,M_n) -> 0` for each of the finitely many `i`.
4. **Apply (QC).** Given `ε`, eventually `max_i ||ρ_n(k_i) - 1||_(2,M_n) <= δ(ε)`, so
   `||ρ_n(z) - 1||_(2,M_n) <= ε`. Hence `||ρ_n(z) - 1||_(2,M_n) -> 0`.
5. **Descend.** `||P(ρ_n(z) - 1)P*||_HS <= ||ρ_n(z) - 1||_HS`, so

   ```text
   ||Pρ_n(z)P* - 1_(d_n)||_(2,d_n) <= (M_n/d_n)^(1/2) ||ρ_n(z) - 1||_(2,M_n) -> 0.
   ```

   Since `p(z) = z`, step 2 gives `||σ_n(z) - 1||_(2,d_n) -> 0`. □

Items (a)–(c) prove item 1 (split) and item 2.

## Item 3 (halves-exact form of (QC))

(⇒) Assume `(QC)`. Let `σ_n` be an asymptotic representation of `Delta` whose restrictions to
`Delta_+` and to `Delta_-` are homomorphisms.
1. The two restrictions agree on `Delta_0`. By the universal property of the amalgam, there is a
   genuine `ρ_n : Gamma -> U(d_n)` with `ρ_n = σ_n ∘ p` on `Delta_+ ∪ Delta_-`.
2. Write `k_i = a_1 ... a_m` with `a_j in Delta_+ ∪ Delta_-`. Then
   `ρ_n(k_i) = σ_n(p a_1) ... σ_n(p a_m)`, which is within `m - 1` multiplicativity defects of
   `σ_n(p(k_i)) = σ_n(1)`. By (a'), `σ_n(1) -> 1`.
3. So `max_i ||ρ_n(k_i) - 1||_2 -> 0`, and `(QC)` gives `σ_n(z) = ρ_n(z) -> 1`.

(⇐) Suppose `(QC)` fails, witnessed by `ρ_n`. Then Lemma (b) gives an asymptotic representation
`σ_n = ρ_n ∘ s`. Its restrictions to the halves are the genuine `ρ_n|Delta_+-`, and
`σ_n(z) = ρ_n(z)` stays at distance `> ε` from `1`. □

## Item 5 (stable halves)

Assume `Delta_+` is flexibly HS-stable, in the sense of Dogon's Definition 1.2 as quoted in
`flexible-rounding-glues-across-finite-edge-amalgams`: every asymptotic representation of `Delta_+`
is flexibly roundable.
- **(HR) holds.** For an asymptotic representation `σ_n` of `Delta`, the restriction `σ_n|Delta_+`
  is an asymptotic representation of `Delta_+`.
- **Gamma is flexibly HS-stable.** `θ|Delta_+ : Delta_+ -> Delta_-` is an isomorphism, so `Delta_-`
  is flexibly HS-stable too. The Corollary of the gluing claim, with the residually finite `Gamma`
  and the finite edge `Delta_0`, then makes `Gamma` flexibly HS-stable.
- **Split.** By item 1, `Delta` is non-hyperlinear iff `(QC)`. □

## Item 6 (strict rounding is unavailable)

- **Infinite.** `Delta_+` contains `x_12(s_1^k)` for all `k >= 1`. These elements are distinct
  because the `s_1^k` are distinct basis monomials of `R` lying in `R_+`, and `a -> x_12(a)` is
  injective.
- **Residually finite, hence hyperlinear.** By item 1 of the cover node, `Delta_+` is residually
  finite. Permutation representations on finite quotients separate points, so residually finite
  groups are sofic and therefore hyperlinear.
- **Kazhdan.** `Delta_+ = EL_20(R_+)` over the finitely generated ring `R_+`, which is generated by
  `s_1`, `s_2` and `q` (cover node), has property (T) by
  `ershov-jaikin-kassabov-steinberg-groups-have-property-t` (type `A_19`, rank `>= 2`, elementary
  group).
- **Conclusion.** `infinite-hyperlinear-kazhdan-group-is-not-hs-stable` applies: `Delta_+` is not
  locally strictly HS-stable. So any rounding in `(HR)` can be at best flexible and only relative
  to `Delta`. □

## Scope

Nothing here proves `(QC)` or `(HR)`. The theorem is a split: the two prerequisites are independent
statements. `(QC)` is about genuine representations of the residually finite group `Gamma` only, and
`(HR)` is about non-genuine approximations of one Kazhdan half. Their conjunction is exactly
non-hyperlinearity of `Delta`.
