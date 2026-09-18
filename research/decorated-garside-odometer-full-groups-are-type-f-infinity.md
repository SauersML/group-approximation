---
rg: 2
id: decorated-garside-odometer-full-groups-are-type-f-infinity
kind: claim
title: For every homogeneous Garside monoid, the topological full group of its binary-decorated Garside category extended by an odometer is of type F_infinity
distinct_from:
  odometer-2v-is-fp-simple-and-contains-bs12: that applies Li's Zappa--Szep theorem to the product 2-graph of two full shifts, which gives 2V extended by one odometer; this applies Li's degree-map form of the same theorem to a category graded by a Garside monoid (for instance a finite-type Artin monoid), which is not a higher-rank graph.
  artin-normal-form-boundary-full-groups-fix-a-point: that shows the full group of the Deligne normal-form boundary is never simple; this builds a different full group, on a decorated Garside boundary with no global fixed point, and proves only its finiteness.
artifacts:
  - research/artifacts/gq-bh-bh-free-15-2026-preprints.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed). The finiteness
input is X. Li, arXiv:2110.04505v2 (TeX in the gq scratchpad `src/kep/`):
- Theorem `thm:deg` (TeX l. 2055–2066);
- Lemma `lem:deg--t<d` (l. 2092–2099);
- Example `ex:ZS` (II) (l. 2371–2378).

## Construction

Let `P` be a Garside monoid with trivial units, Garside element `Δ`, and an
additive length `ℓ : P → N` with `ℓ(s) ≥ 1` for every simple element
`s ≠ 1`. Every finite-type Artin monoid qualifies, with `ℓ` the word length:
its relations are homogeneous.

1. **Decorated monoid.** Let `C_P = P ×_ℓ F_2^+` be the set of pairs `(p, w)`,
   where `w` is a binary word with `|w| = ℓ(p)`. Multiplication is
   `(p,w)(q,u) = (pq, wu)`.
2. **Category.** Let `C = C_P × F_2^+ × F_2^+`, a monoid with one object. Its
   degree map is `d(c, v, v') = (p, |v|, |v'|)` into `P' = P × N × N`, where
   `c = (p, w)`.
3. **Odometer.** Let `Z = ⟨a⟩` act on `C` by the binary odometer on the last
   factor: `a·(c, v, v') = (c, v, τ(v'))`.
   - Here `τ` adds 1 to `v'`, read least significant digit first.
   - The restriction is `a^{carry}`, where the carry is `1` exactly when `v'` is
     all ones and `0` otherwise.
   - This is the colour-1 odometer of `odometer-2v-is-fp-simple-and-contains-bs12`,
     with the first two factors playing the role of that node's free colour.
4. **Groups.** `D = C ⋈ Z` is the Zappa--Szép product.
   - `F_P = F(I_l(D) ⋉ ∂Ω_D)` is its topological full group on the boundary.
   - `F_P^0 = F(I_l(C) ⋉ ∂Ω_C)` is the version without the odometer.

## Statement

`F_P` and `F_P^0` are of type `F_∞`.

## Proof: hypotheses of Theorem `thm:deg` and Example `ex:ZS` (II)

1. **The degree monoid `P' = P × N × N`.**
   - It is cancellative, with `P'^* = {1}`.
   - It is right Noetherian, since `ℓ + |·| + |·|` is an additive length.
   - It is left reversible: `Δ^k` is a common left multiple in `P`, and `N` is
     commutative.
   - It admits lcms, since `P` does (it is a Garside monoid) and `N` does.
   - It is right cancellative, as Example `ex:ZS` requires.
   - Its finite Garside family is
     `S' = {(s, e, e') : s ∈ Div(Δ), e, e' ∈ {0,1}} ∖ {(1,0,0)}`. This is the
     divisor set of the Garside element `(Δ,1,1)` of the product Garside monoid,
     minus `1`.
   - `(S'^{≤L})^♯ = Div((Δ,1,1)^L)`, which is closed under left divisors. In a
     Garside monoid, products of at most `L` simples are exactly the left
     divisors of `Δ^L`.
2. **The degree map.** `d` is a functor with `d^{-1}(1) = {1} = C^*`. For the
   unique factorization property (UFP*): if `d(c) = p_1 p_2`, then `c` factors
   uniquely as `c_1 c_2` with `d(c_i) = p_i`, by cutting `w`, `v` and `v'` at
   lengths `ℓ(p_1)`, `|p_1|_N` and `|p_1|_N'`. The fibers are finite:
   `# d^{-1}(s,e,e') = 2^{ℓ(s)+e+e'}`.
3. **Condition (t<d).** It holds by Lemma `lem:deg--t<d`, because `P'` is left
   reversible and `# d^{-1}(s') ≥ 2` for every `s' ∈ S'`. When `s ≠ 1` this is
   `2^{ℓ(s)} ≥ 2`; otherwise `e + e' ≥ 1`.
4. **Condition (F) for `C`.** It holds because `C` is right cancellative, which
   Li notes after its definition (l. 1454–1456).
5. **The self-similar action.** The six axioms of l. 2185–2195 hold factorwise,
   exactly as for the binary odometer. The action is degree-preserving.
6. **Condition (F) for `D`.**
   - `D^*(v,v) = {(1, a^n)}` (`rem:ZS-Stab`).
   - In the degree setting the only relevant set is `U = ∂Ω(v)` (Li's
     corollary at l. 2082–2085).
   - `[a^n, U] = [a^m, U]` forces the odometer power `τ^{n-m}` to act trivially
     on `{0,1}^N`, so `n = m`.
7. **The unit groups are `F_∞`.**
   - For `F_P^0`, the group `C^*(v,v)` is trivial.
   - For `F_P`, the group `D^*(v,v) = St(Z, v) = Z`.
8. **Conclusion.**
   - Corollary `cor:deg` (l. 2108–2112) with `X = ∂Ω` gives `F_P^0` of type `F_n`
     for every `n`.
   - Example `ex:ZS` (II) gives the same for `F_P`. ∎

## Remarks (corrected 2026-09-18)

- **Unit space.** Li's boundary of a Garside monoid is a single point, because
  all principal right ideals meet. So `∂Ω_D = ∂Ω_C` is homeomorphic to
  `({0,1}^N)^3`: the decoration word and the two free factors. The first version
  of this remark wrongly described `∂Ω_{C_P}` as a Garside boundary with
  decorations. See `garside-decorated-groupoids-hide-artin-groups-in-isotropy`.
- **Not effective.** The groupoid is not effective. Its isotropy contains
  `ker(ℓ : G(P) → Z)` at every point. So `F_P` is an extension of a
  Brin--Thompson-type full group with an odometer, the image in `Homeo(∂Ω_D)`,
  by a group of isotropy sections.
- **What still stands.** The finiteness conclusion (type `F_∞`) is unaffected; it
  is Li's theorem applied to the checked hypotheses above.
- **What fails.** As a Boone--Higman host for `G(P)` this group is useless. See
  the refutation of `garside-odometer-groups-have-simple-finite-index-commutator`.
