# Where (Q,+) sits in VA, and whether Aff(Q) or U_3(Q) can sit the same way (lane gq-q-in-germs, 2026-09-17)

Target context: `gl-n-q-embeds-in-fp-simple-group`. This artifact records the local (germ) anatomy of the
Belk–Hyde–Matucci group `VA` and of `(Q,+) ≤ VA`, the verdict for `Aff(Q)` and `U_3(Q)` in the same mechanism,
and a retargeted germ group `E` that escapes the no-distortion obstruction O4. Nodes:
- `va-singular-point-germ-groups-are-t-bar` (ESTABLISHED, lane proof);
- `rational-slope-germ-groups-have-bs-but-no-heisenberg` (ESTABLISHED, lane proof);
- `rational-slope-germ-group-contains-aff-plus-q` (OPEN).

## 0. Sources

- Belk–Hyde–Matucci, *Finite germ extensions*, arXiv:2407.03149v1 (3 Jul 2024), arXiv HTML. Verbatim:
  - **Finite germ extension.** "A group G≤Homeo(X) will be called a finite germ extension of B if it satisfies the
    following conditions: (1) Every element of G has only finitely many singular points. (2) G contains B, and indeed
    B is precisely the subgroup of G consisting of all elements that have no singular points. (3) For every g∈G and
    p∈sing(g), there exists an h∈G with sing(h)={p} such that h agrees with g on some neighborhood of p."
  - **VA** (elements f ∈ Homeo(ℭ₂)): "(1) The singular set sing(f) is finite, and each point of sing(f) ends in either
    0̄ or 1̄. (2) If p is a point in sing(f), then there exists a neighborhood of p on which f is order-preserving and
    L_{f(p)}∘f agrees with f∘L_p; here L_p denotes the prefix replacement α0ψ↦αψ if p=α0̄, or α1ψ↦αψ if p=α1̄."
  - Abstract: "a specific 2-generated, F∞ simple group V𝒜 of homeomorphisms of the Cantor set that contains every
    countable abelian group"; the body: "V𝒜 contains ⊕ω(ℚ⊕ℚ/ℤ)".
- Belk–Hyde–Matucci, arXiv:2005.02036v4: the definition of `T̄`, Theorem 1, Lemmas 6–7 and Proposition 13 ("Every
  subgroup of T̄ isomorphic to ℚ contains the center of T̄") are quoted verbatim in
  `research/artifacts/gq-gq-lit-q-embeddings.md` §1 (lane gq-lit-q-embeddings). They are not repeated here.
- Survey arXiv:2306.16356v3 §4.3: "T̄ is contained in a larger finitely presented group 𝒜 introduced by Brin, which
  has index two in the automorphism group of Thompson's group F", and 𝒜 acts naturally on the Cantor set. Brin's
  description of `Aut₊(F)` (dyadic PL homeomorphisms of `R` that agree with elements of `T̄` near `±∞`) is taken from
  the same lit artifact; it is not re-read here.
- Burillo–Felipe, arXiv:2605.09763v1, Theorem 1 and Corollary 5 (no distorted cyclic subgroups in `VA`), as recorded
  in obstruction O4 of the root.

## 1. The germ groups of VA (node `va-singular-point-germ-groups-are-t-bar`)

Take a point `p` ending in `0̄` or `1̄`, and the germs at `p` of elements of `VA` fixing `p`. They form a group
`G_p` with these properties.
- **Local form.** `G_p` is exactly the set of order-preserving, `L_p`-commuting germs that are locally in `V` off
  `p`. Condition (3) of a finite germ extension holds concretely: extend the germ by a prefix-replacement map on
  the complement.
- **The V-part.** The germs of elements of `V` in `G_p` are exactly the powers of the V-shift `L_p`, and `L_p` is
  central.
- **Isomorphism type.** `G_p ≅ T̄`, with `L_p ↦ z = (x ↦ x+1)`. So `G_p/⟨L_p⟩ ≅ T`. The dictionary: prefix
  replacements are the maps `x ↦ 2^n x + d`, `L_p ↦ ×2`, and the dyadic PL map `h(y) = 2^n(y−n+1)` on `[n,n+1]`
  conjugates `+1` to `×2`.
- **Stabilizers.** For every `f ∈ Stab_VA(p)` its germ lies in `G_p`. The singular germs of `VA` at fixed singular
  points are therefore elements of `T̄` that are not powers of the centre.

## 2. Where Q sits

| Level | Location of `(Q,+)` | Divisibility comes from |
|---|---|---|
| ambient `VA` | `Q ≤ T̄ ≤ 𝒜 ≤ VA` (survey §4.3), and `⊕_ω Q` by disjoint supports | copies of the local mechanism |
| element | `q ∈ Q ≤ T̄ ≤ 𝒜` with `q ∉ ⟨z⟩` has singular set exactly `{0̄, 1̄}`, the two ends (Brin's end-germ description) | — |
| germ at a singular point | the end-germ map `T̄ → G_{0̄} ≅ T̄` is injective: an element of `T̄` is determined by its germ at an end, by `z`-periodicity | — |
| `V`-part | `Q ∩ V = Q ∩ ⟨z⟩ ≅ Z`: an element of `T̄ ≤ 𝒜` lies in `V` exactly when its end-germs are `V`-germs, i.e. powers of the V-shift | the central V-shift |
| quotient | `Q/(Q ∩ ⟨z⟩) ≅ Q/Z ≤ T = G_p/⟨L_p⟩` (Prop. 13 plus §1) | torsion of all orders in `T`, lifted over the centre (BHM Lemmas 6–7: roots of roots of `z`) |

So `(Q,+)` sits in `VA` as a **central extension, by the V-shift `⟨L_p⟩ ≅ Z`, of a copy of `Q/Z` inside the germ
quotient `T`**, at each of the two singular points `0̄, 1̄`. The same holds for every copy of `Q` in a germ group
`G_p` (Prop. 13): divisibility in `VA`'s germs is always "torsion of `T` over the V-shift".

## 3. Germ-level lemmas (lane proofs, not independently reviewed)

For `T̄ ≤ VA` the lemmas below also follow from O4. They are recorded because they are germ-level and are reused
for the larger germ group `E` of §5, which is not inside `VA`.

**Lemma C (normalizer).** Let `D ≤ W` with `D ≅ (Q,+)` and `D ∩ Z(W) ≠ 1`. Then `N_W(D) = C_W(D)`.
*Proof.* `w ∈ N_W(D)` acts on `D` as multiplication by some `λ ∈ Q^x`, and it fixes a nonzero central element, so
`λ = 1`. ∎ With Prop. 13 and §1: no germ in `G_p ≅ T̄` normalizes a copy of `Q` nontrivially. This is the germ form
of item 2 of `aff-q-does-not-embed-in-aut-thompson-f`.

**Lemma D1 (no Baumslag–Solitar relation in T̄).** If `a, b ∈ T̄` and `a b a^-1 = b^m` with `m ≥ 2`, then `b = 1`.
*Proof.* Work in `T`, the PL₂ homeomorphisms of the circle, and put `c = b^(m−1)`.
- Then `a c a^-1 = c^m` and `rot(c) = (m−1)rot(b) ≡ 0`.
- If `c ≠ 1`, then `Fix(c) = Fix(c^m) ≠ ∅` (rotation number 0), and `supp(c)` has finitely many components.
  `a` permutes them, so `a^N` fixes each endpoint for some `N ≥ 1`.
- At the left endpoint `e` of a component, right derivatives give
  `c'(e+) = (a^N c a^-N)'(e+) = c'(e+)^(m^N)`, so `c'(e+) = 1`.
- So `c` is the identity just to the right of `e`, a contradiction. Hence `b` has finite order in `T`.
- Lifting, `b^k = z^j`. Then `z^j = a z^j a^-1 = b^(mk) = z^(jm)`, so `j = 0`.
- `T̄` is torsion-free (order-preserving maps of `R`), so `b = 1`. ∎

**Lemma D2 (nilpotent subgroups of T̄ are abelian).** Let `x, y ∈ T̄`, and let `c = [x,y]` commute with `x` and `y`.
*Proof.*
- **Image in T.** The image `H = ⟨x̄, ȳ⟩ ≤ T` is nilpotent, hence amenable. It preserves a probability measure on
  the circle, so `rot|_H` is a homomorphism and `rot(c̄) = 0`.
- If `c̄ ≠ 1`, then `x̄^N, ȳ^N` fix the endpoints of the finitely many components of `supp(c̄)`. Also
  `[x̄^N, ȳ^N] = c̄^(N²)`.
- The right-derivative homomorphism at such an endpoint `e` kills this commutator, so `c̄'(e+) = 1`, a
  contradiction. So `c̄ = 1`.
- **In T̄.** Then `c = z^j`. The translation number `τ` is conjugation-invariant and satisfies
  `τ(z^j y) = j + τ(y)`. So `τ(y) = τ(x y x^-1) = τ(z^j y) = τ(y) + j`, and `j = 0`. ∎

## 4. Verdict: can Aff(Q) or U_3(Q) sit in VA "the same way"?

**No, for both, and already at the germ level.**
- **Aff(Q).** Its translation subgroup would be a copy of `Q` in a germ group `G_p ≅ T̄`. By Prop. 13 that copy
  contains the central V-shift. By Lemma C the dilations of `Q^x` then cannot act. More generally, no copy of
  `Q ⋊_λ Z` with `λ ≠ 1` lies in `T̄`, and neither does `BS(1,2) ≤ Aff(Z[1/2])` (Lemma D1).
- **U_3(Q).** Its centre `Q` would have to be the lifted `Q/Z`-over-shift of a germ group, while the whole group
  sits in `T̄`. But `T̄` has no nonabelian nilpotent subgroup (Lemma D2), not even `U_3(Z)`. It also has no `Q²`
  (`aff-q-does-not-embed-in-aut-thompson-f`, item 1).
- **Globally.** O4 (Burillo–Felipe) excludes both groups from `VA` and from all its subgroups, since
  `BS(1,2) ≤ Aff(Q)` and `U_3(Z) ≤ U_3(Q)` have distorted cyclic subgroups.
- **Why the mechanism fails.** It makes the source of divisibility, the V-shift, central in the local germ group.
  A central element cannot be scaled (`Aff`) or be a commutator (`U_3`). Any host built "the same way" must break
  this centrality.

## 5. Retarget: germ groups with distortion (nodes `rational-slope-germ-groups-have-bs-but-no-heisenberg`, `rational-slope-germ-group-contains-aff-plus-q`)

**The group E.** The minimal way to make the shift non-central is to allow germs `φ` with `φ∘L^q = L^r∘φ`,
i.e. rational asymptotic slope `λ(φ) = r/q`. In the `R`-model at `+∞`, `E` is the group of germs of
`φ ∈ PL₂(R)` with `φ(y+q) = φ(y) + r` for large `y`.
- `λ: E ↠ Q_{>0}` is a homomorphism, with kernel `K = ⋃_q C(z^q) ≅ ⋃ T̄`.
- **Positive.** `BS(1,m) = ⟨δ_m, z⟩ ≤ E` for every `m ≥ 2`, so the shift `z` is exponentially distorted. `E`
  escapes O4.
- **Negative.** Every nilpotent subgroup of `E` is abelian.
  - If both slopes are 1, this is Lemma D2 inside one `C(z^q) ≅ T̄`.
  - Otherwise the commutator has translation number 0.
  - A component count of its periodic support against the slope `μ ≠ 1` gives a contradiction.
- **Consequence.** Rational-slope germs can carry the distortion of `BS(1,m)` and `Aff`, but never the quadratic
  distortion of a Heisenberg centre.
- **Where Heisenberg distortion must come from.** For `U_3(Q)`, and for `GL_n(Q)` with `n ≥ 3` (which contains
  `U_3(Z) ≤ SL_3(Z)`), it has to come from germs of another kind. Examples: two-dimensional germs as in Brin–Thompson
  `nV` (Kojima–Sheng arXiv:2603.18410v3 put `Q` in `nV`), germs whose asymptotic slope is not constant along the
  period, or non-germ (global) sources.

**Aff⁺(Q) in E (OPEN).** Necessary conditions for `Aff⁺(Q) = D ⋊ P ≤ E`:
1. `D ≤ K`.
2. `τ(d) ≠ 0` for every `d ≠ 1`, and `λ(a_μ) = μ` for every `μ` (the slopes are forced).
3. No dilation of slope `∉ 2^Z` commutes with an affine dilation `y ↦ 2^k y`.
First falsifiable step: decide whether `Aff⁺(Z[1/6]) = Z[1/6] ⋊ Z² ≤ E`.

**Design note for a global host (for gq-va-affq / gq-germ-design).** Take the group of homeomorphisms of `C` that
are locally in `V` except at finitely many points ending in `0̄`/`1̄`, and are order-preserving there with germs in
`E` (after the dictionary of §1). It is the natural finite germ extension of `V` with germ group `E`.
- **The germ group at a point is finitely generated.** Suppose the host satisfies BHM Theorem 2.1 with `n ≥ 1`.
  - Its germ group at `p`, for elements fixing `p`, is the image of `SingFix({p},{p})`. That uses condition (3),
    and `V`-germs come from `V ∩ Stab(p)`.
  - That subgroup has type `F_1` by hypothesis (2) of the theorem, with `M = M' = {p}`. So the germ group is a
    finitely generated `E_0 ≤ E`, and `λ(E_0) ≤ Q_{>0}` is finitely generated.
- **Obstruction.** By condition 2, if a copy of `Aff⁺(Q)` fixes `p` and acts faithfully through its germs at `p`,
  then `λ(E_0) ⊇ Q_{>0}`, which is impossible.
- **Conclusion.** In any such finitely presented `E`-type host, `Aff⁺(Q)` cannot live in the germs at one common
  fixed point. Its dilations must be spread over germs at infinitely many points, or at points not fixed by the
  whole group. This is the next test for any `E`-type design.
