---
rg: 2
id: alphabet-enlarging-covers-refute-dual-and-domain-duality-proof
kind: route
title: Precompose with a collapsing letter map, restrict to the subalphabet shift, and count constants; for linear maps sum the coordinates
target: alphabet-enlarging-covers-refute-dual-and-domain-duality
requires: []
---

**Conventions.** `(g.x)(h) = x(g^-1 h)`. An automaton is a continuous equivariant map. `x ~ y` means `x` and `y`
differ at finitely many sites, and `Δ(x, y)` is the set of those sites. Strong post-surjectivity with constant
`Φ` and lifts in `X` is as in `strict-pairs-give-dual-failures-on-bounded-defect-domains`. For a letter map
`s : C' → A`, `s^G` applies `s` at every site; it is an automaton. Fix `P : A^G → B^G` strongly post-surjective
with constant `Φ`, where `A ⊊ B`.

**Lemma L (letter lifts).** Let `s : C' → A` be onto. For `x ∈ C'^G` and `w ~ s^G(x)` there is `x' ~ x` with
`s^G(x') = w` and `Δ(x, x') = Δ(s^G(x), w)`.
- *Proof.* Put `x'(g) = x(g)` where `w(g) = s(x(g))`, and otherwise let `x'(g)` be any `s`-preimage of `w(g)`. ∎

**Lemma C (composition).** `P ∘ s^G : C'^G → B^G` is strongly post-surjective with the same `Φ`, and its lifts lie
in `C'^G`.
- *Proof.* Let `x ∈ C'^G` and `z ~ P(s^G(x))`. Strong post-surjectivity of `P` at `s^G(x)` gives `w ~ s^G(x)`
  with `P(w) = z` and `Δ(s^G(x), w) ⊆ Δ(P(s^G(x)), z)Φ`. Lemma L gives `x'` with `s^G(x') = w` and
  `Δ(x, x') = Δ(s^G(x), w)`. So `P(s^G(x')) = z` and `Δ(x, x') ⊆ Δ(P(s^G(x)), z)Φ`, which is finite. ∎
- Dropping `Φ` throughout, the same argument shows that plain post-surjectivity of `P` passes to `P ∘ s^G`.

**Lemma N (collapse).** If `s` is not injective, then `P ∘ s^G` is not pre-injective.
- *Proof.* Take `c ≠ c'` with `s(c) = s(c')`. Let `x = c^G`, and let `x'` equal `x` except `x'(1) = c'`. Then
  `x ~ x'`, `x ≠ x'`, and `s^G(x) = s^G(x')`, so the two images agree. ∎

**Lemma P (products).** `P × P : (A × A)^G → (B × B)^G` is strongly post-surjective with constant `Φ`.
- *Proof.* Let `z = (z_1, z_2) ~ (P(x_1), P(x_2))`. Then `Δ(P(x_i), z_i) ⊆ Δ((P × P)(x), z)`. Lift each
  coordinate separately and take the union of the two difference sets. ∎

**Part 1.** `|B| > |A|`, so an onto `q : B → A` is not injective. By Lemmas C and N, `F = P ∘ q^G` is a strongly
post-surjective, hence post-surjective, automaton `B^G → B^G` that is not pre-injective. If `P` is only
post-surjective, the plain form of Lemma C gives the same conclusion. This is a counterexample to
`every-group-is-dual-surjunctive` at `G`.

**Part 2.** `X = A^G` is the SFT in `B^G` whose forbidden patterns are the one-site patterns with a letter of
`B \ A`. It is proper since `A ≠ B`, and it contains every `a^G` with `a ∈ A`. The map `P : X → B^G` is an
automaton, and it is strongly post-surjective with lifts in `A^G = X`, by hypothesis. With `B` in the role of
the alphabet, this is a counterexample to `constant-point-sft-domains-admit-no-post-surjective-covers` at `G`.

**Part 3.**
1. **Sizes.** `|B| ≥ |A| + 1` gives `|B|^2 ≥ |A|^2 + 2|A| + 1 > |A|^2 + 1`. So there is `C' ⊊ C = B × B` with
   `|C'| = |A|^2 + 1`, and an onto letter map `s : C' → A × A`, which is not injective.
2. **The map.** By Lemmas P, C and N, `F' = (P × P) ∘ s^G : C'^G → C^G` is strongly post-surjective with lifts in
   `C'^G`, and not pre-injective.
3. **The domain.** `C'^G ⊊ C^G` is an SFT with one-site forbidden patterns. It is strongly irreducible with
   gap `{1}`, since patterns on disjoint sets glue.
4. This is a counterexample to `proper-sft-domains-admit-no-dual-failures` at `G`.

**Part 4.**
1. **Constants.** The configurations fixed by all of `G` are exactly the constants: `g.x = x` for all `g`
   means `x(g^-1 h) = x(h)`, and this is step 1 of `full-shifts-with-different-alphabets-are-not-conjugate-proof`.
2. **Deficiency.** `P` is equivariant, so it maps the `|A|` constants of `A^G` to constants. At most `|A| < |B|`
   constants of `B^G` are hit. Pick a constant `b^G` that is not hit. So `D(A^G, P) ∋ b`.
3. **No right inverse.** Suppose `R : B^G → A^G` is equivariant with `P ∘ R = id`. Then `R(b^G)` is `G`-fixed,
   so it is a constant `a^G`, and `P(a^G) = b^G`. This contradicts step 2. Continuity is not used.
4. **The derived maps.** `q^G` and `s^G` map constants to constants.
   - So `F` hits only constants in `P(constants of A^G)`, at most `|A| < |B|` of them.
   - `F'` hits at most `|A|^2 < |B|^2` constants of `C^G`.
   - Step 3 applies verbatim to both. Neither has an equivariant right inverse, so neither has a section or an
     automaton right inverse. ∎

**Part 5 (linear).** Let `A = F^m`, `B = F^n`, and let `P` be `F`-linear. Only post-surjectivity at `0` is used.
1. **Memory.** By continuity at every point of the compact space `A^G`, `P(x)(1)` depends only on `x|_S` for
   some finite `S`. By equivariance `P(x)(g) = P(g^-1.x)(1)`, so `P(x)(g)` depends only on `x|_{gS}`.
   `P(0) = 0`, so `P` maps the space `V` of finitely supported points of `A^G` into the space `W` of finitely
   supported points of `B^G`.
2. **Onto on finite supports.** For `z ∈ W` we have `z ~ 0 = P(0)`, so post-surjectivity gives `x' ~ 0`, that is
   `x' ∈ V`, with `P(x') = z`. So `P|_V : V → W` is onto.
3. **Sums.** Let `ε_V(x) = Σ_g x(g) ∈ F^m` and `ε_W(w) = Σ_g w(g) ∈ F^n`. Both are linear, onto, and
   shift-invariant. Put `L(v) = ε_W(P(v δ_1))`, where `v δ_1` is `v` at `1` and `0` elsewhere. `L : F^m → F^n` is
   linear.
4. **Factorisation.** Every `x ∈ V` is the finite sum `Σ_g g.(x(g) δ_1)`. So
   `ε_W(P(x)) = Σ_g ε_W(g.P(x(g) δ_1)) = Σ_g L(x(g)) = L(ε_V(x))`.
5. **Rank.** `ε_W ∘ P|_V` is onto by steps 2 and 3, so `L` is onto, and `n ≤ m`. ∎

This is the augmentation argument: `P|_V` is an onto map of free `F[G]`-modules `F[G]^m → F[G]^n`, and the
trivial module turns it into an onto map `F^m → F^n`.
