---
rg: 2
id: ornstein-weiss-map-has-no-approximate-right-inverses
kind: claim
title: On a group containing a free subgroup of rank two, the Ornstein–Weiss endomorphism has no approximate right inverses, and no two Bernoulli shifts of different entropy both have them
distinct_from:
  bernoulli-isomorphism-from-approximate-right-inverses: that proves approximate right inverses in two shifts give an isomorphism; this proves by a spectral gap that on groups containing a free subgroup they fail from base entropy log 4 on and never hold for two different entropies.
  iid-generators-not-dense-at-positive-rokhlin-supremum: that obstructs density of generating i.i.d. partitions through Rokhlin entropy when the supremum is positive; this obstructs it through Kesten's spectral bound on free groups, at every supremum including zero.
  zero-supremum-endomorphisms-have-approximate-right-inverses: that is the open claim at zero supremum; this shows that claim forces groups with zero supremum to contain no free subgroup of rank two.
---

**ESTABLISHED (unreviewed)** by [[ornstein-weiss-map-has-no-approximate-right-inverses-proof]].

**Setting.** `G` is countably infinite and contains elements `a, b` that freely generate a subgroup `F ≅ F_2`.
Notation, ARI and DENSE are as in `bernoulli-isomorphism-from-approximate-right-inverses` and
`iid-density-iff-collapse-and-endomorphism-density`. `(R, ρ)` is any finite base, trivial allowed. `X` is the
Bernoulli shift with base `{0,1}² × R` and measure `(u_4 × ρ)^G`, with coordinates `(y, w, r)`.

1. **The Ornstein–Weiss endomorphism.** `δ(y)_g = (y_g + y_(ga), y_g + y_(gb))` mod 2 is an equivariant map from
   `({0,1}^G, u_2^G)` onto `(({0,1}²)^G, u_4^G)` that preserves measure. So `φ(y, w, r) = (δ(y), r)` is a
   non-invertible endomorphism of `X`.
2. **Spectral bound.** Let `f: X → {0,1}^G` be any `G`-equivariant Borel map. Then
   `µ{f(x)_1 + f(x)_a ≠ y_1} + µ{f(x)_1 + f(x)_b ≠ w_1} >= 1 − √3/2`. In particular
   `d(φ ∘ ζ, id) >= (2 − √3)/4` for every equivariant Borel `ζ: X → X`, measure-preserving or not.
3. **Failure from entropy `log 4`.** If `H(κ) >= log 4`, then `X_κ` does not have ARI, and `Aut_G(X_κ)` is not dense
   in `End_G(X_κ)`.
4. **Never two entropies.** If `H(κ) ≠ H(λ)`, then `X_κ` and `X_λ` do not both have ARI.
5. **Generating i.i.d. partitions.** Generating partitions are not dense in `Ind_λ(X_κ)` whenever `H(κ) ≠ H(λ)`,
   and whenever `H(λ) >= log 4`.

**Consequences for the zero-supremum program.**
- On every group with `h^Rok_sup(G) = 0` that contains `F_2`, three open claims fail:
  - `iid-generators-dense-at-zero-rokhlin-supremum`, by item 5;
  - `zero-supremum-bernoulli-automorphisms-dense-in-endomorphisms`, for bases of entropy `>= log 4`, by item 3;
  - `zero-supremum-endomorphisms-have-approximate-right-inverses`, by item 3.

  So each of the three implies that no group with zero Rokhlin supremum contains a free subgroup of rank two.
- The routes `zero-supremum-collapse-via-dense-iid-generators` and `zero-supremum-collapse-via-approximate-right-inverses`
  remain valid implications, but their inputs are false on such groups. Thompson's `V` contains `F_2`, so neither
  Baire-category route can produce a Bernoulli collapse over `V`.
- The obstruction uses no entropy. A would-be right inverse must invent one bit for each coset of `F`, constant along
  the tree of that coset. From it one builds an odd, almost invariant unit vector for `F` on `L²_0` of a Bernoulli
  shift, which Kesten's bound `||a + a^-1 + b + b^-1|| = 2√3` on `ℓ²(F_2)` forbids.

**Reading.**
- Fibres that run along one partial injection can be cut into finite segments. The free two-generator tree cannot
  be cut this way with small boundary, and item 2 turns that into a quantitative lower bound.
- Gaboriau–Lyons and Bowen give measurable free `F_2` subrelations inside the Bernoulli shifts of every nonamenable
  group. Running the argument along them with markers should extend items 2–5 to all nonamenable groups, possibly
  with larger entropy thresholds. That is not done here.
- What survives of the Baire approach: on groups without free subgroups, and for a single base entropy below
  `log 4`, nothing here decides DENSE or ARI.

**Model tests.**
- `Z` contains no free subgroup, and there ARI holds by the residual factor theorem (model test of
  `bernoulli-isomorphism-from-approximate-right-inverses`). This is consistent.
- For `G = F_2` items 3–5 already followed from Rokhlin entropy (item 5 of that node; Bowen's Proposition 9.4). The
  spectral proof recovers them without entropy.
- The hypothesis holds for `V`, for nonamenable finitely generated linear groups (Tits alternative) and for every
  group with a free subgroup. It fails for amenable groups and for Tarski monsters.

**Novelty (bounded).** Not found in Sections 1, 9 and 10 of arXiv:1804.05269 or in this graph. No wider search was
made.
