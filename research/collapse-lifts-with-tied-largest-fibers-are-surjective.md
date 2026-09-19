---
rg: 2
id: collapse-lifts-with-tied-largest-fibers-are-surjective
kind: claim
title: An injective lift of an injective automaton through any letter collapse is onto unless the largest fiber size, the number of largest fibers, or their product is already a nonsurjunctive size
distinct_from:
  collapse-lifts-with-unique-largest-fiber-are-surjective: that needs a unique largest fiber, so the background is one constant and charge noncreation on finite configurations finishes. This allows any number of largest fibers. The background is then a full shift of seas and the charge levels have infinite measure modulo translation; a flux identity and a cluster expansion are needed.
  smallest-fiber-collapse-lifts-are-surjective: that needs a bijective base and a unique smallest fiber, and works with the inverse base. This needs neither and works with the largest fibers as a sea.
  finite-injective-charge-noncreation-forces-surjectivity: that concerns configurations that are finite relative to one zero symbol, and proves them onto with a finite collision corner. This concerns configurations with finitely many particles over an arbitrary sea from a full shift, and proves them onto by measure: a Jacobian and a flux identity, with no operator algebra.
  certificate-controlled-routing-is-surjunctive: that is surjunctivity for routing rules controlled by a certificate full shift, by one mass transport. This is surjectivity of arbitrary injective lifts, by mass transport on each charge level together with an inclusion-exclusion over product models.
---

**ESTABLISHED** by `tie-collapse-sea-jacobian-proof`, from `bijective-ca-preserve-uniform-bernoulli-measure`
and `surjunctivity-passes-to-subgroups`. Notation `NS(G)` as in `ec-groups-share-the-nonsurjunctive-alphabet-sizes`.

**Setting.** `G` is any group and `r : B -> A` is a surjection of finite alphabets with fibers `Q_a = r^{-1}(a)`.
`τ` is an injective cellular automaton on `A^G`, and `Φ` is an injective cellular automaton on `B^G`, with
`r ∘ Φ = τ ∘ r`. Let `q >= 2` be the largest fiber size.
- `Z = {a : |Q_a| = q}`, which may have any number of letters, and `B_Z = r^{-1}(Z)`.
- The letters outside `Z` are particles, with charge `w(a) = log(q / |Q_a|) > 0`, and `w_min = min w`.
- `L` is the set of `x ∈ A^G` with finitely many particle sites, over an arbitrary `Z`-sea elsewhere.
- `W(x) = Σ_g w(x(g))`, and `L_c = {x ∈ L : W(x) = c}`.
- `F_x = Π_g Q_{x(g)}`.

**Theorem.** One of `q`, `|Z|`, `q|Z|` lies in `NS(G)`, or `Φ` and `τ` are both surjective.

**Structure proved on the way.** Assume none of the three sizes lies in `NS(G)`. Then, for a power `m >= 1`
that fixes all constants, the pair `(Φ^m, τ^m)` satisfies the following.
1. `τ^m(Z^G) = Z^G` and `Φ^m(B_Z^G) = B_Z^G`, both bijectively.
2. `W(τ^m x) <= W(x)` for every `x ∈ L`.
3. `Φ` is surjective if and only if `τ^m(L) = L` and `W ∘ τ^m = W` on `L`.
4. `τ^m(L_c) = L_c` for every level `c`. The levels `c < 2 w_min`, which are single-particle, follow already
   from compactness.
5. Whenever `W(τ^m x) = W(x)`, `Φ^m(F_x) = F_{τ^m x}`.

**Consequence for ascent by collapse.** Suppose an injective `Φ` on `|B|` letters lifts an injective `τ` on
`|A| < |B|` letters. Unless the profile is uniform (all fibers of size `q`, so `|B| = q|A|`), all three sizes
`q`, `|Z|`, `q|Z|` are below `|B|`.
- If `Φ` is not onto, the theorem puts one of these smaller sizes in `NS(G)` already. Whether the base `τ`
  fails to be onto is irrelevant: when `Φ` fails, one of the three sizes has already failed.
- For a single-letter doubling, profile `(2,1,…,1)`, the sizes are `2`, `1` and `2`. So a lift witnesses
  non-surjunctivity only over a group where `2 ∈ NS(G)`.
- For a uniform profile, `q|Z| = |B|` and the statement is tautological.

**Three lemmas, valid for any group.**
- *Sea Jacobian.* Let `σ` be an automaton on `Y^G`, injective on the configurations `L_Y` with finitely many
  sites outside `Z ⊂ Y`, with `σ(Z^G) = Z^G` bijective. Weight sea letters `1/|Z|` and particle letters
  `λ_a`. Then cylinder masses change by `|Z|^{k'-k} Πλ(σx)/Πλ(x)`, and with `λ ≡ 1/|Z|` the automaton `σ`
  preserves the measure.
- *Sea sectors are filled.* Every such `σ` with a positive charge that never increases maps `L_Y` onto
  `L_Y` and conserves the charge. Here "positive charge" means a weight `w > 0` on the letters outside `Z`,
  and "never increases" means `W ∘ σ <= W` on `L_Y`. Only injectivity on `L_Y` is used.
- *Flux identity.* At each level, the missing set has `M̄`-mass equal to the net flux out of the
  finite-measure set of connected configurations. By inclusion and exclusion over products of lower levels
  with independent seas, this flux equals a signed sum of zero model fluxes. The weights are the linear
  coefficients of chromatic polynomials.
