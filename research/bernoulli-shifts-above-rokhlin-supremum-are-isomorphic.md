---
rg: 2
id: bernoulli-shifts-above-rokhlin-supremum-are-isomorphic
kind: claim
title: Over a group with finite Rokhlin supremum, Bernoulli shifts whose base entropies exceed the supremum are all isomorphic
distinct_from:
  rokhlin-entropy-is-the-bernoulli-approximation-threshold: that proves the weak* approximation of Bernoulli measures by isomorphic shift models above the supremum; this asks that the approximations close, giving actual isomorphisms.
  bernoulli-entropy-counterexample-constraints: that proves a collapsing pair must lie at or above the supremum; this is the converse, that every pair above it collapses.
  bernoulli-shifts-with-equal-base-entropy-are-isomorphic: that is Seward's theorem that base entropy is sufficient; this asks that Rokhlin entropy, min(base entropy, supremum), be sufficient.
  zero-rokhlin-supremum-forces-bernoulli-collapse: that asks for one collapse when the supremum is zero; this asks for total collapse above any finite supremum, and implies it (route collapse-above-supremum-gives-zero-supremum-collapse).
---

**OPEN.** Let `G` be a countably infinite group with `s = h^Rok_sup(G) < ∞`. For all standard
probability spaces with `s < H(L, lambda) < H(K, kappa) < ∞`, the Bernoulli shifts `L^G` and `K^G` are
isomorphic.

**What it says.**
- By Seward's Theorem 1.10 (`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`),
  `h^Rok_G(L^G) = min(H(L), s)`. So the claim is: Rokhlin entropy is a complete isomorphism invariant of
  Bernoulli shifts over every group.
- It is the exact form of `rokhlin-entropy-is-the-bernoulli-approximation-threshold`, whose approximations
  above `s` go both ways.
- Model tests.
  - Sofic groups have `s = ∞`, so the claim is vacuous there, as it must be.
  - A trivial world with `s = 0` would make all nontrivial finite-entropy Bernoulli shifts isomorphic,
    matching the total collapse of `bernoulli-isomorphism-collapse-set-is-a-subgroup`, item 5.
  - No group with `s < ∞` is known, so nothing tests it against a known example.

**Reformulation.** `L^G ≅ K^G` iff `K^G` has a generating partition `alpha` with distribution `lambda` whose
`G`-translates are independent. Pull back the coordinate partition; conversely, `x ↦ (g ↦ alpha(g^-1 x))`
pushes the measure to `lambda^G` by independence and is injective by generation. Above `s`, Seward's Krieger
theorem gives generating partitions with distribution exactly `lambda`, because
`h^Rok_G(K^G) = s < H(lambda)`. This is Part I, Theorem 1.1, as quoted in
`research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md` (S3). So the claim asks only that one
of them can be taken with independent translates.

## Attempts

- **Algebra.** Dead as a mechanism. Algebraic identities among free and finite-subgroup-induced modules conserve
  the lifted trace, which equals the entropy the co-induced Ornstein theorem adds
  (`finite-subgroup-induced-absorption-conserves-entropy`).
- **Relative Ornstein recoding.** Dead as a mechanism. Seward-type isomorphisms fix a common factor and recode
  i.i.d. rows along an aperiodic `T`. Ornstein's theorem for `Z` then forces equal row entropy (Attempts on
  `bernoulli-shift-entropy-classifies-for-every-group`). A collapse must recode many rows jointly, or move the
  common factor.
- **Factor maps.** Over groups containing `F_2`, `K^G` factors onto `L^G` (Bowen, arXiv:0812.2718), and over
  every nonamenable group (`nonamenable-bernoulli-shifts-are-weakly-isomorphic`), with no control of
  injectivity. Seward's small generating partitions (Theorem 6.7 mechanism) record information on a
  transversal of a finite subgroup. They are generating but carry no independence.
- **What a proof needs.** An Ornstein-type upgrade in which the entropy hypothesis is replaced by "above `s`".
  Perturb a Krieger generating partition with distribution `lambda` towards independence of translates while
  keeping it generating, and converge in `L^1`. The finitely determined property of Bernoulli shifts is known
  only through amenable or sofic counting.
- **Genericity (lane ex-bernoulli-rokhlin-complete, 2026-09-13).** Dead when `0 < s < ∞`.
  - On a nonamenable group with positive supremum, generating partitions of `K^G` keep a definite distance from
    i.i.d. partitions carried by a Bernoulli factor of base entropy `a < s`.
  - Factor maps from `L^G` onto `K^G` keep a definite distance from the joinings such partitions define.
  - Both follow from sub-additivity and Bowen's weak isomorphism
    (`iid-generators-not-dense-at-positive-rokhlin-supremum`).

  So generating i.i.d. partitions are not dense among i.i.d. partitions, and isomorphism joinings are not dense
  among joinings. A Baire category argument over either space cannot give this claim when `0 < s < ∞`. At
  `s = 0` the obstruction is empty. That case is posed as `iid-generators-dense-at-zero-rokhlin-supremum`,
  whose Baire route gives total finite collapse (`zero-supremum-collapse-via-dense-iid-generators`).
- **Seward's factor theorem (arXiv:1804.05269v3).** It cannot output the partition this claim asks for.
  - A generating i.i.d. partition `alpha` of `K^G` above `s` is outer-deficient. The outer Rokhlin entropy of
    `σ-alg_G(alpha) = B(K^G)` is `h^Rok_G(K^G) = s`, below `H(alpha)`.
  - The perturbative factor theorem (Theorem 9.2) makes a partition exactly Bernoulli only near partitions
    whose outer entropy is close to their Shannon entropy. So it never returns such an `alpha`.
  - What it does give, for `s > 0`, is Theorem 10.1 with trivial `Σ`. For every `ε > 0` and every finite
    probability vector `p̄` with `H(p̄) = s`, `K^G` has a partition with distribution `p̄` and independent
    translates, relative to which `K^G` has Rokhlin entropy below `ε`. So every Bernoulli shift above `s` is an
    `ε`-extension of the Bernoulli shift with base entropy exactly `s`, and this claim asks that the extension
    be absorbed exactly.
- **Exactification loop (lane ex-bernoulli-rokhlin-complete, 2026-09-13).** The known tools for exact
  independence reduce a collapse to a collapse.
  - Seward's factor theorem builds its partitions along an expressible transformation, over the external past
    of a nontrivial free factor `F`. It returns partitions `G`-Bernoulli over `F`, hence independent of `F`. A
    generating output would present `K^G` as `F × M^G`, and absorbing `F` is again a collapse.
  - The null Bernoulli factors of Seward's Corollary 10.2 (independent translates, base entropy at most
    `s + ε`, relative Rokhlin entropy `0`) never have an independent Bernoulli complement when `s > 0`.
    - Suppose `K^G = F ∨ σ-alg_G(ζ)`, with `F` Bernoulli of base entropy `a` and `ζ` `G`-Bernoulli over `F`
      with `H(ζ) = b > 0`.
    - Then `(K^G, F)` is isomorphic to a product of two Bernoulli shifts with finite bases of entropies `a`
      and `b`, with `F` the first coordinate.
    - Proposition 6.5 of arXiv:1501.03367 gives relative Rokhlin entropy `min(b, s) > 0`, so `F` is not null.
  - Predictable recodings along an invariant random order stay independent of the process they read
    (Attempts on `iid-generators-dense-at-zero-rokhlin-supremum`).
