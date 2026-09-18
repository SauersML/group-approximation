# Fixed-point surjectivity of cover-pair sections, and a free-monoid calibration

swarm-0917-w9-w9-gs-follow, 2026-09-18. Supports `cover-pair-sections-force-fixed-point-surjectivity`.
Conventions are those of `research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md`:
`(g.x)(h) = x(g^-1 h)`. A **cover pair** `(X, F)` over `A^G` is an SFT `X ⊊ A^G` with an automaton
`F : X → A^G` that is strongly post-surjective with lifts in `X`. A **section** is a continuous equivariant
`s : A^G → X` with `F ∘ s = id`. A **seed** is a continuous equivariant `ξ : A^G → X`.

For a subgroup `H ≤ G` write `Fix_A(H) = {z ∈ A^G : h.z = z for all h ∈ H}`. `C_X = X ∩ Fix_A(G)` is the set of
constants of `X`, identified with a subset of `A`. The **constant map** is `φ : C_X → A`, `b ↦ f(b,...,b)`, where
`f` is the local rule of `F`, so `F(b^G) = φ(b)^G`.

**Deficiencies.** `D_H(X, F) = Fix_A(H) \ F(X ∩ Fix_A(H))` and `D(X, F) = A \ φ(C_X)`, so that
`D_G = {a^G : a ∈ D}`.

## 1. Theorem F1: sections are fixed-point surjective

**Theorem.** Let `(X, F)` be a cover pair (in fact any continuous equivariant `F : X → A^G` will do).
1. If `(X, F)` has a section `s`, then `F(X ∩ Fix_A(H)) = Fix_A(H)` for every subgroup `H ≤ G`. That is, `D_H = ∅`
   for every `H`.
2. In particular a section forces `φ` to be onto. Because `|C_X| ≤ |A|`, this means that `X` contains all `|A|`
   constants and that `φ` is a permutation of `A`.
3. Take a seed `ξ` with `F(ξ(z))(1) = z(1)` for all `z ∈ Sym_E`, where `E ≠ {1}`. Then `F(ξ(a^G)) = a^G` for every
   `a ∈ A`, and so `D = ∅`.

**Proof.**
1. **Inclusion ⊆.** `F` is equivariant, so it maps `X ∩ Fix_A(H)` into `Fix_A(H)`.
2. **Inclusion ⊇.** Let `z ∈ Fix_A(H)`. For `h ∈ H`, `h.s(z) = s(h.z) = s(z)`, so `s(z) ∈ X ∩ Fix_A(H)`, and
   `F(s(z)) = z`.
3. **Part 2.** Take `H = G`. Then `φ(C_X) = A` forces `|C_X| ≥ |A|`, so `C_X = A` and `φ` is a bijection.
4. **Part 3.** Fix `a ∈ A`. The constant `a^G` is fixed by every `e`, so it lies in `Sym_E` because `E \ {1} ≠ ∅`.
   By equivariance `ξ(a^G)` is `G`-fixed.
5. For every `g`, `F(ξ(a^G))(g) = (g^-1.F(ξ(a^G)))(1) = F(ξ(g^-1.a^G))(1) = F(ξ(a^G))(1) = a`.
6. So `F(ξ(a^G)) = a^G`. ∎

`E` can always be enlarged by enlarging `Φ`, which keeps both Lemma 2 and Theorem S valid, so assuming `E ≠ {1}`
costs nothing once `G ≠ 1`.

## 2. Heredity: deficiency pulls back along morphisms of pairs

A **morphism** `(X', F') → (X, F)` of pairs, over alphabets `A'` and `A`, is a pair `(ρ, π)` with the following
properties:
- `ρ : X' → X` is continuous and equivariant;
- `π : A'^G → A^G` is continuous and equivariant;
- `π ∘ F' = F ∘ ρ`;
- `π(Fix_{A'}(H)) ⊇ Fix_A(H)`. This holds, for example, when `π` is a coordinate projection `(A × B)^G → A^G` or
  a conjugacy.

**Proposition F2.** If `(ρ, π)` is such a morphism, then `D_H(X, F) ≠ ∅` implies `D_H(X', F') ≠ ∅`. So
`(X', F')` has no section either.

**Proof.**
1. Pick `z ∈ D_H(X, F)`, and `z' ∈ Fix_{A'}(H)` with `π(z') = z`.
2. Suppose `z' = F'(x')` with `x' ∈ X' ∩ Fix_{A'}(H)`.
3. Then `ρ(x') ∈ X ∩ Fix_A(H)` and `F(ρ(x')) = π(F'(x')) = z`. This contradicts `z ∈ D_H(X, F)`. ∎

**Instances.** Each of the following constructions from a pair `(X, F)` admits a morphism back to `(X, F)`, so
none of them can remove a deficiency.
- **Product with any cover pair.** Take `(X × Y, F × K)`, with `π` the first projection.
- **Shear.** Over `A = Z/k`, take `(X × A^G, (x, y) ↦ (F(x) + ψ(y), y))`, with `ψ` any automaton on `A^G`. Use
  `ρ(x, y) = x` and `π(u, v) = u - ψ(v)`, which is onto constants.
- **Restriction to a sub-SFT `X' ⊆ X`** on which `F` is still a cover pair. Use `ρ` the inclusion and `π = id`.
- **Composite.** Take `(X ∩ F^-1(X), F ∘ F)`, which is again a cover pair: lift twice, inside `X`. Use
  `ρ = F|` and `π = id`.
- **Conjugacy of the domain and automorphism of the target.** `φ` changes by bijections.

**Corollary F3 (route bookkeeping).** Every pair that `gottschalk-via-constant-point-domains` feeds into CP has
`D_H = ∅` for all `H`.
- These are the pairs `(X_R, σ|_{X_R})` of `strict-pairs-give-dual-failures-on-bounded-defect-domains`.
- Part 3 of that theorem gives the automaton section `τ`, so F1 applies.
- By Proposition C of the scheduled-sections artifact, the fragment of CP the route consumes is "no cover pair has a
  section", which is exactly Gottschalk.
- Deficient constant-point pairs, with `D ≠ ∅`, are never produced by the route. Excluding them is the part of CP
  that goes beyond Gottschalk.

## 3. Calibration: a surjunctive cancellative monoid with a deficient constant-point cover pair

Let `M = {a, b}*` be the free monoid, with identity `ε`. Configurations are `x : M → A`, and `M` acts by
`(m ⋆ x)(w) = x(mw)`. An automaton with finite memory `S ⊆ M` has the form `τ(x)(w) = μ((x(ws))_{s ∈ S})`, and it
commutes with `⋆`. This is the monoid form of `τ(x)(g) = μ((x(gs))_s)`. SFTs, `~` (finite difference) and strong
post-surjectivity with lifts in `X` read verbatim, with `Δ(x, x') ⊆ Δ(F(x), z)Φ` and `Φ ⊆ M` finite.

**Proposition M1 (M is surjunctive).** Every injective automaton `τ : A^M → A^M` is surjective.

**Proof.**
1. **Periodic points.** Let `r = max |s|` over `s ∈ S`. For `n ≥ r`, let `Per_n` be the set of `x` that are
   constant on `{w : |w| > n}`. These are the configurations that factor through the Rees quotient `M/I_n`, where
   `I_n = {w : |w| > n}` collapses to an absorbing zero. `Per_n` is finite.
2. **Invariance.** If `x ∈ Per_n` has tail value `c`, then for `|w| > n` every `ws` also has length `> n`, so
   `τ(x)(w) = μ(c, ..., c)`. Hence `τ(Per_n) ⊆ Per_n`.
3. **Surjectivity on `Per_n`.** An injective `τ` is bijective on the finite set `Per_n`, so `τ(A^M) ⊇ ∪_n Per_n`.
4. **Density.** `∪_n Per_n` is dense, because every finite pattern extends by a constant tail.
5. **Conclusion.** `τ(A^M)` is compact, hence closed, so it is all of `A^M`. ∎

This is consistent with Ceccherini-Silberstein and Coornaert, "On surjunctive monoids", IJAC 25 (2015). That source
has not been checked verbatim, and the proof above does not rely on it.

**Proposition M2 (a deficient constant-point cover pair on M).** Let `A = {0, 1}`. Let
`X = {x : x(wb) = 0 for all w ∈ M}`, an SFT with window `{b}`. Let `F(x)(w) = x(wa)`, with memory `{a}`. Then:
1. `X ⊊ A^M` is a proper SFT, since `1^M ∉ X`.
2. `X` is strongly irreducible. The constraint is single-site, so admissible patterns on disjoint finite sets glue.
3. `0^M` is the only constant in `X`.
4. `F` is strongly post-surjective with lifts in `X`, with `Φ = {a}`.
5. `F` is onto, and it is not pre-injective.
6. `φ(0) = 0`, so `D(X, F) = {1}`.

**Proof.**
1. **Parts 1–3.** Immediate.
2. **The lift.** Let `x ∈ X` and `z ~ F(x)`. Every `w ≠ ε` is uniquely `ua` or `ub`. Put `x'(ε) = x(ε)`,
   `x'(ua) = z(u)` and `x'(ub) = 0`.
3. **It works.** `x' ∈ X` and `F(x') = z`.
4. **It is local.** `x'` differs from `x` at `ua` only if `z(u) ≠ F(x)(u)`, so `Δ(x, x') ⊆ Δ(F(x), z)a`. The
   same formula with an arbitrary `z` gives surjectivity.
5. **Not pre-injective.** `F` never reads `x(ε)`, so flipping it gives two distinct asymptotic points with the
   same image. ∎

**Machine check.** `experiments/free-monoid-cover-pair-2026-09-17/check.py` verifies the lift and its locality
exhaustively on balls of radius 1, 2 and 3 (8, 128 and 32768 cases). It also verifies the constant set on
radius 4. For 200 random automata with memory `{ε, a, b}`, it checks that injectivity on `Per_2` is bijectivity.
The run printed `OK`.

**No section.** Theorem F1(1)–(2) uses only equivariance, so it holds verbatim over `M`. Hence `(X, F)` has no
continuous equivariant section: `s(1^M)` would be a constant of `X` mapped to `1^M`. The naive section
`s(z)(ua) = z(u)`, `s(z)(ub) = 0`, `s(z)(ε) = 0` is continuous but not equivariant. For `m = m'a` we have
`s(m ⋆ z)(ε) = 0`, while `(m ⋆ s(z))(ε) = s(z)(m) = z(m')`.

## 4. What the calibration kills

`M` is surjunctive, cancellative, finitely generated, and residually finite (the Rees quotients `M/I_n` separate
points). Each of the following transcribes a group statement on the board into monoid form, and each is false at `M`.

- **CP at M.** Proposition M2 gives a constant-point cover pair. So surjunctivity does not imply CP once inverses are
  dropped. Any proof of `Gottschalk ⇒ CP`, which is what needs 36774ad3 and 06d50d0e ask for, must use
  invertibility of translations. The step where it dies is the constant target `1^M`, where `D = {1}` (Theorem F1).
- **PSD at M.** `X` is a proper strongly irreducible SFT carrying a strongly post-surjective, non-pre-injective map
  onto the full shift. So `proper-sft-domains-admit-no-dual-failures` has no inverse-free proof.
- **Finite-orbit exclusion at M.** `0^M` is a fixed point of a cover pair on a residually finite `M`. The periodic
  counting dies at the absorbing zero of `M/I_n`.
  - Long words ending in `b` carry `0`, so `F(X ∩ Per_n)` contains only tail-`0` points.
  - Hence `F` is not onto `Per_n`, and counting on `Per_n` yields no contradiction.
  - Over a group, a finite quotient `G/H` is acted on by permutations and has no absorbing coset.
- **The paradoxical input.** `Ma ∩ Mb = ∅` and `Ma ∪ Mb = M \ {ε}`. Right translation by `a` is injective but not
  onto `M`, and `F` reads the configuration through it.
  - Over a group, `x ↦ (g ↦ x(ga))` is a homeomorphism of `A^G`, so it sends a proper subshift to a proper subshift.
  - A letterwise onto map `A → A` is a bijection.
  - So no automaton with a one-element memory set is onto from a proper domain.

## 5. Scope

- F1 and F2 are elementary. Their content is that they name the invariant, the deficiencies `D_H`, and the step
  where every section, seed or de-colouring construction for the given pair dies: the `H`-fixed target in `D_H`.
  They also show (F2) that products, shears, restrictions, composites and recodings cannot repair a deficiency.
- Over groups, no deficient constant-point cover pair is known. One would be a counterexample to CP, and over a
  surjunctive `G` it would also be a counterexample to `Gottschalk ⇒ CP`.
- The sharp group question left is this: does some group (necessarily non-sofic) carry a cover pair with `D ≠ ∅`?
  If no group does, CP is equivalent to its fixed-point-surjective fragment `D = ∅`. The route uses only the
  fragment with `D_H = ∅` for all `H` (F3).
