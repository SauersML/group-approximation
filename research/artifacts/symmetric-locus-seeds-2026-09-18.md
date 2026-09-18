# Sections of cover pairs localize to the symmetric locus (2026-09-18)

Agent `swarm-0917-w9-w9-gs-last1`, wave swarm-0917. Target: the de-colouring question on
`constant-point-sft-domains-admit-no-post-surjective-covers` (CP), bus need 36774ad3.

## 0. Setting

All notation is that of `research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md`
(Sections 0–2), which is the artifact of the ESTABLISHED claim
`post-surjective-sft-covers-admit-scheduled-sections`. In particular:
- `(X, F)` is a cover pair over `A^G`: `X ⊊ A^G` an SFT with window `W`, `F : X → A^G` an automaton with memory
  `M`, strongly post-surjective with lifts in `X` with constant `Φ`;
- `N = ΦW^-1W ∪ ΦM^-1M`, `E = NΦ^-1 ∪ ΦN^-1 ∪ {1}` (finite, symmetric), `k = |E|`;
- `L_g(x, a)` is the single-site lift rule of Lemma 1, and Lemma 2 performs lifts at all sites of an
  `E`-separated set `S` at once (distinct `g, g' ∈ S` have `g^-1 g' ∉ E`). Lemma 2 changes the output only on
  `S`: `F(x^S)(h) = F(x)(h)` for `h ∉ S`. `L_g(x, a) = x` when `F(x)(g) = a` already.

A **section** is a continuous equivariant `s : A^G → X` with `F ∘ s = id`. A **seed** is any continuous
equivariant `ξ : A^G → X`.

Define the **symmetric locus** of the pair,

    Sym_E = { z ∈ A^G : e . z = z for some e ∈ E \ {1} } = ∪_{e ∈ E \ {1}} Fix(e).

It is closed (a finite union of closed sets). It is not invariant: `g . Fix(e) = Fix(g e g^-1)`. It contains
every constant configuration as soon as `E ≠ {1}`.

## 1. The localization theorem

**Theorem S.** For a cover pair `(X, F)` the following are equivalent.
1. `(X, F)` has a section.
2. Some seed `ξ` is an exact lift at the identity on the symmetric locus:
   `F(ξ(z))(1) = z(1)` for every `z ∈ Sym_E`.

*Proof of 1 ⇒ 2.* Take `ξ = s`.

*Proof of 2 ⇒ 1.* Four steps.

**Step 1 (the exact set is a clopen neighbourhood of `Sym_E`).** `F ∘ ξ : A^G → A^G` is continuous, so
`V = { w : F(ξ(w))(1) = w(1) }` is clopen: both sides are continuous maps into the finite set `A`. By
hypothesis `Sym_E ⊆ V`. By equivariance, for all `z` and `g`:

    g^-1 . z ∈ V   ⟹   F(ξ(z))(g) = F(ξ(g^-1 . z))(1) = (g^-1 . z)(1) = z(g).        (∗)

**Step 2 (a finite clopen colouring off `V`).** `K = A^G \ V` is clopen, hence compact, and misses `Sym_E`. So
`e . w ≠ w` for every `w ∈ K` and every `e ∈ E \ {1}`. For such `w` and `e`, pick disjoint clopen `P ∋ w`,
`Q ∋ e . w`; then `U = P ∩ e^-1 . Q` is a clopen neighbourhood of `w` with `U ∩ e . U = ∅`. Intersecting over
the finitely many `e ∈ E \ {1}` gives a clopen `U_w ∋ w` with `U_w ∩ e . U_w = ∅` for all `e ∈ E \ {1}`.
Compactness gives `U_1, ..., U_m` covering `K`. Put `B_j = (U_j ∩ K) \ (U_1 ∪ ... ∪ U_{j-1})`, a clopen partition
of `K`. No `B_j` contains both `w` and `e . w` with `e ∈ E \ {1}`.

Define `c : K → [k]` by recursion on `j`. For `w ∈ B_j`, `c(w)` is the least colour not in
`{ c(e . w) : e ∈ E \ {1}, e . w ∈ B_1 ∪ ... ∪ B_{j-1} }`. At most `k - 1` colours are excluded. By induction on
`j`, `c` is locally constant on each `B_j`: each step reads membership of the finitely many points `e . w` in
clopen sets, and their colours, which are already locally constant. So `c` is continuous. As in Lemma 4 of the
scheduled-sections artifact (`E` is symmetric), `c(w) ≠ c(e . w)` whenever `w, e . w ∈ K` and `e ∈ E \ {1}`.
The recursion has depth `m`, which is finite, so `c` is continuous and not merely Borel.

**Step 3 (schedule the non-exact sites).** For `z ∈ A^G` and `i ∈ [k]` let

    S_i(z) = { g ∈ G : g^-1 . z ∈ K  and  c(g^-1 . z) = i }.

Each `S_i(z)` is `E`-separated. Suppose `g, ge ∈ S_i(z)` with `e ∈ E \ {1}`. Then `w = g^-1 . z` and
`(ge)^-1 . z = e^-1 . w` both lie in `K` and have the same colour, contradicting Step 2 for `e^-1 ∈ E \ {1}`.
Moreover `S_i(h . z) = h S_i(z)`.

Put `x_0 = ξ(z)` and `x_i = (x_{i-1})^{S_i(z)}` (Lemma 2 with target `z`) for `i = 1, ..., k`. Set `s(z) = x_k`.

**Step 4 (verification).**
- *`s(z) ∈ X`.* Lemma 2 and induction on `i`.
- *`F(s(z)) = z`.* The sets `S_i(z)` are disjoint, and round `i` changes the output only on `S_i(z)`, setting it
  to `z` there (Lemma 2, item 2). So a site of some `S_i(z)` ends with output `z(g)`. A site in no `S_i(z)` has
  `g^-1 . z ∈ V`, so `F(x_0)(g) = z(g)` by (∗), and no round touches it.
- *Equivariance.* `ξ` is equivariant, `S_i(h . z) = h S_i(z)`, and `h . L_g(x, a) = L_{hg}(h . x, a)`.
- *Continuity.* `ξ` is a sliding block code. Whether `g ∈ S_i(z)` depends only on `z` on `gR` for a finite `R`,
  because `K` and the level sets of `c` are clopen. Round `i` changes `x_{i-1}` at `h` only through `L_g` with
  `g ∈ hΦ^-1`, which reads `x_{i-1}` on `gN`. By induction on `i`, as in Theorem A(3), `s(z)(1)` depends on `z` on
  a finite set. So `s` is continuous. `∎`

## 2. Consequences

**Corollary S1 (Gottschalk, localized).** `G` is not surjunctive iff some cover pair over some `A^G` has a seed
that is exact at the identity on its symmetric locus.
- ⇐: Theorem S gives a section `s`. By Proposition C of the scheduled-sections artifact, `s` is an injective
  automaton `A^G → A^G` (as `F ∘ s = id`) with image in `X ⊊ A^G`.
- ⇒: a strict pair `(τ, σ)` gives the cover pair `(X_R, σ|_{X_R})` of
  `strict-pairs-give-dual-failures-on-bounded-defect-domains` with `τ(A^G) ⊆ X_R`. Take `ξ = τ`.

So Gottschalk at `G` says: for every cover pair and every seed `ξ : A^G → X`, the automaton `F ∘ ξ` disagrees
with the identity at site `1` somewhere on the closed set `∪_{e ∈ E \ {1}} Fix(e)`. The free part plays no role.

**Corollary S2 (the de-colouring question, sharpened).** Bus need 36774ad3 asks whether a constant-point cover
pair over a surjunctive group must have a section. By Theorem S this is the same as asking for one seed that is
exact on `Sym_E`. Colourings are never needed away from `Sym_E`: on `K = A^G \ V`, Step 2 builds them
continuously from finitely many clopen sets.

**Corollary S3 (Obstruction 2 is not an obstruction).** The interface-buffer obstruction in Section 6 of the
scheduled-sections artifact concerns designs that lift on a region and keep a constant seed `c` elsewhere.
Theorem S has no interface. Every non-exact site of an arbitrary seed is lifted, and every non-exact site is
locally `E`-free by construction. So the boundary term in which "`F` has no spare capacity" does not arise, over
amenable or nonamenable `G`. The only surviving obstruction is at symmetric configurations.

**Corollary S4 (what is left: coset lifts along `⟨e⟩`).** Let `ξ` be a seed and `e ∈ E \ {1}`. For `z ∈ Fix(e)`
equivariance gives `ξ(z) ∈ Fix(e) ∩ X`, and exactness at `1` is exactness along the orbit `⟨e⟩`:
`F(ξ(z))(e^j) = F(ξ(e^-j . z))(1) = F(ξ(z))(1)`, and `z(e^j) = z(1)`. So on `Fix(e)` a seed must lift
simultaneously at all sites `e^j`, `j ∈ Z`, by an `e`-invariant patch. Because `e ∈ E`, the write regions
`e^j Φ` meet the read regions `e^{j'} N`, so Lemma 2 does not apply. This is the precise residual step.
- `G`-fixed points: `Fix(e) ⊇` constants, and exactness at `a^G` forces a constant `b^G ∈ X` with
  `F(b^G) = a^G`. This recovers Obstruction 1 at `H = G`.
- A negative answer to the de-colouring question must therefore come from a constant-point cover pair in which
  no seed solves the `⟨e⟩`-coset lift problem for some `e ∈ E \ {1}`. A positive answer must solve that problem
  continuously on `Fix(e)`, compatibly across the finitely many `e`, and nothing else.

**What this does not do.** It does not decide CP at any nonsofic group. It does not give Gottschalk ⇒ CP. It
replaces the question "de-colour a scheduled section over all of `A^G`" by the question "find a seed exact on
the closed set `∪_{e ∈ E \ {1}} Fix(e)`", on which the colouring obstruction is concentrated.
