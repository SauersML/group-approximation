# EX review, wave 2, part 6: quantum rigidity, Radu's lattice, SL_3(Z) factors, dyadic vertex models (2026-09-13)

Lane `ex-verify2-groups`. Index: `ex-review2-groups-2026-09-13.md`. Read at tip `0f57d3cdf`.

## 1. ex2-labbe-quantum-rigidity and ex2-labbe-relation-climbing: all three PASS

The relations are (Q1)--(Q3) of `sft-crossed-product-fp-iff-quantum-rigid`: a partition of unity at each site,
commutation for `|z - z'| <= 2D`, and vanishing of products over forbidden `B_D`-patterns. They were checked against
the ring artifact `sft-crossed-product-presentation-rigidity-2026-09-13.md` §§1--2.

**`sft-wall-rigidity-iff-idempotent-commutator-ideal`.** PASS on Theorems 1 and 2 and on 1 => 3 => 4 => 1.
- *Theorem 1.* Write an upper-triangular idempotent partition with diagonal `(T_1, T_2)` as `[[s_a, μ_a],[0, t_a]]`.
  - Idempotence forces `μ_a (s_a + t_a - 1) = 0`, so `μ = 0` off Δ. At a site of Δ, orthogonality and `Σμ = 0` give
    `μ_a = λ(z)(s_a - t_a)`.
  - Commutation of two sites within `2D` of each other is `(λ(z) - λ(w))(s_a - t_a)(s_b - t_b) = 0`, so λ is constant
    on `2D`-components.
  - (Q3) telescopes to `λ(Π s - Π t) = 0`, because the Δ-sites of a `D`-ball lie in one component.
  - The family commutes iff λ is constant on Δ.
- *Theorem 2.*
  - At split sites a 2×2 partition is an unordered pair of lines, and two split sites commute iff their pairs agree.
  - A `D`-ball meets at most one `2D`-component of the split set. There the family is simultaneously diagonal, so
    reading one line per component gives a legal configuration.
  - Flipping exactly two components gives `T_1, T_2 in Ω` whose difference set is those two components.
- *Theorem 3.*
  - *Point localization.* The clopen sets `V` with `1_V m = m` form a filter, which has a point `y` by compactness,
    and then `m notin m_y M`.
  - *The representation.* Given the splitting `C/J^2 ≅ LC(Ω) ⋉ J/J^2`, a `(T_1,T_2)`-equivariant functional φ gives an
    algebra map `f + μ ↦ [[f(T_1), φ(μ)],[0, f(T_2)]]`.
  - *The splitting (Lemma 3.2).* Idempotent lifting along the square-zero ideal, read at outline level.
- *Corollary 3.3.* A `J`-nilpotent action with `J = J^m` is zero.

**`periodic-quantum-tilings-refute-quantum-rigidity`.** PASS.
- A one-dimensional composition factor of `V` over `C_D` is a character of the finite-dimensional image `𝔅`, and it
  reads off a legal configuration.
- `u^g` permutes the finitely many maximal ideals of `𝔅`. So the configuration has a finite-index stabilizer, hence
  is periodic, a contradiction.
- A commuting family generates a commutative algebra spanned by idempotents, which is split semisimple. So its
  simple modules are one-dimensional over any field.
- Over a finite field `GL(V)` is finite, which gives periodicity. The converse module is `W ⊗ k[Z^2/Λ]`.

**`zd-derived-full-group-fp-excludes-periodic-quantum-tilings`.** PASS.
- *Lemma 1 of the ring artifact, re-derived.*
  - A word of length `<= D` has normal form `P_(g_1)^(a_1)...P_(g_s)^(a_s) u^g` with `|g_j| <= D`, and these `P` commute.
  - Expanding by the partitions at `B_D` gives legal cylinder products times `u^g`. These are independent in `R_X`.
  - So a short combination vanishing in `R_X` vanishes in `A_D`.
- *The homomorphism.* For `D >= D_0` it gives `G -> A_D^×`.
- *Linearity.* The image in `GL(V)` is finitely generated and linear, hence residually finite (Malcev). It is a
  quotient of the infinite simple `G`, so it is trivial.
- *The zero module.* The 3-cycle identity `χ_C (U_s - 1) χ_C = -χ_C` holds because `s^(-1)(C) = s^2(C)` is disjoint
  from `C`. So every `χ[π]` acts by zero, and `V = 0`.
- *Import.* `minimal-z2-subshift-derived-full-groups-are-fg-simple` imports Chornyi--Juschenko--Nekrashevych and
  Nekrashevych; it was read from TeX by its owner and not re-read here.

## 2. ex2-radu-chain-lamp-positive and ex2-radu-superstrong-negative: all three PASS

The imports `radu-bmw-lattice-embeds-in-titz-witzel-kernel`, `radu-horizontal-projection-kills-delta-squared`,
`radu-horizontal-quotient-is-arithmetic-lattice` and `radu-horizontal-tree-group-is-linear` already have PASS verdicts
in the ex-review-dynamics artifacts.

**`radu-delta-squared-orbit-is-signed-permutation-module`.**
- *Rewriting rules.* `az = zb`, `bz = za`, `cx = zc`, `cz = xc`, `by = yc`.
- *Item 1.* All five conjugations re-derived letter by letter. `c·xzxz·c = zxzx = δ^(-2)`.
- *The sign character.* `ψ'` is well defined, since each relator uses `c, x, z` an even number of times.
- *The basis.* The `{x,z}`-components of `Cay(W)` are the edge-disjoint 4-cycles `wD_2`, hence independent in
  `H_1`. `q = wh` gives `q·m_0 = ±[wD_2]`, and the sign is consistent on `D_2 ⊆ H_Q`: `x` reverses the orientation,
  and `ψ'(x) = -1`.
- *Item 4.* `ĥ = kλ`, with `λ` commuting with `δ^2` in the abelian `M`, gives `π(δ^4) = 1`. An open subgroup
  contained in `ker ψ'` would make it closed.

**`radu-metabelian-quotient-embeds-in-edge-lamp-wreath`.**
- *The cocycle.* It is the tree identity `[o, gh·o] = [o, g·o] + g_*[o, h·o]`, and its kernel is the kernel of
  Hurewicz on the free group `π_1(Y)`.
- *The edge orbits.*
  - `a` and `b` fix the link of `o`, and `c` swaps `xo ↔ zo`. So the `y`-edges form `Q/C` and the `{x,z}`-edges
    form `Q/C_χ`.
  - `y` and `x` reverse their edges inside their orbits.
- *`D_4`.*
  - `D_4 ∩ C_χ = 1`, because `W ∩ C = 1` and `c notin C_χ`.
  - `x(cac)x = c(zaz)c = cbc` and `x(cbc)x = cac`.
  - The signs `ε(g)` on the eight edges of the square match the list.
- *Item 3.* GKP Theorem 3.6 (= Theorem A, verbatim).

**`radu-square-lamp-forces-reflections-in-finite-actions`.**
- *Item 1.* `Ψ` lands in the finite group `(Z/32)[Q/K] ⋊ Q/N`, and `gK = g'K` iff `g^(-1)g' in H = D_4 ∩ K`. If
  `ε|H = 1`, the coefficients `±2|H|` lie in `{±2, ±4, ±8, ±16}`, all nonzero mod 32. That contradicts the finite
  residual of `Γ_R`.
- *Item 2.* The point `C_χN`, with `g = kn`, gives `n = k^(-1)g in H_Q ∩ N` and `ψ'(n) = ψ'(g) = -1`.
- *Item 3.* The orbit of `f` in `B^A` is finite, and item 1 applies.
- *Reading note.* Item 2 proves non-closedness unconditionally, so the "iff" in the node's closing paragraph holds
  because both sides are true.

## 3. ex2-sl3z-cocompact-weak-containment: all three PASS

**Citations, checked against the arXiv PDFs.** Ioana arXiv:0805.2998v1 Theorem B, and Popa arXiv:math/0512646v8
Theorem 0.1 (second sentence). Details in §5.

**`sl3z-cocompact-not-factor-of-bernoulli-times-profinite`.**
- *The coupling cocycle.* `c(γ,x) = g_(γx)^(-1) γ g_x in Λ`, and the identity checks.
- *Untwisting.* Popa and then Ioana give `w = φ(γz) v''(γ, r_n q z) φ(z)^(-1)`, and at a fixed point of `X_n` this
  is a homomorphism `ρ : Γ_a -> Λ`.
- *Finite image.* BMS gives an algebraic `F` agreeing with `ι∘ρ` on `Γ'`.
  - `ker F` is `SL_3` or central.
  - `e_12^N in Γ'` by pigeonhole.
  - A nontrivial `F` would send `e_12^N` to a nontrivial unipotent in `ι(Λ)`, which (R) forbids.
- *The contradiction.* `Ψ̃ = g_Ψ φ` is `Γ_1`-equivariant on `Y_a`. A `Γ_1`-invariant probability measure on `G` is
  impossible, by the Borel fundamental domain.
- *Scope.* The node's calibration section correctly says the theorem does not separate `Λ` from `SL_3(Z)`.

**`ioana-profinite-cocycle-superrigidity`, `popa-bernoulli-product-cocycles-come-from-cofactor`.** PASS on the
citations (§5). The matching of hypotheses holds: `Γ_0 = Γ` with (T); a countable `Λ` is of finite type; the Bernoulli
action over `([0,1], Leb)` is mixing. Popa's definitions of "rigid" and "w-normal" were not re-read, as the route says.

## 4. ex2-dyadic-vertex-action: all three PASS

**`expanding-matchings-need-a-shared-stabilizer`.**
- *Lemma G.* `|O| = |Bx|[Stab x : Stab x ∩ Stab y]`, and the graph of τ projects injectively. So occupying more than
  half of an orbit forces both indices to be 1, and hence coincidence.
- *Even levels.* Conjugation by `g` is `[[a,b],[c,d]] ↦ [[a, b/2],[2c, d]]`. The two unipotent tests require
  `M >= M'+1` and `M'-1 >= M`, which cannot both hold. The cases `M' = 0` and `M = 0` use `[[1,m'],[0,1]]` and
  `[[1,0],[2m,1]]`.
- *Expansion.* `Γ(2N) ⊆ Γ_1(N)`, checked entrywise, so orbits are quotients of `B/Γ(2LL')`. `f = 1_U - |U|/|O|` has
  `||f||^2 >= |U|/2`, and `||sf - f||^2 = 2|∂_s U|`, which gives `h_S = κ^2/4`.
- *Imports.* Selberg's `(τ)` and its transfer to the finite-index `B`, at outline level.

**`homogeneous-quotient-soficity-gives-vertex-soficity`.**
- *The label.* `f_x(gΛ_N) = Λ_N g^(-1) x` is well defined, exactly equivariant and locally constant.
- *Separation.* Equal labels give `λ in h(KwK)h^(-1)` with `w = a_1^(-1)a_2 notin K`.
- *Lemma S.* `Λ_1 ∩ ΩKWKΩ^(-1)` is finite and misses `1`, and normality of `Λ_N` in `Λ_1` moves any hit into it.
- *The orbit approximation.* `π_v(x) = f_x(y(v))`. By (P3) and then (P1), `π_(φ(g)v)(x) = f_(g^(-1)x)(y(v))`. The
  multiplicativity defect is at most `2η`, with the case `gh = 1` handled through `σ(1)`.
- *The dyadic instance.* `A ∩ K = C`, strong approximation, and the Cartan decomposition give density and unique
  ergodicity.

**`twin-deep-vertex-models-give-homogeneous-microstates`.**
- *(TD0).* The Atkin--Lehner element `[[a,b],[c,d]] ↦ [[d, c/2],[2b, a]]` swaps `N_0 ↔ N_1` and fixes `Δ_R`.
- *(b).* The stabilizer law is invariant under `⟨C_0, C_1⟩ = C_0 *_B C_1 = A`. So `S(w)` lies in the normal core of
  `N_0 ∩ N_1`, which is central by `sl2-s-arithmetic-noncentral-normal-subgroups-have-finite-index`, hence trivial.
  But `S(w)` has finite index in `C_0`.
- *(a).*
  - Lemma F: the stabilizer of `(qN, w)` is `N ∩ Stab(w) = Stab(w)`, so `(Δ/N) × W ≅ [Δ:N]·W`.
  - Induced fibres over `B/Δ_R`, with equal indices, give τ with `B`-defect `O(ε)`.
  - Marks lose one level for `C_1`, since `K_1(2^(R-1)) <= K(2^(R-2))`, and `ℓ` levels for words of length `ℓ`.
  - Read at outline level.

## 5. Sources read in this part

- **Ioana.** arXiv:0805.2998v1 Theorem B (cocycle superrigidity for profinite actions), with Theorem A's hypotheses;
  quoted in the node, confirmed in the PDF text.
- **Popa.** arXiv:math/0512646v8 Theorem 0.1 (cocycle superrigidity, the `σ × ρ` sentence); confirmed in the PDF text.
- **GKP arXiv:2401.04945.** Definition 2.1, Proposition 2.15 (1)--(3), Theorem 2.17, Remark 2.18 and Theorem 3.7,
  verbatim in the PDF text. This covers every GKP input consumed in parts 5 and 6.

## 6. Verdicts

| claims | verdict |
|---|---|
| labbe quantum rigidity (2), relation climbing (1) | PASS |
| radu chain lamp (1), superstrong negative (2) | PASS, one reading note |
| sl3z cocompact weak containment (3) | PASS |
| dyadic vertex action (3) | PASS; (a) of the twin-deep theorem and the `(τ)` transfer at outline level |
