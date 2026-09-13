# Matricial crossed products, part 2: invariant measure, free groups, and the Z^2 boundary

Lane `un-measure`, 2026-09-13. Part 2 of 2. Written proofs, UNREVIEWED. Part 1:
`research/artifacts/un-measure-residually-finite-lef-rings-2026-09-13-part1.md`.

## 3. Proposition B: matricial models force an invariant measure

**Proposition B.** Let `𝒢` be a Hausdorff ample groupoid with compact unit space `X`, `k` a field,
`A = A_k(𝒢)` its Steinberg algebra, and `Ψ : A -> ∏_ω M_(N_n)(k)` a unital ring homomorphism, not
assumed injective. Then:
1. `rk(a) = lim_ω rank(ψ_n(a))/N_n` is a unital Sylvester matrix rank function on `A`, where
   `ψ_n` is any representative sequence.
2. `μ(U) = rk(1_U)` is finitely additive on clopen sets, with `μ(X) = 1`, and `𝒢`-invariant:
   `μ(s(B)) = μ(r(B))` for every compact open bisection `B`. It extends to a `𝒢`-invariant Borel
   probability measure on `X`.
3. If `Ψ` is injective, `A` is stably finite. If also `k` is finite, every finitely generated
   subgroup of every `GL_m(A)` is LEF.

*Proof.*
1. The normalized rank of `∏_ω M_(N_n)(k)` is a Sylvester matrix rank function, as an ultralimit
   of those of `M_(N_n)(k)`. Pulling back along a unital homomorphism keeps the axioms, and
   `rk(1) = 1`.
2. Disjoint clopen `U, V` give orthogonal idempotents with `1_(U ⊔ V) = 1_U + 1_V`, and rank is
   additive on orthogonal idempotents. For a compact open bisection `B`, put `x = 1_B` and
   `y = 1_(B^(-1))`. Then `xy = 1_(r(B))` and `yx = 1_(s(B))`, and algebraically equivalent
   idempotents have equal rank. The clopen algebra of a compact totally disconnected metrizable
   space is a Boolean algebra on which every finitely additive probability is countably additive
   (by compactness), so Carathéodory extends `μ` to a Borel probability, invariant on bisections.
3. `M_m(∏_ω M_(N_n)(k)) ≅ ∏_ω M_(m N_n)(k)` is directly finite, and a subring of a directly finite
   ring is directly finite. For finite `k` the ultraproduct groups `∏_ω GL_(m N_n)(k)` are
   ultraproducts of finite groups. ∎

**Calibration (the paradox side must fail).**
- *Cuntz groupoid*, `A = L_k(1,2)`: there are compact open bisections `B_1, B_2` with
  `s(B_i) = X` and `r(B_1) ⊔ r(B_2) = X`, so `μ(X) = 2μ(X)`, which is impossible. Hence
  `L_k(1,2)` has no unital homomorphism into any `∏_ω M_N(k)`. This agrees with
  `leavitt-algebra-has-no-unital-rank-model`, which proves the stronger rank-metric statement.
- *Pestov's ring:* `μ` is the unique invariant measure of the minimal subshift when it is
  uniquely ergodic. In general it is some invariant measure selected by the towers.

## 4. Theorem C: free groups

**Import (secondary).** Ma, arXiv:2209.00580, Remark after `thm: topo group of residually finite
action`, read from source: "it was shown in [K-N, Theorem 5.2] that any minimal action of the free
group `F_r` (`r ∈ N ∪ {∞}`) on the Cantor set is residually finite if it admits an `F_r`-invariant
Borel probability measure". The primary paper (Kerr–Nowak, Ergod. Th. Dynam. Sys. 32 (2012)
1582–1614) was NOT read: arXiv and Semantic Scholar API queries were rate-limited (HTTP 429).

**Theorem C.** Let `F_r` (`r ∈ N ∪ {∞}`) act minimally and topologically freely on the Cantor set
`X`, `k` a field, `R = LC(X,k) ⋊ F_r`. The following are equivalent:
- (i) `X` carries an `F_r`-invariant Borel probability measure;
- (ii) the action is residually finite;
- (iii) `R` embeds unitally and injectively in some `∏_ω M_(N_n)(k)`;
- (iv) `R` admits a unital homomorphism into some `∏_ω M_(N_n)(k)`;
- (v) `R` carries a unital Sylvester matrix rank function.

*Proof.*
- (i) ⇒ (ii): Kerr–Nowak Theorem 5.2 (import above).
- (ii) ⇒ (iii): Theorem A.
- (iii) ⇒ (iv): trivial.
- (iv) ⇒ (v): Proposition B.1.
- (v) ⇒ (i): the argument of Proposition B.2 uses only a unital Sylvester rank function.
∎

**Where the dichotomy is sharp.** When (i) fails, `R` has no rank function at all. Such actions
include the boundary action `F_2 ↷ ∂F_2`, whose groupoid is purely infinite, so the non-MF paper's
Corollary l.1016 applies to `EL_n(R)`. They also include Boldrini–Prasad actions without
comparison (arXiv:2607.01896), where no invariant measure exists but `R` need not be paradoxical
at `[1]`. Theorem C says nothing about the group `EL_n(R)` in that middle case. That is target U4.

## 5. Proposition D: the Z^2 boundary

**Proposition D.** Let `Ω ⊆ A^(Z^2)` be a free minimal SFT (forbidden patterns in `B_r`), `k` a field,
`R = LC(Ω,k) ⋊ Z^2`. If `R` embeds unitally in `∏_ω M_(N_n)(k)`, then for every `D >= r` there are a
nonzero finite-dimensional `k`-space `W`, commuting invertibles `U_1, U_2 ∈ GL(W)` and idempotents
`E_a(z)` (`a ∈ A`, `z ∈ Z^2`) satisfying (Q1)–(Q3) of `sft-crossed-product-fp-iff-quantum-rigid`, with
`E_a(z) = U^z E_a(0) U^(-z)`.

*Proof.* Put `W = k^(N_n)` for an `n` in the ω-set where `ψ_n` is exact on the finitely many elements
below, `U_i = ψ_n(u_(e_i))`, and `E_a(0) = ψ_n(χ_[a])`. Take for granted the finitely many identities
in `R`:
- `Σ_a χ_[a] = 1` and `χ_[a] χ_[b] = δ_ab χ_[a]`;
- `[u_z χ_[a] u_z^(-1), χ_[b]] = 0` for `|z| <= 2D`;
- `Π_(h ∈ B_D) u_h χ_[π(h)] u_h^(-1) = 0` for forbidden `π`;
- `u_(e_1) u_(e_2) = u_(e_2) u_(e_1)`.

They are exact in `ψ_n`, and conjugating by `U^z` gives (Q1)–(Q3) at every `z`. `W != 0` since
`N_n >= 1`. ∎

**Consequences** (with existing claims):
- **Classical towers stop.** `Ω` has no finite orbit, so the action is not residually finite
  (`sfts-without-finite-orbits-are-not-residually-finite-actions`), and Theorem A does not apply,
  although an invariant measure always exists (`Z^2` is amenable).
- **Quantum tilings are forced.** Over a finite field, the families in Proposition D are periodic
  quantum tilings. For aperiodic `Ω` they are noncommuting at every scale and refute `D`-quantum
  rigidity (`periodic-quantum-tilings-refute-quantum-rigidity`, item 1).
- **Rigid SFTs are never matricial.** If `Ω` is `D`-quantum rigid for some `D`, then `R` admits no
  unital matricial embedding. This is consistent with `lef-simple-rings-are-not-finitely-presented`
  combined with `sft-crossed-product-fp-iff-quantum-rigid`, which is an independent route to the same
  conclusion.
- **Converse (proved in `matricial-z2-sft-crossed-products-give-quantum-tilings-proof`; review 2026-09-13).** Covariant
  families at every scale make `R` matricial: the local presentations have colimit `R`, window identities hold at a
  finite stage, a finite-dimensional module gives a window-exact map, and Lemma S applies. Labbé's shift reduces to
  `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`.

## 6. New families, and the unification picture

- **Toeplitz subshifts over free groups.** Cecchi-Bernales–Cortez–Gómez, arXiv:2305.09835, Theorem
  `theo:main1`, read from source: "Let `G` be a countable residually finite group and let `←G` be a
  totally disconnected metric compactification of `G` equipped with the action of `G` by left
  multiplication. Then there exists a uniquely ergodic Toeplitz `G`-subshift `(X, σ, G)` and an almost
  1-1 factor map `π : X -> ←G`, such that [...] `π` is a measure conjugacy [...]". Ma's Corollary
  `cor: amenability and LEF` (read from source) uses this for `F_r`.
  - Take `←F_r` the odometer of a nested chain of finite-index normal subgroups with trivial
    intersection. It is free.
  - **Topological freeness of `X`.** The injectivity points `{x : |π^(-1)(πx)| = 1}` are a dense
    `G_δ`, since `π` is almost 1-1. If `gx = x` at such a point, then `g πx = πx`, so `g = e`.
  - **Minimality.** Toeplitz subshifts are orbit closures of regularly recurrent points, hence minimal
    (standard, not re-read).
  - Unique ergodicity gives (i) of Theorem C.
  For such `X ⊆ Σ^(F_r)` with `r` finite:
  - the ring `R = LC(X,F_q) ⋊ F_r` is finitely generated (by `u_(s_i)^(±1)` and the letter cylinder),
    simple (Lemma 2.1) and matricial (Theorem A);
  - so `G_n = EL_n(R)` is, for `n >= 3`, a finitely generated **LEF Kazhdan group over a crossed
    product by a non-amenable free group** (Corollary A1).
  - Simplicity of `G_n` modulo its centre needs the root-detection argument for free minimal actions
    of finitely generated groups (towers indexed by balls). That is open here: target of
    `un-simplicity`.
- **Products.** For minimal residually finite `α_1, α_2`, the product action of `Γ_1 × Γ_2` is
  minimal, free when both are free, and residually finite (take products of models), with
  `R = R_1 ⊗_k R_2`.
- **Unification picture (U2 side).** Across Steinberg algebras of transformation groupoids:
  - exact finite dynamics, i.e. residual finiteness, gives matricial rings, hence LEF elementary
    groups (the Pestov side);
  - a matricial model always gives an invariant measure (Proposition B);
  - paradoxical `[1]` (Cuntz, boundary actions) kills every model, and the non-MF paper's full
    complementary idempotents kill MF quotients of `EL_n` (the non-MF side);
  - the two ring-level conditions coincide exactly for free groups (Theorem C) and separate at
    `Z^2`, where the gap is precisely noncommuting periodic quantum tilings (Proposition D).

## 7. Credit and bounds

- Kerr–Nowak (residual finiteness, Theorem 5.2 via Ma's restatement); Ma arXiv:2209.00580 (Theorem C,
  the Toeplitz corollary: the group-level analogue of Theorem A); Grigorchuk–Medynets arXiv:1105.0719
  (LEF for `Z`); Pimsner (chain recurrence); Ara–Claramunt arXiv:1902.06476 (approximating subalgebras
  for `C_K(X) ⋊_T Z`); Ershov–Jaikin-Zapirain (property (T)).
- **Novelty, bounded.** `un-prior-art` found no source giving an exact algebraic ultraproduct embedding
  of `LC(X,k) ⋊ Γ` for residually finite actions beyond `Z`, and no ring-level free-group equivalence.
  No web search was run by this lane.
- **Not re-read:** Kerr–Nowak primary; Clark–Edie-Michell–Sims and Steinberg (not used, since Lemma 2.1 is
  proved directly); Carathéodory and the rank-function axioms (standard).
