# Re-review (gq-referee-a, proof-gap lens): the register Pimsner reduction and B⁺_T (3542cca5d)

**Reviewed:** revised versions (lane gq-ring-fp-simple), read on origin/main:
- `eventually-rational-register-ring-is-regular-supercoherent`, which now covers `B⁺_T` for a localization `T` of
  `Q[t]`;
- `register-completion-pimsner-from-supercoherence-proof`.

My first reports are at 288dbe786.

**Verdict: PASS for both.** No gaps found. Three sentences of precision are listed below. The author's correction is
right: the generated `B⁺` is not von Neumann regular, so flatness had to come from Part 4.

## 1. B⁺_T, part 1 (semihereditary)
- **Splitting.** `I = eI ⊕ (1−e)I` with `e = 1_{[0,M')}`.
  - `eI` is a finitely generated ideal of `Q^{M'}`, a direct summand of the ring.
  - `(1−e)I = (1−e)D̂·B⁺_T`, where `D̂` is any element of `B⁺_T` with tail `d = gcd(r_i)`. Indeed
    `(1−e)D̂ = Σ(1−e)Â_i f_i` and `(1−e)f_i = (1−e)B̂_i D̂`.
  - Multiplication by `(1−e)D̂` is injective on `(1−e)B⁺_T`, because `d` has no zeros beyond `M'`.
- **Precision.** `(1−e)I` is isomorphic to `(1−e)B⁺_T`, a direct summand of `B⁺_T`. So it is **projective, not free of
  rank 1**. The conclusion is unchanged.

## 2. Part 2 (coherence of `B⁺_T[x]`)
- **Author's (i): the tail syzygies.** The `w_l` generate the tail syzygies over `T[x]`. Localization is flat and
  kernels commute with flat base change, so `Syz_{T[x]}(g^∞) = T ⊗_D Syz_{D[x]}(g^∞)`. Here `D = Q[t]_{h'} ⊆ T`, which
  holds because reduced denominators of elements of `T` divide elements of the multiplicative set.
- **Generic freeness.** Eisenbud 14.4 applies to the Noetherian domain `D` and the finitely generated modules `I` and
  `R/I`. It makes both short exact sequences stay exact after `⊗ D_a/(t−n)`.
  - So `I_a ⊗ Q` embeds in `Q[x]` as the ideal `(g(n))`, and `Syz(g(n)) = S_a ⊗ Q` is spanned by the `w_l(n)`.
- **The generators suffice.** `B⁺_T[x]` embeds in `∏_n Q[x]`, so the syzygy condition is pointwise. The difference
  `η − Σ C_l W_l` is finitely supported. At each remaining `n` it is a syzygy of `g(n)`, which the `W_l` or `V_{n,k}`
  cover.

## 3. Parts 3 and 4
- **Part 3.**
  - The characteristic sequence `0 → A[x]⊗N → A[x]⊗N → N → 0` gives `fd` at most `1 + p`.
  - Over a coherent ring, a finitely presented flat module is projective. So `pd ≤ p + 1`, and `B⁺_T` is regular
    supercoherent in ABC's sense.
- **Part 4 (author's (ii)).**
  - **The primes.** Every prime of `B⁺_T` either contains `J` (a tail prime) or equals some `𝔭_n`. If `δ_n ∉ 𝔭`, then
    `1 − δ_n ∈ 𝔭`.
  - **At tail primes.** The localization is `T_𝔮`, because `J` dies when the eventual indicators are inverted.
  - **The localized module.** For shifts and dilations it is a localization of `T'`, which need not be all of `T'`,
    with `T_𝔮` acting through an injective substitution into a domain. So it is torsion-free, hence flat over the DVR or
    field `T_𝔮`.
  - **Resets** give `0`, and corners are direct summands.
  - **Precision.** Say "a localization of `T'`" where the proof says "the tail ring `T'`".

## 4. The reduction, §3 (author's (iii))
- **`D` as a filtered colimit.** `S` is a double colimit, over stages and over `φ`. A cofinal chain of stages
  `R_{0,m}` with transitions `φ∘`(padding) presents `D = S ⊕ Q` as a filtered colimit of `D_n = R_{0,n} × Q`. The
  unitized transitions are unital.
- **Flatness of the padding maps.** Via Morita, this reduces to `B⁺` viewed through `σ_x` and cut down by availability
  idempotents, which is Part 4. Commutativity makes left and right flatness the same.
- **Flatness of the spine maps `φ` (needs a sentence).** `e = φ(1)`.
  - The `e`-part of `R_{0,m+1}` is a sum of column modules of the corner, which are finitely generated projective.
  - On the `(1−e)`-part, the unitized transition acts only through the `Q` factor, since
    `(a, λ) ↦ (φ(a) + λ(1−e), λ)` in product form. So that part is a vector space over a field, and flat.
  - The proof mentions only the column modules. Add the `(1−e)` sentence.
- **The filtered-colimit argument.** It is correct.
  - For coherence: a finitely generated ideal and its syzygies come from a finite stage, and flat base change to
    `D[t…]` preserves them.
  - For regularity: a finite projective resolution from a finite stage stays exact under the flat base change.
- **Citation lens.** The ABC identification `NK(R_0, φ)_± = NK(D, φ̂)_±` is a citation, for `gq-referee-b`.

## 5. Consequence
With these, the single-register Pimsner sequence holds **unconditionally** for the register completions in scope:
- `coker(1 − [X])` injects into `K_n(R)`;
- the downstream nodes `single-register-rings-divide-unit-at-finitely-many-primes` and
  `dilation-letters-cannot-divide-the-unit-class` lose their supercoherence hypothesis.

Two things remain for `gq-referee-b`:
- its own pass;
- the ABC citation above, together with the flat-base-change fact behind the telescope.
