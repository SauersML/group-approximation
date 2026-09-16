# Parity-clean arcs only see Burau modulo t+1: an explicit Brunnian obstruction

Swarm frontier lane `hi-fron-zaremsky-3-05-four-strand-bura`, 2026-09-16.
Root: `zaremsky-3-05-four-strand-burau-faithful`.

## 0. Summary and graph map

- **Theorem A** (§5). Let `𝔞` be an ideal of `Z[t^{±1}]` that is stable under `t ↦ t^{-1}`. If
  `ρ_n(Ψ) ≡ I mod 𝔞`, then for every `Γ ∈ B_n` the loop classes of `(β_*^3)ΨΓ` and
  `(β_*^3)Γ` have intersection forms congruent mod `𝔞`.
  - `𝔞 = 0` gives Moody's criterion (Corollary A1), with a complete proof. That is route
    `moody-polynomial-change-certifies-burau-nonkernel-proof`.
  - `𝔞 = (t+1)` gives `𝕄_{ΨΓ}(−1) = 𝕄_Γ(−1)` (Corollary A2).
- **Parity lemma** (§6). A transverse representative satisfies the parity condition iff
  `|𝕄(α, A)(−1)| = |A ∩ α|`. Equivalently, parity means no cancellation at `t = −1`.
- **Theorem B** (§7). If `ρ_n(Ψ) ≡ I mod (t+1)`, then parity-clean representatives of
  `(β_*^3)ΨΓ` and `(β_*^3)Γ` cross `α` equally often. This is claim
  `parity-clean-arc-counts-see-only-burau-mod-t-plus-one`.
- **The braid `Φ_0`** (§8). `Φ_0 = [(σ_1σ_2)^6, [A_14, [A_24, A_34]]]` is a nontrivial Brunnian
  4-braid with `ρ_4(Φ_0) ≡ I mod (t+1)` and `ρ_4(Φ_0) ≠ I`. This is claim
  `burau-minus-one-kernel-meets-brunnian-four-braids`.
- **Refutation** (§9). The two facts together refute
  `brunnian-four-braids-admit-parity-correcting-push`, via claim
  `parity-correcting-push-fails-for-a-brunnian-four-braid`. The route
  `five-strand-moody-witness-via-parity-correction` becomes invalid as a result.
- **Consequences** (§10).
  - For `Φ_0`, at least one of the following steps of arXiv:2607.05283v1 is false: the
    conjugation step of Theorem 6.6, Proposition 6.4, or Proposition 5.1 in the form used there.
    The same holds for the corresponding statement of v2 (preliminary; §10.1).
  - More sharply: any braid that the parity mechanism can certify is already outside the
    kernel of Burau at `t = −1`, where non-membership is visible anyway. So the mechanism
    carries no information about `ker ρ_4` beyond `t = −1`.
  - The witness claim `brunnian-four-braids-have-five-strand-moody-witness` stays open. For
    `Φ_0`, the evidence in §10 suggests a witness exists but is not parity-clean.

Scripts: `experiments/zp-burau-parity-t-minus-one-2026-09-16/` (exact integer arithmetic).

## 1. Setting and conventions

- `D` is the closed unit disk and `P = {p_1, ..., p_n}` are marked points on the horizontal
  diameter, in order. `D_n = D \ P`. The base point `p_*` is a point of `∂D`.
- `α` is the arc from `p_1` to `p_2`, and `α° = α \ {p_1, p_2}`. The set `α°` is closed in
  `D_n`.
- `β_*^3` is an embedded arc from `p_*` to `p_3` whose interior lies in `D_n`.
- For a loop `γ` at `p_*`, `φ(γ) = Σ_j wind(γ, p_j)` is the total winding number.
  - `φ : π_1(D_n, p_*) → Z = ⟨t⟩` is written multiplicatively.
  - `π : D̃ → D_n` is the covering space with group `ker φ`, with deck group `⟨t⟩`.
  - `p̃_*` is a fixed lift of `p_*`, and `P̃_* = π^{-1}(p_*) = {t^j p̃_*}`.
- `H = H_1(D̃, P̃_*; Z)` is a `Z[t^{±1}]`-module through the deck action.
- `B_n` is identified with the mapping class group of `(D, P)` rel `∂D`, and `σ_i` is the
  half-twist exchanging `p_i` and `p_{i+1}`. The direction of the twist and the order of
  composition are conventions; §4 shows that nothing below depends on them.
- Unreduced Burau: `ρ_n(σ_i) = I_{i−1} ⊕ [[1−t, t], [1, 0]] ⊕ I_{n−i−1}`, and
  `ρ_n(w) = ρ_n(s_1) ⋯ ρ_n(s_r)` for a word `w = s_1 ⋯ s_r`. For every `n`, the reduction
  `ρ̄_n = ρ_n mod (t+1)` (that is, `t ↦ −1`) is a homomorphism `B_n → GL_n(Z)`.
- Word operations:
  - `rev(w)` is `w` read backwards;
  - `inv(w)` is the inverse word;
  - `mirror(w)` replaces each `σ_i^{±1}` by `σ_i^{∓1}` in place, so `mirror = rev ∘ inv`.
- The **Moody polynomial** of an arc `A` from `p_*` to a marked point:
  `𝕄(α, A) = Σ_ℓ (t^ℓ α̃, Ã) t^ℓ`.
  - `α̃` is a lift of `α°`, fixed once and for all.
  - `Ã` is the lift of `A` starting at `p̃_*`.
  - `( , )` counts signed transverse crossings.
  - For a transverse representative crossing `α` at `q_1, ..., q_m` (in order along `A`),
    `𝕄(α, A) = Σ_i ε_i t^{k_i}`, where `ε_i` is the crossing sign and `Ã` meets `t^{k_i} α̃`
    over `q_i`.
  - `𝕄_Γ := 𝕄(α, (β_*^3)Γ)`.
  - That `𝕄` does not depend on the transverse representative is proved in §3.
- **Disk sequence and parity** (the preprint's Lemma 3.1 and Lemma 4.2, as recorded in
  `zp-burau-n4-verification-2026-09-13-part1.md`, S4–S5).
  - For `1 ≤ i < m`, `C_i = A[q_i, q_{i+1}] ∪ α[q_i, q_{i+1}]` is a simple closed curve. The
    two pieces meet only at `q_i` and `q_{i+1}`, because the arc piece has no interior
    crossing with `α`. `C_i` bounds a disk `Δ_i ⊂ D`.
  - `Δ_i` is **sign-changing** iff `ε_{i+1} = −ε_i`.
  - `A` satisfies the **parity condition** iff for every `i`, `Δ_i` is sign-changing exactly
    when `|P ∩ Δ_i|` is odd.

## 2. The intersection form `I : H → Z[t^{±1}]`

**Construction.**
- Fix a closed tubular neighbourhood `N ≅ α° × [−1, 1]` of `α°` in `D_n`, with core
  `α° × {0}`. Take `N` closed in `D_n` (a lens with its tips at `p_1`, `p_2`), disjoint from
  `∂D` and from a small disk around every other marked point.
- `π^{-1}(N)` is the disjoint union of the lifts `t^ℓ Ñ`, where `Ñ ⊃ α̃`. `α°` is simply
  connected, so each lift is a homeomorphic copy.
- Each `t^ℓ Ñ` is a component of the closed set `π^{-1}(N)`, hence closed in `D̃`. The family
  is locally finite.
- Define `f_ℓ : D̃ → S^1 = [−1, 1]/(−1 ∼ 1)`:
  - on `t^ℓ Ñ`, `f_ℓ(a, s) = s`;
  - everywhere else, `f_ℓ` is the point `[±1]`.
- `f_ℓ` is continuous. Its two pieces are closed and agree on the frontier
  `t^ℓ(α̃ × {±1})`.
- `f_ℓ(P̃_*) = [±1]`, because `N ∩ ∂D = ∅`. So `f_ℓ` is a map of pairs
  `(D̃, P̃_*) → (S^1, [±1])`.
- Set `I_ℓ := (f_ℓ)_* : H → H_1(S^1, [±1]) = Z`, and `I(x) := Σ_ℓ I_ℓ(x) t^ℓ`.

**Well-defined.** A class `x` is carried by a compact 1-chain. That chain meets only
finitely many `t^ℓ Ñ`, so the sum is finite.

**`Z[t^{±1}]`-linear.** `f_ℓ ∘ t = f_{ℓ−1}`, because `t` carries `t^{ℓ−1} Ñ` onto `t^ℓ Ñ`
preserving the product coordinates. So `I_ℓ(t x) = I_{ℓ−1}(x)` and `I(t x) = t I(x)`.
Additivity is clear.

**Counting formula.** Let `γ̃` be a path in `D̃` with endpoints in `P̃_*`, transverse to
`π^{-1}(α°)`.
- By an isotopy of `D_n` supported near `α°`, which changes `f_ℓ` only by a homotopy of maps
  of pairs, we may assume `γ̃ ∩ t^ℓ Ñ` consists of short segments crossing the product
  transversally.
- `f_ℓ ∘ γ̃` is then a loop in `S^1` whose degree is the signed number of passes through
  `0`.
- So `I_ℓ([γ̃])` is the signed number of crossings of `γ̃` with `t^ℓ α̃`. The sign is the
  orientation sign of the pair (direction of `α`, direction of `γ`), fixed once.

## 3. The loop class of an arc and `(1 − t^s) 𝕄 = I`

Let `A` be an arc from `p_*` to a marked point `p`, transverse to `α`.
- Let `c_A` be the loop at `p_*` that runs along `A` to a small circle around `p`, goes once
  around the circle (counterclockwise), and returns along a parallel push-off of `A`.
- The circle is small enough to miss `α`, and the push-off is thin enough to cross `α` once
  near each `q_i`, with the same local picture.

**Lemma 3.1.** `I([c̃_A]) = (1 − t^s) 𝕄(α, A)`. Here `c̃_A` is the lift of `c_A` from `p̃_*`,
and `t^s` (with `s ∈ {±1}`) is the deck transformation of the counterclockwise small circle.
The sign `s` depends only on the fixed choice of generator `t`.

*Proof.*
- The lift of the first half follows `Ã`. Its crossings contribute `Σ_i ε_i t^{k_i}`.
- The lifted circle ends at `t^s` times its start point, and meets no lift of `α`.
- The return half lifts to a path close to `t^s Ã` traversed backwards. Near `q_i` it crosses
  `t^{k_i + s} α̃` with sign `−ε_i`, contributing `−t^s Σ_i ε_i t^{k_i}`.
- By the counting formula of §2, `I([c̃_A]) = (1 − t^s) Σ_i ε_i t^{k_i}`. ∎

**Corollary 3.2 (invariance).** `𝕄(α, A)` depends only on the homotopy class of `A` through
arcs from `p_*` to `p` with interior in `D_n`. In particular it is independent of the
transverse representative.
- Such a homotopy moves `c_A` by a homotopy rel `p_*`, so `[c̃_A]` is unchanged.
- `1 − t^s ≠ 0` in the domain `Z[t^{±1}]`. ∎

**Remark.** At `t = −1`, `1 − t^s` equals `2`. So `I([c̃_A])(−1) = 2 𝕄(α, A)(−1)`.

## 4. Mapping classes act on `H` through Burau

**4.1 Lifting.** Let `h` be an orientation-preserving homeomorphism of `D` fixing `∂D`
pointwise and `P` setwise.
- `h` permutes the classes of small counterclockwise loops in `H_1(D_n; Z) = Z^n`. `φ` is the
  sum of coordinates there, so `φ ∘ h_* = φ`.
- Hence `h` lifts to a unique `h̃ : D̃ → D̃` with `h̃(p̃_*) = p̃_*`.
- **`h̃` commutes with `t`.** `h̃ ∘ t` and `t ∘ h̃` are both lifts of `h`, so it is enough to
  compare them at `p̃_*`. The lift of a loop `x` with `φ(x) = 1` runs from `p̃_*` to `t p̃_*`.
  `h̃` carries it to the lift of `h ∘ x`, which ends at `t^{φ(h_* x)} p̃_* = t p̃_*`.
- So `h̃_*` is a `Z[t^{±1}]`-linear automorphism of `H`, and `h̃(P̃_*) = P̃_*`.
- An isotopy rel `∂D` lifts to a homotopy of maps of pairs, so `h̃_*` depends only on the
  mapping class. Also `(h ∘ g)~ = h̃ ∘ g̃`.

**4.2 Fox basis.** `π_1(D_n, p_*)` is free on a standard system `x_1, ..., x_n` of loops. Each
`x_j` is a tail from `p_*` plus a small circle around `p_j`, with `φ(x_j) = t`.
- `D_n` deformation retracts, fixing `p_*`, onto a wedge `W` of these circles.
- Lifting gives a homotopy equivalence of pairs `(D̃, P̃_*) ≃ (W̃, W̃^0)`, where `W̃^0 = P̃_*`
  is the vertex set of the cover `W̃`.
- There are no 2-cells, so `H = H_1(W̃, W̃^0) = C_1(W̃)`. This module is free on
  `e_j = [x̃_j]`.
- **Fox formula.** For a loop `γ`, `[γ̃] = Σ_k φ(∂γ/∂x_k) e_k`. This follows from
  `(γδ)~ = γ̃ · t^{φ(γ)} δ̃`, which matches `∂(γδ) = ∂γ + γ ∂δ`.
- Hence `h̃_*(e_j) = Σ_k J_h[j][k] e_k`, with `J_h[j][k] = φ(∂ h_*(x_j) / ∂ x_k)`.
- The chain rule and `φ ∘ h_* = φ` give `J_{h∘g} = J_g J_h`.

**4.3 Artin's formula.** For a suitable standard system, the half-twist `σ_i` acts on
`π_1(D_n, p_*)` by `A_i^{±1}`. The sign is one global convention (the direction of the
half-twist). Here `A_i` is
`x_i ↦ x_i x_{i+1} x_i^{-1}`, `x_{i+1} ↦ x_i`, `x_j ↦ x_j` otherwise.
- This is classical (Artin; see Birman, *Braids, Links, and Mapping Class Groups*, 1974,
  Ch. 1; Kassel–Turaev, *Braid Groups*, GTM 247, 2008, Ch. 1). Exact theorem numbers not
  re-checked in this lane.
- Direct Fox calculus: rows `i, i+1` of `J_{A_i}` are `(1 − t, t)` and `(1, 0)`. So
  `J_{A_i} = ρ_n(σ_i)` and `J_{A_i^{-1}} = ρ_n(σ_i)^{-1}`.
- **Other orientation.** If the Artin formula is stated with the oppositely oriented loops
  `y_j = x_j^{-1}`, the action in the `y`-basis is `ι A_i^{±1} ι`, where `ι : x_j ↦ x_j^{-1}`.
  Its Fox matrix for the character `y_j ↦ t^{-1}` is `J_{A_i^{±1}}` with `t ↦ t^{-1}`.
- **Conclusion.** For a braid word `w`, in some free basis of `H` the matrix of `h̃_{w,*}` is
  `ρ_n(w')`, possibly with `t ↦ t^{-1}`. Here `w'` is one of `w`, `rev w`, `mirror w`,
  `rev mirror w`, depending on the conventions.

**4.4 Convention independence.** Let `D = diag(1, t, ..., t^{n−1})`.
- `ρ_n(σ_i)^T = D ρ_n(σ_i) D^{-1}`. Directly: `[[1−t, 1], [t, 0]] = diag(1, t) [[1−t, t], [1, 0]] diag(1, t^{-1})`.
  Check 2 of the script confirms this for `n = 4`.
- Transposing a product: `ρ_n(w)^T = D ρ_n(rev w) D^{-1}`.
- Using `mirror = rev ∘ inv`: `ρ_n(mirror w) = D^{-1} (ρ_n(w)^{-1})^T D`.

**Lemma 4.1.** Let `𝔞 ⊂ Z[t^{±1}]` be an ideal with `𝔞(t^{-1}) = 𝔞`. If
`ρ_n(Ψ) ≡ I mod 𝔞`, then in every convention `h̃_{Ψ,*}(x) − x ∈ 𝔞H` for all `x ∈ H`.
- The ideals `0` and `(t+1) = (1 + t^{-1})` both qualify.

*Proof.*
- Congruence to `I` mod `𝔞` is preserved by inverse, transpose, and conjugation by the unit
  matrix `D`. By 4.4, it therefore holds for `w'`.
- It is preserved by `t ↦ t^{-1}` because `𝔞` is stable.
- By 4.3 the matrix of `h̃_{Ψ,*}` in some basis of `H` is congruent to `I` mod `𝔞`. ∎

**Direct check for `Φ_0`.** Check 6 of the script computes the Fox Jacobians of the Artin
automorphism of `Φ_0` at `t = −1`. It does so for both twist directions and both composition
orders, without using the identification with `ρ_4`. All four equal `I`.

## 5. Theorem A: Moody's criterion, exactly and modulo an ideal

**Theorem A.** Let `𝔞` be as in Lemma 4.1, `Ψ ∈ B_n` with `ρ_n(Ψ) ≡ I mod 𝔞`, and
`Γ ∈ B_n`. Put `A = (β_*^3)ΨΓ` and `B = (β_*^3)Γ`, with either composition convention.
Then `I([c̃_A]) ≡ I([c̃_B]) mod 𝔞`.

*Proof.*
- Let `h` and `g` realize `Ψ` and `Γ`. Depending on convention, `A = g(h(β_*^3))` or
  `A = h(g(β_*^3))`, and in both cases `B = g(β_*^3)`.
- A homeomorphism `k` maps a small disk around `p_3` to a disk around `k(p_3)` containing no
  other marked point. So `k ∘ c_β` is homotopic rel `p_*` to `c_{k(β)}`.
- `k̃` fixes `p̃_*` and carries lifts from `p̃_*` to lifts from `p̃_*`. Hence
  `[c̃_{k(β)}] = k̃_*[c̃_β]`.
- Write `x = [c̃_β]`. By Lemma 4.1, `h̃_* y − y ∈ 𝔞H` for every `y ∈ H`.
- If `A = g(h(β))`: `[c̃_A] = g̃_* h̃_* x = g̃_* x + g̃_*(h̃_* x − x)`. The correction lies in
  `𝔞H` because `g̃_*` is `Z[t^{±1}]`-linear.
- If `A = h(g(β))`: `[c̃_A] = h̃_*(g̃_* x) = g̃_* x + (h̃_* − 1)(g̃_* x)`, and the correction
  lies in `𝔞H`.
- `I` is linear, so `I(𝔞H) ⊂ 𝔞`. ∎

**Corollary A1 (Moody's criterion).** If `𝕄_{ΨΓ} ≠ 𝕄_Γ` for some `Γ ∈ B_n`, then
`Ψ ∉ ker ρ_n`.

*Proof.* Take `𝔞 = 0`. By Theorem A and Lemma 3.1,
`(1 − t^s) 𝕄_{ΨΓ} = (1 − t^s) 𝕄_Γ` in the domain `Z[t^{±1}]`. ∎

- The statement of the claim uses the right action `(β_*^3)ΨΓ`. Theorem A covers both
  conventions, and `ker ρ_n` is invariant under `rev` and `mirror` (§4.4).
- The unreduced and reduced kernels agree by `burau-kernel-restricts-along-strand-inclusion`.
  The corollary is stated for the unreduced `ρ_n`.

**Corollary A2 (`t = −1`).** If `ρ_n(Ψ) ≡ I mod (t+1)`, then `𝕄_{ΨΓ}(−1) = 𝕄_Γ(−1)` for every
`Γ ∈ B_n`.

*Proof.* Take `𝔞 = (t+1)`. Then `2 𝕄_{ΨΓ}(−1) = I_A(−1) = I_B(−1) = 2 𝕄_Γ(−1)` in `Z`. ∎

## 6. Parity is exactly "no cancellation at `t = −1`"

Let `A` be a transverse representative with crossings `q_1, ..., q_m`, signs `ε_i` and
exponents `k_i` (§1).

**Lemma 6.1 (winding identity; Bigelow 1999, §3; the preprint's Lemma 3.1).**
`k_{i+1} − k_i = ±|P ∩ Δ_i|`.

*Proof.*
- Lift `C_i`, starting at the point `q̃_i` of `t^{k_i} α̃`.
- Along `A[q_i, q_{i+1}]` the lift runs to the lift of `q_{i+1}` on `t^{k_{i+1}} α̃`. Back
  along `α[q_{i+1}, q_i]` it stays on that sheet of `α̃`, ending at `t^{k_{i+1} − k_i} q̃_i`.
- So `φ(C_i) = k_{i+1} − k_i`.
- `C_i` is a simple closed curve missing `P`. The marked points `p_1, p_2` are not on `C_i`,
  because the `α`-piece lies in `α°`. So `φ(C_i) = Σ_j wind(C_i, p_j) = ±|P ∩ int Δ_i|`. ∎

**Lemma 6.2 (parity lemma).** The following are equivalent:
1. `A` satisfies the parity condition;
2. `ε_i (−1)^{k_i}` is independent of `i`;
3. `|𝕄(α, A)(−1)| = m = |A ∩ α|`.

*Proof.*
- By Lemma 6.1, `(−1)^{k_{i+1} − k_i} = (−1)^{|P ∩ Δ_i|}`.
- (1) says exactly `ε_{i+1} ε_i = (−1)^{|P ∩ Δ_i|}` for all `i`.
- (2) says exactly `ε_{i+1} ε_i = (−1)^{k_{i+1} − k_i}` for all `i`. So (1) ⇔ (2).
- `𝕄(α, A)(−1) = Σ_i ε_i (−1)^{k_i}` is a sum of `m` signs. Its absolute value is `m` iff
  all the signs are equal, so (2) ⇔ (3). ∎

**Remark.** Lemma 6.2 contains the preprint's Lemma 4.2 ("parity ⇒ no cancellation", checked
as S5 in part 1 of the 2026-09-13 verification). The equivalence (1) ⇔ (3) shows parity only
controls the value at `t = −1`.

## 7. Theorem B: parity-clean counts see only Burau mod `t+1`

**Theorem B.** Let `n ≥ 3`, `Ψ ∈ B_n` with `ρ_n(Ψ) ≡ I mod (t+1)`, and `Γ ∈ B_n`. Let `A'`
and `B'` be transverse representatives of `A = (β_*^3)ΨΓ` and `B = (β_*^3)Γ` that both
satisfy the parity condition. Then `|A' ∩ α| = |B' ∩ α|`.

*Proof.* By Lemma 6.2, Corollary 3.2 and Corollary A2:
`|A' ∩ α| = |𝕄(α, A)(−1)| = |𝕄_{ΨΓ}(−1)| = |𝕄_Γ(−1)| = |𝕄(α, B)(−1)| = |B' ∩ α|`. ∎

**Contrapositive.** A pair of parity-clean representatives with unequal counts certifies
`ρ_n(Ψ) ≢ I mod (t+1)`. This is strictly more than `Ψ ∉ ker ρ_n`.

## 8. The Brunnian braid `Φ_0`

**Definitions.**
- `A_ij = σ_{j−1} ⋯ σ_{i+1} σ_i^2 σ_{i+1}^{-1} ⋯ σ_{j−1}^{-1}` for `i < j`.
- `[x, y] = x y x^{-1} y^{-1}`.
- `T = (σ_1 σ_2)^6`, `b = [A_14, [A_24, A_34]]`, and `Φ_0 = [T, b] = T b T^{-1} b^{-1}`.

As a word of length 96 (`+i = σ_i`, `−i = σ_i^{-1}`):

```
1 2 1 2 1 2 1 2 1 2 1 2 3 2 1 1 -2 -3 3 2 2 -3 3 3 3 -2 -2 -3 -3 -3 3 2 -1 -1 -2 -3 3 3 3 2 2
-3 -3 -3 3 -2 -2 -3 -2 -1 -2 -1 -2 -1 -2 -1 -2 -1 -2 -1 3 2 2 -3 3 3 3 -2 -2 -3 -3 -3 3 2 1 1
-2 -3 3 3 3 2 2 -3 -3 -3 3 -2 -2 -3 3 2 -1 -1 -2 -3
```

**Proposition 8.1.** `Φ_0 ∈ Brun_4`, `Φ_0 ≠ 1`, `ρ_4(Φ_0) ≠ I`, and `ρ_4(Φ_0) ≡ I mod (t+1)`.

*Proof.*

**(a) `b ∈ Brun_4`.**
- `Brun_4` is the intersection of the kernels of the four strand-forgetting homomorphisms
  `F_j : P_4 → P_3`.
- Deleting strand `i` or strand `j` of `A_ij` gives the trivial braid.
- `F_4` kills `A_14`, `A_24` and `A_34`. `F_3` kills `A_34`, so `[A_24, A_34] ↦ 1`. `F_2` kills
  `A_24`, so `[A_24, A_34] ↦ 1`. `F_1` kills `A_14`.
- In each case the outer commutator has a trivial entry, so `F_j(b) = 1`.

**(b) `Φ_0 ∈ Brun_4`.**
- `Brun_4` is normal in `B_4`: deleting a strand of `y x y^{-1}` gives a conjugate of `x` with a
  strand deleted.
- So `T b T^{-1} ∈ Brun_4`, and `Φ_0 = (T b T^{-1}) b^{-1} ∈ Brun_4`.

**(c) `ρ_4(T) ≡ I mod (t+1)`, by hand.**
- At `t = −1`, `ρ(σ_i)` has block `[[2, −1], [1, 0]]`.
- `σ_1` and `σ_2` act on the first three coordinates and fix `e_4`. Put
  `M = ρ_3(σ_1σ_2)(−1)`:
  - `M = [[2,−1,0],[1,0,0],[0,0,1]] · [[1,0,0],[0,2,−1],[0,1,0]] = [[2,−2,1],[1,0,0],[0,1,0]]`;
  - `M^2 = [[2,−3,2],[2,−2,1],[1,0,0]]`;
  - `M^3 = [[1,−2,2],[2,−3,2],[2,−2,1]]`;
  - `(M^3)^2 = I`.
- So `ρ̄_4(T) = M^6 ⊕ 1 = I`.
- Geometric reading: `T = Δ_3^4 = T_c^2`, the square of the Dehn twist about a curve `c`
  enclosing `p_1, p_2, p_3`, an odd number of points. It is the kind of generator named in the
  Brendle–Margalit–Putman theorem on the kernel at `t = −1` (unverified here, see §10).

**(d) `ρ_4(Φ_0) ≡ I mod (t+1)`.**
- `ρ̄_4` is a homomorphism, so
  `ρ̄_4(Φ_0) = ρ̄_4(T) ρ̄_4(b) ρ̄_4(T)^{-1} ρ̄_4(b)^{-1} = I`.

**(e) `ρ_4(Φ_0) ≠ I`, hence `Φ_0 ≠ 1`.**
- Exact computation over `Z[t^{±1}]` gives `ρ_4(Φ_0) ≠ I` (check 5). The exponents of its
  entries range over `[−14, 14]`.
- `ρ_4` is a homomorphism on `B_4`: the braid relations are checked in check 1, and this is
  also classical.

**Structural backup for `Φ_0 ≠ 1`, not needed above.**
- `A_14`, `A_24`, `A_34` freely generate `ker F_4`, by Artin combing. The basic commutator `b`
  of three distinct free generators is nontrivial.
- By the established claim `brunnian-four-braids-are-pseudo-anosov`, `b` is pseudo-Anosov.
- `[T_c^2, b] = 1` would force `T_{b(c)}^2 = T_c^2`, hence `b(c) = c`. A pseudo-Anosov class
  fixes no essential curve. ∎

**Certificate.** Run with `timeout 600 python3 burau_minus_one.py | tee run.log` in
`experiments/zp-burau-parity-t-minus-one-2026-09-16/`. It uses exact integer Laurent
polynomials and exits `0`.
- check 1: braid relations hold for `ρ_4`;
- check 2: the transpose identity;
- check 3: `ρ_4(T)(−1) = I` and `ρ_4(T) ≠ I`;
- check 4: `b` is Brunnian and nontrivial on the Artin action (a control for (a));
- check 5: `ρ_4(Φ_0) ≠ I`, `ρ_4(Φ_0)(−1) = I`, and `Φ_0` is Brunnian on the Artin action;
- check 6: the four Fox Jacobians at `t = −1` equal `I`, and the automorphisms are nontrivial;
- check 7: the mirror and reversed words also have identity matrix at `t = −1`.

The logged output ends with `ALL CHECKS PASS: True`.

## 9. Refutation of `brunnian-four-braids-admit-parity-correcting-push`

That claim asserts the following. For every nontrivial `Φ ∈ Brun_4` there are `k ≥ 1`,
`y ∈ B_4` and `Γ ∈ K_5` such that, writing `Φ_1 = y Φ^k y^{-1}`,
`A = (β_*^3) f(Φ_1) Γ` and `B = (β_*^3) Γ` have parity-clean transverse representatives with
`|A ∩ α| ≠ |B ∩ α|`.

**Proposition 9.1.** For `Φ = Φ_0` no such `(k, y, Γ)` exists. Indeed, for all `k ≥ 1`,
`y ∈ B_4` and `Γ ∈ B_5` (a fortiori `Γ ∈ K_5`), any parity-clean transverse representatives
of `A` and `B` cross `α` equally often.

*Proof.*
- `ρ̄_4` is a homomorphism. So `ρ̄_4(Φ_1) = ρ̄_4(y) I^k ρ̄_4(y)^{-1} = I` by Proposition 8.1.
- For the standard inclusion `f : B_4 → B_5`, `ρ_5(f(σ_i)) = ρ_4(σ_i) ⊕ 1` for
  `i = 1, 2, 3`. So `ρ_5 ∘ f = ρ_4 ⊕ 1` and `ρ̄_5(f(Φ_1)) = I_5`.
- Apply Theorem B with `n = 5` and `Ψ = f(Φ_1)`. ∎

So `brunnian-four-braids-admit-parity-correcting-push` is false.
- Its route `five-strand-moody-witness-via-parity-correction` is invalid as a proof of the
  witness claim.
- The case `k = 1`, `y = 1` is Proposition 6.4 of arXiv:2607.05283v1, combined with the
  conjugation step of Theorem 6.6, as packaged by that claim. That case fails too.

## 10. Consequences

### 10.1 The preprint

- **v1 (submitted 2026-07-06).** Theorem 6.6 conjugates a nontrivial `Φ ∈ Brun_4` to a proper
  product `Φ'·Γ_1`. Proposition 6.4 then gives `Γ ∈ K_5` such that:
  - `f(Φ'Γ_1)·Γ` is a proper product;
  - both `f(Φ'Γ_1)·Γ` and `Γ` satisfy parity;
  - the geometric intersection numbers with `α` differ.

  By Proposition 5.1 of the preprint (S6 of the 2026-09-13 check), proper products are in
  minimal position. So those parity-clean representatives realize the geometric intersection
  numbers, and the two numbers must be different.
- **Proposition 9.1 rules this out for every conjugate of `Φ_0`.** So for `Φ = Φ_0`, at least one
  of the following fails:
  1. the conjugation step of Theorem 6.6 (every nontrivial Brunnian braid is conjugate to a
     proper product of the required shape);
  2. Proposition 6.4, applied to that conjugate;
  3. Proposition 5.1, in the form used there.
- This lane does not locate the failing step. The natural suspect is gap G1 of the 2026-09-13
  check. There the last step of Proposition 6.4 enlarges `γ_2` to `γ' ∪ γ'' ∪ γ_2` and asserts,
  without proof, both that the intersection number grows and that parity survives.
  - For `Φ_0` the two assertions cannot both hold.
  - Part 2 of the check had already noted this for braids in `ker ρ_4`. The new point is that
    `Φ_0` is an actual Brunnian braid, not a hypothetical kernel element.
- **v2 (2026-09-14).** Status is *preliminary*.
  - The abstract page read on 2026-09-16 lists v2 with the comment "Minor corrections and
    improved exposition", and no withdrawal.
  - The HTML of v2 was read only through the WebFetch summarizer, on 2026-09-16. Its summary:
    - the corresponding statement is Proposition 6.7 (hypothesis: a proper product
      `Φ = Φ'·Γ_1`; conclusion: some `Γ ∈ K_5` makes `f(Φ)·Γ` proper, both it and `Γ` satisfy
      parity, and the intersection numbers differ);
    - the proof again enlarges `γ_2` by `γ' ∪ γ''` and asserts that `ι` increases.
  - If that summary is accurate, the same obstruction applies to v2, verbatim, for every
    conjugate of `Φ_0` that is a proper product. Neither the hypotheses nor the numbering were
    checked against the source.

### 10.2 What parity-clean counts can and cannot see

- **The mechanism can only certify visible non-kernel braids.** By Theorem B, any `Ψ` it certifies
  has `ρ̄_n(Ψ) ≠ I`. At `t = −1` that non-membership is already visible from a single integer
  matrix.
- **For `n = 4`, the hard part of the problem lies elsewhere.** It is the subgroup
  `Brun_4 ∩ ker ρ̄_4`, on which the mechanism is silent:
  - `ker ρ_4 ∩ Brun_4 ⊂ ker ρ̄_4 ∩ Brun_4`;
  - by `burau-four-faithful-iff-faithful-on-brunnian-braids` (established), `ρ_4` is faithful
    iff no nontrivial element of `Brun_4 ∩ ker ρ̄_4` has `ρ_4 = I`.
- **`Brun_4 ∩ ker ρ̄_4` is large.** Let `c` be any simple closed curve in `D_4` surrounding three
  marked points, and `1 ≠ Φ ∈ Brun_4`. Then `Ψ = [T_c^2, Φ]` has these properties:
  - `Ψ` lies in `Brun_4` by normality, since `Ψ = (T_c^2 Φ T_c^{-2}) Φ^{-1}`.
  - `ρ̄_4(Ψ) = I`. `B_4` acts transitively on such curves (classification of surfaces), so
    `T_c^2` is conjugate to `T`, and `ρ̄_4(T) = I` by §8(c).
  - `Ψ ≠ 1`. `Ψ = 1` would give `T_c^2 = T_{Φ(c)}^2`, hence `Φ(c) = c`. But `Φ` is
    pseudo-Anosov (`brunnian-four-braids-are-pseudo-anosov`), so it fixes no essential curve.
- **Beyond `t = −1`.** Any combinatorial proof of faithfulness in this style must extract from
  arcs something that is not determined by `𝕄(−1)`. Candidates:
  - extreme exponents (the span of `𝕄`), controlled by the heights `k_i` of Lemma 6.1;
  - values at other roots of unity;
  - the full sign-and-height sequence modulo moves that preserve `𝕄`.
- **The same limit applies to Bigelow-style counts.** A no-cancellation certificate that
  compares only `Σ |coefficients|` inherits the same `t = −1` blindness.

### 10.3 The witness claim

`brunnian-four-braids-have-five-strand-moody-witness` is untouched: it asks only for
`𝕄_{f(Φ_1)Γ} ≠ 𝕄_Γ`.

- For `Φ_0` and `Γ = 1`, `B = β_*^3` misses `α`, so `𝕄_1 = 0`.
- `experiments/zp-burau-parity-t-minus-one-2026-09-16/moody_gamma_trivial.py` computes the
  candidate values of `(1 − t^s) 𝕄_{f(Φ_0)}`. It uses the standard picture (tails from below,
  counterclockwise loops), in which `I(e_1) = ε`, `I(e_2) = −ε t^{±1}` and `I(e_k) = 0` for
  `k ≥ 3`.
- The computed value is `ε (J[3][1] − t^{±1} J[3][2])`, where `J = ρ_4(w')` (possibly with
  `t ↦ t^{-1}`) and `w'` runs over the four words of §4.3.
- In all 16 variants it is nonzero over `Z[t^{±1}]` and vanishes at `t = −1`. The log ends with
  `ALL VARIANTS NONZERO AND VANISH AT -1: True`.
- So `Γ = 1` is, as expected, a Moody witness for `Φ_0`, but not a parity-clean one. This is
  evidence only: the identification of the standard picture with a system satisfying Artin's
  formula was not re-derived. It is not used by any node.

### 10.4 Context: Brendle–Margalit–Putman

arXiv:1211.4018 (v1 2012-11-16, v4 2014-06-30; Invent. Math. 200 (2015), no. 1, 263–310). Only
the abstract page was read, on 2026-09-16.

- The abstract identifies the kernel of the Burau representation at `t = −1` with the
  hyperelliptic Torelli group, and proves that group is generated by Dehn twists about
  separating curves fixed by the hyperelliptic involution.
- In braid terms these generators are squares of twists about curves surrounding an odd number of
  marked points. That wording is recalled here, not checked against the paper.
- `T = T_c^2` above is such a generator.
- Nothing in §§1–9 depends on this paper.

## 11. Referee checklist

1. **Artin's formula (§4.3)**, that `σ_i` acts on a standard free basis by `A_i^{±1}`. This is the
   only imported input.
   - For `Φ_0` the proof needs the action only at `t = −1`.
   - Check 6 computes the Fox Jacobians at `−1` of both automorphism conventions and both
     composition orders directly.
   - Reversing loop orientation is `t ↦ t^{-1}`, which fixes `−1`.
   - What remains is that the geometric half-twist acts by some `A_i^{±1}` on a free basis of
     loops, each of total winding `±1`.
2. **The form `I` (§2).** Check the continuity of `f_ℓ`, and the isotopy that puts crossings in
   product position.
3. **Lemma 3.1.** Check the sign `−ε_i` and the exponent shift `s` on the return half of `c_A`,
   and that the small circle meets no lift of `α`.
4. **Definitions.** The disk sequence, sign-changing and parity condition of §1 are taken from the
   2026-09-13 check (part 1, S4–S5) and from the statement of the refuted claim. They were not
   re-read from the preprint's tex source in this lane.
   - The refutation is robust to renormalizations `𝕄 ↦ ±t^c 𝕄(t^{±1})`, because only `|𝕄(−1)|`
     enters.
5. **Proposition 9.1.**
   - It uses the standard inclusion, with `ρ_5 ∘ f = ρ_4 ⊕ 1` (S2 of the check, PASS). If the
     preprint used a different embedding, one would recheck `ρ̄_5(f(Φ_0)) = I`.
   - It uses the right action `(β_*^3)ΨΓ`. Theorem A covers both composition orders.
6. **Script.** `rho` multiplies generator matrices in word order, and check 1 validates the braid
   relations. All arithmetic is exact.
7. **v2 content (§10.1)** was seen only through a summarizer and is marked preliminary. The
   refutation of the graph claim does not depend on v2.
