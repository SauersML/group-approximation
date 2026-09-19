---
rg: 2
id: cover-pair-failures-have-finite-partial-table-witnesses-proof
kind: route
title: Reduce strong post-surjectivity to one single-site lift on a finite window, replace global admissibility by admissibility on one compactness set, and transport everything along a partial embedding
target: cover-pair-failures-have-finite-partial-table-witnesses
requires:
  - universal-all-group-subgroup-colimit-class-tester
  - gottschalk-surjunctivity-fixed-two-generator-tester
  - residually-finite-groups-are-lef
---

**Conventions.** `G` acts on `A^G` by `(gx)(h) = x(g^-1 h)`.
- `X` is given by a finite window `W ∋ 1` and a set `𝒜 ⊆ A^W` of allowed patterns:
  `x ∈ X` iff for every `g ∈ G` the pattern `w ↦ x(gw)` lies in `𝒜`. This is called *the window of `x` at `g`*.
- `F(x)(h) = μ(m ↦ x(hm))` for a finite memory `M ∋ 1` and a rule `μ : A^M → A`, extended arbitrarily off the
  patterns that occur.
- For finite `S, T ⊆ G`, `ST = {st}` and `S^-1 = {s^-1}`. Enlarging `Φ` preserves the lift condition, so
  assume `1 ∈ Φ`.

## Step 1. Single-site lifts

**Lemma 1.** A pair `(X, F)` is strongly post-surjective with constant `Φ`, lifts in `X`, iff the following holds.

> **(S)** For every `x ∈ X` and `b ∈ A` there is `x' ∈ X` that agrees with `x` off `Φ`, has `F(x')(1) = b`, and
> has `F(x')(h) = F(x)(h)` for all `h ≠ 1`.

*Proof.* (⇒) Take `z` equal to `F(x)` except `z(1) = b`. Then `Δ(F(x), z) ⊆ {1}`, so the lift satisfies
`Δ(x, x') ⊆ Φ`.

(⇐)
- By equivariance, (S) holds at every site `g`, with `Φ` replaced by `gΦ`: apply (S) to `g^-1 x` and translate
  back.
- Let `z ~ F(x)` and list `Δ(F(x), z) = {d_1, …, d_k}`.
- Put `x_0 = x`. Let `x_i` be the single-site lift of `x_{i-1}` at `d_i` that writes `z(d_i)` there.
- Then `F(x_i)` agrees with `z` on `d_1, …, d_i` and with `F(x)` elsewhere, and `x_i ∈ X`.
- Also `Δ(x, x_k) ⊆ ∪ d_iΦ = Δ(F(x), z)Φ`, so `x_k ~ x` and `F(x_k) = z`. ∎

**Finite form of (S).** Put `N = Φ ∪ ΦW^-1W ∪ ΦM^-1M`, a finite set containing `Φ`. For a pattern `p` on `N` and
`u ∈ A^Φ`, let `p_u` be `p` with its restriction to `Φ` replaced by `u`. Say that `u` *lifts `p` to `b`* if:
- **(α)** for every `g ∈ ΦW^-1` the pattern `w ↦ p_u(gw)` lies in `𝒜` (note `gW ⊆ N`);
- **(β)** for every `h ∈ ΦM^-1` (note `hM ⊆ N`), `μ(m ↦ p_u(hm))` equals `μ(m ↦ p(hm))` if `h ≠ 1`, and equals `b`
  if `h = 1`.

Call `p` *admissible* if `p = x|_N` for some `x ∈ X`.

**Lemma 2.** (S) holds iff every admissible `p` on `N` and every `b ∈ A` has some `u ∈ A^Φ` lifting `p` to `b`.

*Proof.*
- A window of `x'` that meets `Φ` is at some `g ∈ ΦW^-1`.
- An output `F(x')(h)` can differ from `F(x)(h)` only if `hM` meets `Φ`, i.e. only if `h ∈ ΦM^-1`.
- So for `x'` equal to `x` off `Φ`, with `x'|_Φ = u` and `p = x|_N`:
  - `x' ∈ X` iff (α) holds, because the windows that miss `Φ` are windows of `x`;
  - `x'` has the outputs required by (S) iff (β) holds. ∎

## Step 2. Compactness

Let `L ⊆ G` be finite with `N ⊆ L`. Call a pattern `p` on `N` *`L`-admissible* if it extends to a pattern `q`
on `L` such that, for every `g ∈ L` with `gW ⊆ L`, the pattern `w ↦ q(gw)` lies in `𝒜`. Admissible implies
`L`-admissible, for every `L`.

**Lemma 3.** There is a finite `L ⊇ N` such that every `L`-admissible pattern on `N` is admissible.

*Proof.*
- Fix a pattern `p` on `N` that is not admissible.
- For finite `L ⊇ N`, let `C_L ⊆ A^G` be the set of configurations that extend `p` and whose windows at all
  `g ∈ L` with `gW ⊆ L` are allowed. Each `C_L` is closed, and `C_L ⊆ C_{L'}` when `L ⊇ L'`.
- If every `C_L` were nonempty, then by compactness of `A^G` (Tychonoff) some `y` would lie in all of them.
- Every window `gW` lies in some finite `L ⊇ N ∪ gW`, so `y ∈ X` and `p = y|_N` would be admissible. This is a
  contradiction.
- So some `C_{L_p}` is empty, which means `p` is not `L_p`-admissible.
- Let `L` be the union of the `L_p` over the finitely many non-admissible `p`. If `p` is `L`-admissible, then
  restricting its extension to `L_p` shows that `p` is `L_p`-admissible. ∎

No countability of `G` is used.

## Step 3. Transport along a partial embedding (Theorem L for CP)

Let `(X, F)` be a cover pair over `G` with `X ≠ A^G` and `c^G ∈ X`. Take `N` from Step 1 and `L` from Lemma 3, and
put

`K = {1} ∪ L ∪ LW ∪ W ∪ M ∪ Φ ∪ ΦW^-1 ∪ ΦM^-1` (so `N ⊆ L ⊆ K`).

Let `ψ : K → G'` be a partial embedding. Then `ψ(1) = 1`, because `ψ(1) = ψ(1·1) = ψ(1)^2`.

**The transported pair.**
- `X' ⊆ A^{G'}` has window `W' = ψ(W)` and allowed set `𝒜' = {a ∘ ψ^-1 : a ∈ 𝒜}`.
- `F'(x)(h') = μ(m ↦ x(h'ψ(m)))`.
- The lift constant is `Φ' = ψ(Φ)`.
- `ψ` is injective, so these sets have the same sizes as `W, M, Φ`.

**Three facts about products.** Each one uses only products `a·b = c` with `a, b, c ∈ K`, which `ψ` preserves.
1. For `g ∈ L` and `w ∈ W` we have `gw ∈ LW ⊆ K`, so `ψ(g)ψ(w) = ψ(gw)`.
2. If `g' ψ(w) = ψ(φ)` with `w ∈ W` and `φ ∈ Φ`, then `g = φw^-1 ∈ K` satisfies `ψ(g)ψ(w) = ψ(φ)`. So
   `g' = ψ(g)` with `g ∈ ΦW^-1`. Likewise, `h'ψ(m) = ψ(φ)` forces `h' = ψ(h)` with `h = φm^-1 ∈ ΦM^-1`.
3. For `g ∈ ΦW^-1 ⊆ L` and `w ∈ W`, `ψ(g)ψ(w) = ψ(gw)` by fact 1, and `gw ∈ N`. For `h ∈ ΦM^-1` and `m ∈ M`,
   `hm ∈ N ⊆ K`, so `ψ(h)ψ(m) = ψ(hm)`.

**Proper, with a constant.**
- `X ≠ A^G` forces `𝒜 ≠ A^W`, since otherwise every configuration would be in `X`. So `𝒜' ≠ A^{W'}`, and any
  configuration carrying a forbidden pattern on `W'` lies outside `X'`. Hence `X' ≠ A^{G'}`.
- The constant pattern `c^W` is allowed, since `c^G ∈ X`. So `c^{G'} ∈ X'`.
- More generally, `d^{G'} ∈ X'` iff `d^W ∈ 𝒜` iff `d^G ∈ X`, so the constants of `X` and `X'` correspond.

**Lemma 4.** `(X', F')` satisfies (S) at `1 ∈ G'` with the set `Φ'`.

*Proof.*
- Let `x ∈ X'` and `b ∈ A`. Put `p = x ∘ ψ|_N` and `q = x ∘ ψ|_L`.
- For `g ∈ L` with `gW ⊆ L`, fact 1 gives `q(gw) = x(ψ(g)ψ(w))`. This is the window of `x` at `ψ(g)`,
  transported, so it is allowed. Hence `p` is `L`-admissible in `G`, so admissible by Lemma 3.
- By Lemmas 1 and 2 applied in `G`, some `u ∈ A^Φ` lifts `p` to `b`.
- Define `x'` equal to `x` off `ψ(Φ)`, with `x'(ψ(φ)) = u(φ)`. By injectivity, `x' ∘ ψ|_N = p_u`.
- *`x' ∈ X'`.* A window of `x'` that meets `ψ(Φ)` sits at `g' = ψ(g)` with `g ∈ ΦW^-1` (fact 2). By fact 3 it
  reads `w ↦ p_u(gw)`, which is allowed by (α). Every other window of `x'` is a window of `x`.
- *Outputs.* `F'(x')(h')` can differ from `F'(x)(h')` only if `h'ψ(M)` meets `ψ(Φ)`. Then `h' = ψ(h)` with
  `h ∈ ΦM^-1` (fact 2). By fact 3, `F'(x')(ψ(h)) = μ(m ↦ p_u(hm))` and `F'(x)(ψ(h)) = μ(m ↦ p(hm))`. By (β)
  these agree for `h ≠ 1`, and the first equals `b` for `h = 1`. Since `ψ` is injective and `ψ(1) = 1`, the
  site `h' = 1` corresponds exactly to `h = 1`. ∎

By Lemma 1 in `G'`, `F'` is strongly post-surjective with constant `Φ'` and lifts in `X'`. So `CP(G')` fails. This
proves Theorem L for `CP`.

## Step 4. `CP_col` and `NPE`

**`CP_col`.** Suppose the pair of Step 3 also collides at every constant `d^G ∈ X`.
- For each such `d`, fix colliding `x_d ≠ y_d` and a finite `E_d ⊇ Δ(x_d, d^G) ∪ Δ(y_d, d^G)`.
- Enlarge `K` by `E_d ∪ E_dW^-1 ∪ E_dW^-1W ∪ E_dM^-1 ∪ E_dM^-1M` for every constant `d`. There are at most `|A|`
  of them.
- In `G'`, let `x'_d` equal `d` off `ψ(E_d)`, with `x'_d ∘ ψ = x_d` on `E_d`. Define `y'_d` in the same way.
- As in Lemma 4, a window of `x'_d` that meets `ψ(E_d)` sits at `ψ(g)` with `g ∈ E_dW^-1`, and it reads the
  window of `x_d` at `g`, so it is allowed. The other windows are constant `d`. So `x'_d, y'_d ∈ X'`.
- `F'(x'_d)` and `F'(y'_d)` can differ only at `ψ(h)` with `h ∈ E_dM^-1`. There they read the patterns
  `m ↦ x_d(hm)` and `m ↦ y_d(hm)`, and `F(x_d) = F(y_d)` gives equal outputs. So the two images are equal.
- `x'_d ≠ y'_d` by injectivity of `ψ`.
- By the correspondence of constants, `(X', F')` collides at every constant of `X'`. So `CP_col(G')` fails.

**`NPE`.** The same argument applies to `X = A^G` with output alphabet `B`, `|B| > |A|`.
- Here `𝒜 = A^W` with `W = {1}`, and every pattern is admissible, so Lemma 3 is not needed.
- Lemma 4 goes through word for word, with `b ∈ B`.

## Step 5. Corollaries

Let `P` be `CP`, `CP_col` or `NPE`, and let `K` be a witness set from Theorem L.

**1. Local and hereditary.**
- If `P` fails at `G`, the inclusion `K → ⟨K⟩` is a partial embedding, so `P` fails at the finitely generated
  group `⟨K⟩`.
- If `P` fails at `H ≤ G` with witness set `K ⊆ H`, the inclusion `K → G` is a partial embedding, so `P` fails
  at `G`.

**2. Closure properties.**
- *Local embeddability.* Let `G` be locally embeddable into a class `C`: every finite subset of `G` has a partial
  embedding into some member of `C`. If `P` fails at `G`, apply this to `K`, and `P` fails at a member of `C`.
- *Directed colimits.* Let `G = colim G_i` with arbitrary structure maps `f_i : G_i → G`. Each `k ∈ K` is
  `f_i(k_i)` for some `i` and `k_i`.
  - There are finitely many triples `a, b, ab ∈ K`. Each relation `k_a k_b = k_{ab}` holds in `G`, so it holds
    after pushing to some later stage `j` common to all of them.
  - Distinct elements of `K` stay distinct at every stage, because their images in `G` are distinct.
  - So `k ↦ (k_i pushed to G_j)` is a partial embedding of `K` into `G_j`, and `P` fails at `G_j`.
- *Marked limits.* Let `(G_n, s_n) → (G, s)`, with `K` inside the `r`-ball of `(G, s)`.
  - Choose a word of length at most `r` for each element of the ball.
  - Let `n` be large enough that words of length at most `3r` define the same trivial words in `G_n` as in `G`.
  - Send each element of the ball to the value of its word in `G_n`. This map is well defined and injective.
  - It is multiplicative on the ball: if `a = u`, `b = v` and `ab = w` in `G`, then `uvw^-1` is trivial in `G`,
    so it is trivial in `G_n`.
  - So `P` fails at `G_n` for all large `n`. Failure is open, and the marked groups satisfying `P` form a closed
    set.

**3. Finitely presented witnesses.** A finitely generated `H = F_n / R` is the directed colimit, with surjective
structure maps, of the finitely presented groups `F_n / ⟨⟨w_1, …, w_m⟩⟩` for an enumeration of `R`. If `P` fails
at some group, it fails at a finitely generated `H` by Corollary 1, hence at one of these finitely presented
groups by the colimit case of Corollary 2.

**4. One fixed tester.** By Corollaries 1 and 2, the class of groups satisfying `P` is closed under subgroups and
under directed colimits with arbitrary structure maps.
- `universal-all-group-subgroup-colimit-class-tester` then gives: `P` holds for all groups iff `P(U)` holds.
- `gottschalk-surjunctivity-fixed-two-generator-tester` gives the same statement for Gottschalk with the same
  `U`.
- The w15 split `CP ⟺ Gottschalk ∧ CP_col` holds group by group. So CP for all groups is equivalent to
  `Gottschalk(U) ∧ CP_col(U)`.

**5. Finite and LEF groups.**
- *Finite `G`.* Let `X ⊊ A^G` contain a constant, and suppose `F : X → A^G` is strongly post-surjective with lifts
  in `X`. Every `z ∈ A^G` is asymptotic to `F(x)` for any `x ∈ X`, because `G` is finite. So `z` has a lift, and
  `F` is onto. This is impossible, since `|X| < |A^G|`.
- The same counting refutes a strongly post-surjective automaton `A^G → B^G` with `|B| > |A|`.
- `CP` implies `CP_col`, since a colliding pair is in particular a pair.
- So finite groups satisfy all three. By Corollary 2, so does every LEF group, and by
  `residually-finite-groups-are-lef`, every residually finite group. ∎
