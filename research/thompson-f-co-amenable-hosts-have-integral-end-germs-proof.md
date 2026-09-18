---
rg: 2
id: thompson-f-co-amenable-hosts-have-integral-end-germs-proof
kind: route
title: Farey germs, an end germ dragged by translations, a Shimizu iteration and Carriere-Ghys give a non-hyperfinite relation that the transfer lemma forbids
target: thompson-f-co-amenable-hosts-have-integral-end-germs
requires:
  - co-amenable-subgroups-transfer-hyperfinite-orbit-relations
  - thompson-f-interval-orbit-relation-is-hyperfinite
---

**Imports, verbatim.** Y. Lodha, J. T. Moore, arXiv:1308.4250, TeX `vN_fp.tex`, fetched
2026-09-17.
- l.93–96: `H` consists "of all piecewise projective transformations of the real projective
  line which fix the point at infinity. Monod demonstrated that $H$ does not contain
  nonabelian free subgroups".
- l.132–134: "by an unpublished result of Thurston, $a(t)$ and $b(t)$ generate the subgroup
  $P(\Zbb) \leq H$, consisting of those homeomorphisms which are $C^1$ and piecewise
  $\PSL_2(\Zbb)$". Also l.271–272: "the elements of $F$ correspond exactly to those
  homeomorphisms $f$ of $\Rbb$ which are piecewise $\PSL_2(\Zbb)$ and which have continuous
  derivatives."
- l.136–138: "In fact the methods of \cite{Monod} easily show that $t \mapsto t + 1/2$ and
  $b(t)$ generate a nonamenable group".
- l.304–306 (Carrière–Ghys): "If $\Gamma$ is a countable dense subgroup of $\PSL_2(\Rbb)$,
  then the action of $\Gamma$ on the real projective line induces an orbit equivalence
  relation which is not amenable with respect to Lebesgue measure."
- l.290–294: `E` is `μ`-amenable "if, after discarding a $\mu$-measure $0$ set, $E$ is the
  orbit equivalence relation of an action of $\Zbb$."

Here `a, b` are the maps of the introduction (l.106–122), as in the target claim. Throughout,
`λ` is Lebesgue measure and "hyperfinite" means `λ`-hyperfinite in the sense of the transfer
lemma: hyperfinite after restriction to a Borel set with null complement.

**Lemma D (derivatives at rationals).** Let `δ = [[p,q],[c,d]] ∈ SL_2(Z)` and let `r = u/v` in
lowest terms, `v > 0`, with `cu + dv ≠ 0`. Then `δ(r) = (pu + qv)/(cu + dv)` is in lowest
terms, and `δ'(r) = (cr + d)^{−2} = v²/(cu + dv)²`.

So `δ'(r) = (den r / den δ(r))²` depends only on `r` and `δ(r)`.

*Proof.* A common divisor of `pu + qv` and `cu + dv` divides `u` and `v`, because `δ^{−1}` is
integral. ∎

Consequence: a continuous piecewise-`PSL_2(Z)` map whose breakpoints are rational, and which
sends them to rationals, is automatically `C^1`. The two pieces at a breakpoint have the same
value there, hence the same derivative.

**Lemma P (Farey pieces).** For rationals `r < s` and `r' < s'` there is an increasing
homeomorphism `[r,s] → [r',s']` that is piecewise `PSL_2(Z)` with finitely many rational
breakpoints.

*Proof.*
- *Farey intervals.* A Farey interval is `I = [u/v, u'/v']` with `v, v' > 0` and
  `u'v − uv' = 1`. Put `M_I = [[u', u],[v', v]] ∈ SL_2(Z)`. Then:
  - `M_I(0) = u/v` and `M_I(∞) = u'/v'`;
  - `M_I(1)` is the mediant, which lies inside `I`;
  - the pole `−v/v'` is negative.

  So `M_I` maps `[0,∞]` increasingly onto `I`. For Farey intervals `I, J`, the map
  `M_J M_I^{−1} ∈ PSL_2(Z)` sends `I` increasingly onto `J`.
- *Subdivision.* Let `n` bound the denominators of `r` and `s`. The points of
  `⋃_{k∈Z} (k + F_n)` in `[r,s]` cut it into Farey intervals, where `F_n` is the Farey sequence
  of order `n`:
  - consecutive terms of `F_n` are Farey neighbours (Hardy–Wright, Thm 28);
  - `0/1, 1/1 ∈ F_n`;
  - adding an integer to both terms preserves `u'v − uv'`.
- *Equal numbers of pieces.* The mediant splits a Farey interval into two Farey intervals:
  `(u+u')v − u(v+v') = u'(v+v') − (u+u')v' = u'v − uv' = 1`. So `[r,s]` and `[r',s']` can be
  cut into the same number `m` of Farey intervals `I_1 < … < I_m` and `J_1 < … < J_m`.
- *Gluing.* Define the map to be `M_{J_i} M_{I_i}^{−1}` on `I_i`. Consecutive pieces agree at
  the shared endpoints, which are rational. ∎

**Step 0 (part 1 of the claim: Farey germs).** Let `x ∉ Q` and `γ ∈ PSL_2(Z)`.
- The pole `γ^{−1}(∞)` is rational or `∞`. Choose rationals `p < x < q` with the pole outside
  `[p,q]`. Then `γ` is increasing on `[p,q]`, and `p' = γp` and `q' = γq` are rational.
- Choose integers `N_− < p`, `N'_− < p'`, `N_+ > q` and `N'_+ > q'`. Define `f` to be:
  - `t + (N'_− − N_−)` on `(−∞, N_−]`;
  - a Lemma P map `[N_−, p] → [N'_−, p']`;
  - `γ` on `[p,q]`;
  - a Lemma P map `[q, N_+] → [q', N'_+]`;
  - `t + (N'_+ − N_+)` on `[N_+, ∞)`.
- `f` is an increasing homeomorphism of `R`. It is piecewise `PSL_2(Z)` with finitely many
  rational breakpoints, each sent to a rational, so it is `C^1` by Lemma D.
- As a map of `P^1` it fixes `∞`. By l.132–134, `f ∈ ⟨a,b⟩ = F`, and `f = γ` near `x`.

Conversely, each element of `F` is piecewise `PSL_2(Z)`, so `Fx ⊆ PSL_2(Z)x` for every `x`.
Hence `F`-orbits and `PSL_2(Z)`-orbits agree on `R \ Q`, which is part 1.

**Lemma C (countable reduction).** Let `L ≤ G` be co-amenable with `L` countable, and let
`C ⊆ G` be countable. Then some countable `G'` with `L ∪ C ⊆ G' ≤ G` contains `L`
co-amenably.

*Proof.* Write `X = G/L` and `(kφ)(x) = φ(k^{−1}x)` for `φ ∈ ℓ^1(X)`.
- *Reiter vectors.* Let `m` be a `G`-invariant mean on `X`. Fix a finite `K ⊆ G` and
  `ε > 0`.
  - Probability vectors are weak*-dense in the means (Goldstine). Take a net `φ_i → m`.
  - Then `kφ_i − φ_i → 0` weakly in `ℓ^1(X)` for each `k ∈ K`, since
    `⟨kφ_i − φ_i, f⟩ → m(k^{−1}·f) − m(f) = 0` for `f ∈ ℓ^∞(X)`.
  - So `0` lies in the weak closure of the convex set
    `{(kφ − φ)_{k∈K} : φ ∈ Prob(X)} ⊆ ℓ^1(X)^K`. By Mazur, it lies in the norm closure.
  - Hence there is `φ_{K,ε} ∈ Prob(X)` with `‖kφ_{K,ε} − φ_{K,ε}‖_1 < ε` for all `k ∈ K`, and
    it has countable support.
- *Closing up.* Put `G_0 = ⟨L ∪ C⟩`. Given countable `G_j`, let `G_{j+1}` be generated by
  `G_j` together with one representative of every coset in the support of `φ_{K,1/n}`, over
  all finite `K ⊆ G_j` and all `n ≥ 1`. Each `G_j` is countable, and so is
  `G' = ⋃_j G_j`.
- *Invariant mean.* Since `L ≤ G'`, the map `g'L ↦ g'L` embeds `G'/L` into `G/L` as a
  `G'`-set. For finite `K ⊆ G'` and each `n`, the vector `φ_{K,1/n}` is supported in `G'/L`,
  hence so are the `kφ_{K,1/n}`, and the norms are unchanged. A weak* cluster point of these
  vectors, taken along finite `K ↑ G'` with `n → ∞`, is a `G'`-invariant mean on `G'/L`,
  because `|M(k·f) − M(f)| ≤ lim ‖kφ − φ‖_1 ‖f‖_∞ = 0`. ∎

**Step 1 (an end germ drags to a global map).** Let `G ≥ ⟨a⟩` and `g ∈ G` with `g = s` on
`[R, ∞)`, where `s(t) = αt + β` and `α > 0`. Then `s(y) ∈ Gy` and `s^{−1}(y) ∈ Gy` for every
`y ∈ R`, and `y ± α ∈ Gy`.

*Proof.*
- `g` maps `[R,∞)` onto `[s(R),∞)`. So for `w ≥ s(R)` we have `g^{−1}w = s^{−1}w ≥ R` and
  `s^{−1}w + 1 ≥ R`.
- Hence `h = g a g^{−1}` satisfies `h(w) = s(s^{−1}w + 1) = w + α` on `[s(R), ∞)`.
- For `z ∈ R`, choose `k ∈ N` with `z + k ≥ s(R)`. Then `a^{−k} h a^k (z) = z + α`, so
  `z + α ∈ Gz` for all `z`, and therefore `z − α ∈ Gz` as well.
- For `y ∈ R`, choose `n ∈ N` with `y + n ≥ R`. Then `g a^n (y) = s(y + n) = s(y) + αn` lies
  in `Gy`. Subtracting `α` a total of `n` times, `s(y) ∈ Gy`.
- Applying this to `z = s^{−1}(y)` gives `y ∈ G s^{−1}(y)`, so `s^{−1}(y) ∈ Gy`.

The half-line `(−∞, R]` is identical with `n → −∞`:
- `h = g a g^{−1}` is `w + α` on `(−∞, s(R − 1)]`;
- conjugate by `a^{−k}` to reach every `z`;
- use `g a^{−n}(y) = s(y) − αn`. ∎

**Step 2 (the relation of `Λ` sits inside that of `G`).** Let `G` satisfy the hypotheses of
part 2, and let `Λ = ⟨PSL_2(Z), s⟩ ≤ PSL_2(R)`. Here `s` is the matrix
`[[√α, β/√α],[0, 1/√α]]`.
- Put `Y = P^1 \ Λ·(Q ∪ {∞})`. It is `Λ`-invariant, it lies in `R \ Q`, and its complement is
  countable, so it is conull.
- Let `x ∈ Y` and `μ = μ_1 ⋯ μ_n` with each `μ_i ∈ PSL_2(Z) ∪ {s^{±1}}`. Put
  `x_i = μ_{i+1} ⋯ μ_n x ∈ Y` and `x_n = x`.
- Then `μ_i x_i ∈ G x_i`: by Step 0 when `μ_i ∈ PSL_2(Z)`, since `x_i` is irrational, and by
  Step 1 when `μ_i = s^{±1}`.
- By induction, `Λx ⊆ Gx` for every `x ∈ Y`.

**Step 3 (`Λ` is dense).**
- *A short translation.* `Λ` contains a translation `τ_h(t) = t + h` with `0 < h < 1`.
  - If `α = 1`, then `β ∉ Z`. Take `h = β − ⌊β⌋`, using `τ_β = s` and `τ_1 ∈ PSL_2(Z)`.
  - If `α ≠ 1`, then `s τ_1 s^{−1} = τ_α`, so `τ_{α^n} ∈ Λ` for all `n ∈ Z`. Take `h = α^n`
    for a suitable `n`.
- *Non-discrete (Shimizu iteration).* For `ξ = [[p,q],[c,d]] ∈ SL_2(R)`, direct multiplication
  gives
  `ξ τ_h ξ^{−1} = [[1 − hpc, hp²],[−hc², 1 + hpc]]`.
  - Start from `ξ_0 = [[0,−1],[1,0]] ∈ PSL_2(Z)` and put `ξ_{j+1} = ξ_j τ_h ξ_j^{−1} ∈ Λ`.
  - Then `c_j = −h^{2^j − 1}` for `j ≥ 1`. It is nonzero, strictly decreasing in absolute
    value, and tends to `0`.
  - `|p_{j+1} − 1| = h |p_j| |c_j|`, so `p_j → 1`. Hence `ξ_j → [[1,h],[0,1]] = τ_h`.
  - The `ξ_j` are pairwise distinct, because the `|c_j|` are distinct. So `Λ` is not
    discrete.
- *Dense.*
  - The closure `Λ̄` is a closed subgroup of `PSL_2(R)`, hence a Lie subgroup (Cartan). It is
    non-discrete, so its Lie algebra `𝔥` is nonzero.
  - `𝔥` is `Ad(Λ̄)`-invariant. In particular it is invariant under `Ad(U^n)`, where
    `U = exp(e)` and `e = [[0,1],[0,0]]`.
  - Since `(ad e)^3 = 0` on `sl_2`, we have `Ad(U^n) v = v + n[e,v] + (n²/2)[e,[e,v]]`. From
    `n = 0, 1, 2` and `v ∈ 𝔥` one solves for `[e,v] ∈ 𝔥`.
  - Likewise `[f,𝔥] ⊆ 𝔥` for `f = [[0,0],[1,0]]`, using `[[1,0],[1,1]] ∈ PSL_2(Z)`.
  - `e` and `f` generate `sl_2(R)` as a Lie algebra, so `𝔥` is an ideal. By simplicity
    `𝔥 = sl_2(R)`, and `Λ̄ = PSL_2(R)`.
  - This matches the principle Lodha–Moore quote at l.331–332: "Since $K$ contains
    $\PSL_2(\Zbb)$ as a proper subgroup, it is dense".
- `Λ` is countable. By Carrière–Ghys (l.304–306), `R_Λ` on `P^1` is not `λ`-amenable.

**Step A (the relation of `F` on the line is hyperfinite).** This is the heretic's Step A in
`thompson-f-not-co-amenable-in-known-hosts-proof`, repeated here so the route is
self-contained.
- *Φ is almost a bijection.* Lodha–Moore define `Φ : 2^N → R ∪ {∞}` (l.245–253). It "is
  one-to-one except at $\xi$ which are eventually constant", and two-to-one there
  (l.263–266).
- *Φ conjugates `⟨a,b⟩` to `F`.* By l.269–270, Φ conjugates `⟨a,b⟩` to the prefix-replacement
  group `F` on `2^N` (l.212–213). The binary-value map `β(ξ) = Σ ξ_i 2^{−i}` intertwines prefix
  replacement with dyadic piecewise-linear maps of `[0,1]`.
- *The Borel conjugacy.* Let `C` be the countable set of `Φ`-images of eventually constant
  sequences. Then `β ∘ Φ^{−1} : R \ C → (0,1) \ Z[1/2]` is a Borel bijection conjugating
  `⟨a,b⟩` to dyadic `F`.
- *Pushing λ forward.* `⟨a,b⟩` is piecewise Möbius with finitely many pieces, so `λ` is
  quasi-invariant. Its push-forward is an `F`-quasi-invariant σ-finite measure on `(0,1)`.
- *Conclusion.* By `thompson-f-interval-orbit-relation-is-hyperfinite`, part 2, that relation
  is hyperfinite. Transport back and discard `C`: `R_F` is `λ`-hyperfinite on `R`.

Hyperfiniteness passes to subrelations on the same set. If `E|_A = ⋃ E_i` with finite Borel
`E_i`, and `E' ⊆ E` is a Borel equivalence relation, then `E'|_A = ⋃ (E_i ∩ E')`. So `R_L` is
`λ`-hyperfinite for every `L ≤ F`.

**Step 4 (part 2 of the claim).** Let `G` be as in part 2, and suppose some countable
`L ≤ G` with `λ`-hyperfinite `R_L` is co-amenable in `G`.
1. *Countable host.* Lemma C with `C = F ∪ {g}` gives a countable `G'` with
   `L ∪ F ∪ {g} ⊆ G' ≤ G` and `L` co-amenable in `G'`.
2. *Hypotheses of the transfer lemma.* `G'` acts on the standard Borel space `R` by
   homeomorphisms, which are Borel automorphisms. Its elements preserve `λ`-null sets.
3. *Transfer.* By `co-amenable-subgroups-transfer-hyperfinite-orbit-relations`, `R_{G'}` is
   `λ`-hyperfinite: `R_{G'}|_A` is hyperfinite for some Borel `A` with null complement.
4. *Descend to Λ.* Steps 0–2 apply to `G'`, since it contains `a`, `b` and `g`. So
   `Λx ⊆ G'x` for `x ∈ Y`, and `R_Λ|_{A∩Y} ⊆ R_{G'}|_A` is a Borel subrelation. It is
   therefore hyperfinite, and `A ∩ Y` has null complement in `P^1`.
5. *Contradiction.* A `λ`-hyperfinite relation is `λ`-amenable in the Lodha–Moore sense
   (l.290–294, Connes–Feldman–Weiss; see the trust surface). This contradicts Step 3. ∎

The special cases follow directly:
- `L ≤ F` has hyperfinite relation by Step A.
- `L = 1` shows `G` is non-amenable, since `1` is co-amenable exactly when `G` is amenable.
- For `⟨t + 1/2, b⟩`: it contains `a = (t+1/2)^2`, `b` and `g = s = t + 1/2`. Its generators
  are piecewise projective and fix `∞`, so it lies in `H`, which has no free subgroups by
  l.96.

**Part 3 (end germs in `H`).** Let `g ∈ H`. The piece of `g` on an interval of `P^1` with
endpoint `∞` (or containing `∞`) is some `μ ∈ PSL_2(R)` with `μ(∞) = g(∞) = ∞`. So `μ` is
affine, `t ↦ αt + β`, with `α > 0` because `g` is increasing on `R`. Hence `g` agrees with an
affine map on a half-line at each end.
- Elements of `H` have finitely many Möbius pieces, so they preserve `λ`-null sets.
- If `F ≤ G ≤ H` and some germ `∂_±(g)` is not an integer translation, part 2 applies.
- For `H(A)` with `A ≠ Z` a ring and `x ∈ A \ Z`: `τ_x = [[1,x],[0,1]] ∈ PSL_2(A)` is
  global, fixes `∞`, and has no finite breakpoints, so `τ_x ∈ H(A)`. ∎

**Trust surface.**
- *Imported claims.* The transfer lemma, and the hyperfiniteness of `F`'s interval relation
  (with its Zimmer and Connes–Feldman–Weiss imports).
- *Verbatim imports.* Lodha–Moore, as quoted above, covering:
  - Thurston's identification `⟨a,b⟩ = P(Z)`, the `C^1` piecewise-`PSL_2(Z)` homeomorphisms;
  - `Φ`;
  - Carrière–Ghys.
- *Textbook facts used without re-reading:*
  - Hardy–Wright Thm 28 on Farey sequences;
  - Cartan's closed-subgroup theorem;
  - simplicity of `sl_2(R)`;
  - Goldstine and Mazur.
- *Implicit assumption.* "Piecewise" in l.132–134 means finitely many pieces. The map built in
  Step 0 has finitely many pieces, so it qualifies under either reading.
- *Amenability definitions.* "`λ`-hyperfinite ⇒ `λ`-amenable" in the Lodha–Moore sense is used
  exactly as in the heretic route: the Connes–Feldman–Weiss equivalence and the standard fact
  that a hyperfinite relation is generated by one Borel automorphism.
- *What is not used.* Neither Zimmer's theorem for `G` nor Monod's no-free-subgroups theorem
  is needed for part 2. The latter is used only to note that `⟨t + 1/2, b⟩` has no free
  subgroups.
