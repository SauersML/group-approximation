# Coset lifts are fixed points of tube shifts (2026-09-20)

Agent `swarm-0917-w21-w21-gs-last1`, wave swarm-0917. Target:
`constant-point-sft-domains-admit-no-post-surjective-covers` (CP), residual step of Corollary S4 of
`research/artifacts/symmetric-locus-seeds-2026-09-18.md` (bus need 06d50d0e, the `⟨e⟩`-coset lift).

## 0. Setting and imports

Notation is that of `research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md`, Sections 0–1
(the artifact of the ESTABLISHED claim `post-surjective-sft-covers-admit-scheduled-sections`).
- `(X, F)` is a cover pair: `X ⊊ A^G` an SFT with window `W ∋ 1` and allowed set `Adm`; `F` an automaton with
  memory `M ∋ 1`; `F` strongly post-surjective with lifts in `X` with constant `Φ ∋ 1`.
- The shift is `(g.x)(h) = x(g^-1 h)`. So `e.x = x` means `x(e^j u) = x(u)` for all `j ∈ Z`, `u ∈ G`.
- `N`, `E` and `k` are as there.

The only imported step is Lemma 1 of that artifact, quoted verbatim:

> **Lemma 1.** `Q(x, a)` is nonempty, `L_1(x, a) ∈ X`, `F(L_1(x, a)) = F(x)` off `{1}`, and
> `F(L_1(x,a))(1) = a`. Whether `p ∈ Q(x, a)` depends only on `p`, `a` and `x|_N`.

`L_1(x,a)` agrees with `x` off `Φ`, by its definition in Section 1 there. Its translate is
`L_g(x, a) = g . L_1(g^-1 . x, a)`. This lies in `X`, agrees with `x` off `gΦ`, has output `a` at `g`, and leaves
the output unchanged off `{g}`.

Throughout, the following objects are fixed:
- `e ∈ E \ {1}`;
- `z ∈ Fix(e)`, with `a = z(1)`, so that `z(e^j) = a` for all `j`;
- `x ∈ X ∩ Fix(e)`. For a seed `ξ`, `x = ξ(z)` is such a point, because `ξ` is equivariant.

By Corollary S4, a seed is exact at `1` on `Fix(e)` only if `F(ξ(z))(e^j) = a` for all `j`, with `ξ(z) ∈ Fix(e)`.
A **tube repair** of `x` replaces it by a point that differs from `x` only on a set `⟨e⟩K`, where `K` is finite.

## 1. The tube shift

Let `K ⊇ Φ` be finite. Put `T_K = ⟨e⟩K`, and define

    Σ_K(x, a) = { y ∈ X :  y = x off T_K,
                           F(y)(e^j) = a for all j ∈ Z,
                           F(y)(h) = F(x)(h) for all h ∉ ⟨e⟩ }.

**Proposition T1 (nonempty).** `Σ_Φ(x, a) ≠ ∅`, so `Σ_K(x, a) ≠ ∅` for all `K ⊇ Φ`.

*Proof.* Enumerate `Z` as `j_1 = 0, 1, -1, 2, -2, ...`, or list the finite group `⟨e⟩` if `e` has finite order.
Put `y_0 = x` and `y_n = L_{e^{j_n}}(y_{n-1}, a)`. Lemma 1, translated, gives three facts for each `n`:
- `y_n ∈ X`;
- `y_n = y_{n-1}` off `e^{j_n}Φ ⊆ T_Φ`;
- `F(y_n) = F(y_{n-1})` off `{e^{j_n}}`, and `F(y_n)(e^{j_n}) = a`.

By induction, `y_n = x` off `T_Φ`, `F(y_n)(e^{j_m}) = a` for `m ≤ n`, and `F(y_n)(h) = F(x)(h)` for `h ∉ ⟨e⟩`.
Take a convergent subsequence `y_{n_i} → y`, using compactness of `A^G`.
- `y ∈ X`, because `X` is closed.
- `y = x` off `T_Φ`.
- Each value `F(·)(h)` depends on finitely many coordinates, so `F(y)(h) = F(y_{n_i})(h)` for `i` large. Hence
  `y ∈ Σ_Φ(x, a)`. `∎`

**Proposition T2 (the `e`-action).** `e . Σ_K(x, a) = Σ_K(x, a)`. The `e`-invariant tube repairs are exactly
`Σ_K(x, a) ∩ Fix(e)`.

*Proof.* Let `y ∈ Σ_K`. Then:
- `e.y ∈ X`.
- `e.y = e.x = x` off `eT_K = T_K`.
- `F(e.y)(e^j) = F(y)(e^{j-1}) = a`.
- For `h ∉ ⟨e⟩` we have `e^-1 h ∉ ⟨e⟩`, so `F(e.y)(h) = F(y)(e^-1 h) = F(x)(e^-1 h) = F(e.x)(h) = F(x)(h)`.

The same argument applies to `e^-1`. `∎`

**Proposition T3 (a `Z`-SFT, for `e` of infinite order).** Let `R` index the `⟨e⟩`-orbits `⟨e⟩k_r` of `T_K`, so
`|R| ≤ |K|`. Since `e` has infinite order, `(j, r) ↦ e^j k_r` is a bijection `Z × R → T_K`. Put
`c_j(y) = (y(e^j k_r))_{r ∈ R} ∈ A^R`. Let

    D = max{ |n| : e^n ∈ K W^-1 W K^-1  ∪  K M^-1 M K^-1 },

which is finite. Then `c : y ↦ (c_j(y))_{j ∈ Z}` is a homeomorphism from `Σ_K(x, a)` onto a `Z`-SFT
`Y_K ⊆ (A^R)^Z`, defined by a set of allowed `(D+1)`-blocks. It satisfies `c(e.y) = σ(c(y))`, where
`(σw)_j = w_{j-1}`.

*Proof.* For `w ∈ (A^R)^Z`, let `y_w` equal `w` on `T_K` and `x` off `T_K`. Then `c` is a bijection from `Σ_K` to
the set of `w` with `y_w ∈ Σ_K`, and it is continuous both ways. The condition `y_w ∈ Σ_K` consists of two parts.
- `(i)` The pattern of `y_w` on `gW` lies in `Adm`, for every `g ∈ T_K W^-1`. At other `g` the pattern is that of
  `x`.
- `(ii)` `F(y_w)(h) = a` for `h ∈ ⟨e⟩`, and `F(y_w)(h) = F(x)(h)` for `h ∈ T_K M^-1 \ ⟨e⟩`. Here `⟨e⟩ ⊆ T_K M^-1`
  because `1 ∈ K ∩ M`. At other `h`, the output reads only `x`.

*Bounded span.* Suppose two points of `gW ∩ T_K` are `e^{j_1}k_{r_1} = g w_1` and `e^{j_2}k_{r_2} = g w_2`. Then
`k_{r_1}^-1 e^{j_2 - j_1} k_{r_2} = w_1^-1 w_2`, so `e^{j_2 - j_1} ∈ K W^-1 W K^-1` and `|j_2 - j_1| ≤ D`. So the
condition at `g` reads at most `D + 1` consecutive columns. The same holds for `hM ∩ T_K`, using `K M^-1 M K^-1`.

*Translation invariance.* Every `g ∈ T_K W^-1` has the form `e^j g_0` with `g_0 ∈ K W^-1`, a finite set. The
letters of `y_w` off `T_K` are those of `x`, and `x(e^j u) = x(u)`. So the condition at `e^j g_0` is the
`j`-translate of the condition at `g_0`. The same holds for `(ii)`: use `h_0 ∈ K M^-1`, the identity
`F(x)(e^j h_0) = F(x)(h_0)` (true because `F(x) ∈ Fix(e)`), and the fact that `e^j h_0 ∈ ⟨e⟩` if and only if
`h_0 ∈ ⟨e⟩`.

So there are finitely many condition types. Each is a set of allowed `(D+1)`-blocks, placed at every `j`, and
`Y_K` is their intersection. The conjugacy `c(e.y) = σ c(y)` is the computation `c_j(e.y) = c_{j-1}(y)`. `∎`

**Corollary T4 (periodic repairs always exist, with a uniform period).** Let `e` have infinite order. For every
`z ∈ Fix(e)` and `x ∈ X ∩ Fix(e)`, there is `y ∈ Σ_K(x, z(1))` with `e^p . y = y` for some

    1 ≤ p ≤ P(e, K) = max(1, |A|^{D|K|}).

The bound does not depend on `z` or `x`.

*Proof.* `Y_K ≠ ∅` by T1. If `D = 0`, `Y_K` is a product of column sets and has a fixed point. Otherwise, recode
`Y_K` as the edge shift on the graph whose vertices are the `D`-blocks that occur in `Y_K`. There are at most
`|A|^{D|R|}` vertices, and a bi-infinite path exists. So some cycle has length at most the number of vertices,
and it gives a `σ^p`-periodic point. Pull back by `c`, using T3. `∎`

**Corollary T5 (the `e`-invariant tube repair is a finite, clopen test).** Let `e` have infinite order. Then
`Σ_K(x, a) ∩ Fix(e) ≠ ∅` if and only if some column `κ ∈ A^R` has its constant `(D+1)`-block allowed by every
condition type of T3. The condition types read only `a` and `x|_{K_0}`, where
`K_0 = K W^-1 W ∪ K M^-1 M` is finite. So the test is a clopen condition on `(a, x)`. When it holds, the least
such `κ`, in a fixed order, is chosen by a local rule.

*Proof.* The `σ`-fixed points of `Y_K` are exactly the constant sequences `κ^Z` that satisfy every block
condition. Their pull-backs are exactly `Σ_K ∩ Fix(e)`, by T2 and T3. The condition type at `g_0 = k w^-1` reads
`x` on `g_0 W \ T_K ⊆ K W^-1 W`, and the type at `h_0 ∈ K M^-1` reads it on `h_0 M ⊆ K M^-1 M`. `∎`

**Finite-order case.** If `e` has order `n < ∞`, then `T_K` is finite and `Σ_K(x, a)` is a finite nonempty set
(T1) on which the cyclic group `⟨e⟩` acts (T2). An `e`-invariant tube repair exists if and only if this action has a
fixed point. Periodicity is automatic, and T4 carries no information.

## 2. The tube system and its axioms

For `e` of infinite order, put

    Ỹ_K = { w ∈ (A^R)^Z : y_w ∈ X  and  F(y_w)(h) = F(x)(h) for h ∉ ⟨e⟩ },   π(w) = (F(y_w)(e^j))_{j ∈ Z}.

By the proof of T3, `Ỹ_K` is a `Z`-SFT and `π : Ỹ_K → A^Z` is a sliding block code with window `[-D, D]`. The
tube system `(Ỹ_K, π)` has four properties.

- **(A1)** `π` is strongly post-surjective with lifts in `Ỹ_K`, with constant `[-D, D]`. A change of target at `j`
  is lifted by `L_{e^j}`, which changes `y_w` only on `e^jΦ`, and so only on columns within distance `D` of `j`.
  It changes the output only at `e^j`.
- **(A2)** `Ỹ_K` contains the `σ`-fixed point `c(x)`, which is constant because `x ∈ Fix(e)`. Its image is the
  constant `F(x)(1)^Z`.
- **(A3)** `π^-1(a^Z) = Y_K` is nonempty, by T1.
- **(A4)** `π^-1(a^Z)` has `σ^p`-periodic points with `p ≤ P(e, K)`, by T4.

The `e`-invariant coset lift inside `T_K` is exactly a `σ`-fixed point of `π^-1(a^Z)`.

## 3. Calibration: a phase tube with no fixed point in the fibre

Fix an alphabet `A` with `|A| ≥ 2` and a letter `a ∈ A`, and choose `f : A → A \ {a}` onto. The column alphabet is

    B = { (u, p) : u ∈ A, p ∈ {0, 1} }  ∪  { β }  ∪  { (u, ∗) : u ∈ A }.

`Y ⊆ B^Z` is the 2-block SFT defined by two rules:
- two adjacent phase symbols `(u,p)(u',p')` must have `p' ≠ p`;
- `ββ` is forbidden;
- all other adjacent pairs are allowed.

`π` is the 1-block code with `π(u, p) = u`, `π(β) = a` and `π(u, ∗) = f(u)`.

- **(A1) holds with constant `{0}`.** Let the neighbours of site `0` be `l, r ∈ B`, and let the target be `b ∈ A`.
  - If `b ≠ a`, use `(u, ∗)` with `f(u) = b`. Star symbols are compatible with everything.
  - If `b = a` and neither neighbour is `β`, use `β`.
  - If `b = a` and some neighbour is `β`, use `(a, p)`, with `p` opposite to the phase of the other neighbour if
    that neighbour is a phase symbol.

  Changing one site changes the output only there, because `π` is a 1-block code. So all finite changes of target
  are lifted site by site.
- **(A2).** `(u, ∗)^Z ∈ Y` is a fixed point, with image `f(u)^Z ≠ a^Z`.
- **(A3), (A4).** `π^-1(a^Z)` is the SFT over `{(a,0), (a,1), β}` given by the rules above. It contains the
  period-2 point `((a,0)(a,1))^Z`.
- **No fixed point in the fibre.** The `σ`-fixed points of `Y` are constants. `(a,p)^Z` violates alternation,
  `β^Z` contains `ββ`, and `(u,∗)^Z` maps to `f(u)^Z ≠ a^Z`.

Equivalently, on the fibre the transition matrix `M_a` over `{(a,0),(a,1),β}` has `tr M_a = 0` and
`tr M_a^2 = 6`. On every cycle `Z/n` with `n ≥ 3`, the fibre over `a^n` is nonempty and has no rotation-fixed
point. This is the finite-order analogue.

This is checked by machine in `experiments/coset-lift-tubes-2026-09-17/phase_tube.py`, for `|A| = 2, 3, 4` and
cycles `n = 3..8`. The output is in `phase_tube_output.txt`.

The phase tube is an abstract tube system: `|B| > |A|`, so it is not a cover pair over `Z`. This is consistent,
since over `Z` no cover pair exists at all. Its column alphabet is larger than `A`, just as the column alphabet
`A^R` of `Ỹ_K` is.

## 4. The class that dies, and where

**Class: tube-internal coset lifts.** These are arguments that produce the `e`-invariant coset lift at `(z, x)`,
for `e` of infinite order, by a repair supported on one tube `⟨e⟩K`, and that use only axioms (A1)–(A4) of the
tube system `(Ỹ_K, π)`:
- one-dimensional SFT structure;
- strong post-surjectivity with lifts;
- a fixed point elsewhere;
- a nonempty fibre with bounded-period points.

This covers every argument that is one-dimensional and amenable. Examples are Garden-of-Eden and entropy
counting along the tube, and period arguments.

- **Invariant.** The number of `σ`-fixed points of the fibre `π^-1(a^Z)`, that is, the trace of the fibre
  transition matrix after recoding to one step.
- **Dying step.** Extraction of period `1` from the periodic points given by T4. The phase tube satisfies
  (A1)–(A4), and its fibre trace is `0` while the trace at period `2` is positive.
- **Finite order.** In the finite-order case the same example on `Z/n` kills fixed-point extraction from the
  nonempty finite `⟨e⟩`-set `Σ_K`.

**What survives.**
1. **Transverse structure.** A proof of the `e`-invariant lift must use the group `G` across the tube. Two
   routes are possible:
   - enlarging `K` without bound, where `Σ_K ⊆ Σ_{K'}` gives more room for fixed points;
   - repairs whose support is not contained in finitely many `⟨e⟩`-orbits.
2. **Centralizer coupling.** Exactness at `1` on all of `Fix(e)` forces exactness on the centralizer `C(e)`. For
   `z ∈ Fix(e)` and `g ∈ C(e)` we have `g^-1.z ∈ Fix(e)`, so (∗) of Theorem S gives `F(ξ(z))(g) = z(g)`. So the
   tubes `h⟨e⟩K`, `h ∈ C(e)`, must be repaired simultaneously and `e`-invariantly. Corollary S4 records only the
   coset `⟨e⟩`.
3. **Central fold.** If `e` is central, then `Fix(e) ≅ A^Q` with `Q = G/⟨e⟩`, and `X ∩ Fix(e) ≅ X̄`, an SFT over
   `Q`. A seed exact on `Fix(e)` restricts to a `Q`-equivariant section of the folded map `F̄ : X̄ → A^Q`.
   - `F̄` need not be strongly post-surjective. A one-site change in `A^Q` is an `⟨e⟩`-coset change in `A^G`,
     whose `e`-invariant lift is exactly what the phase tube shows can fail.
   - So the fold is not a cover pair, and Theorem S cannot be iterated through it without an `e`-invariant lift
     lemma.
   - Side remark, elementary: if `(X, F)` has a section `s` and `X̄ ⊊ A^Q`, then `s|_{Fix(e)}` is an injective
     non-surjective `Q`-automaton, so `Q` is non-surjunctive.

**What this does not do.** It does not decide the `⟨e⟩`-coset lift for any actual cover pair. The phase tube is
not known to occur as a tube system `(Ỹ_K, π)` of a cover pair for every `K`. An occurrence for all `K`, at a
`z ∈ Fix(e)`, would block every tube repair of that seed at `z`. It would not by itself block a section, since
a section need not arise from tube repairs of a given seed.
