
## 36. w7-escape-set (45282c2142)

Sources:
- Artifact `four-transvection-escape-set-2026-09-12.md` (blob `cb33ab0f`), Sections 0–5.
- The claims `four-transvection-set-escapes-depth-monotone-units` (blob `1339c38f`),
  `four-transvection-units-have-a-weakly-finite-symbol-image` (blob `fcc45de7`) and
  `depth-monotone-units-carry-weakly-finite-nonzero-defect` (blob `9e696bc5`).
- The OPEN claim `four-transvections-and-x23-force-defect-vanishing` (blob `1f3ccdee`).
- The routes `four-transvection-escape-proof` (blob `384f5613`), `four-transvection-symbol-firewall-proof` (blob
  `85927ae8`), `depth-monotone-tensor-cube-defect-proof` (blob `06b2138e`) and
  `summand-obstruction-from-four-transvection-defect` (blob `0aff6a1e`).
- The entries on `ternary-leavitt-units-have-no-weakly-finite-representation` (blob `a274ca7f`) and
  `ternary-weakly-finite-representations-kill-two-root-defect` (blob `99a42c33`).

**Verdict: PASS on Sections 1–4, the three claim displays and the three proof routes.** The OPEN claim is correctly
OPEN, and `summand-obstruction-from-four-transvection-defect` is a valid implication. There are three wording
advisories (36.5) and no correction.

It is decision-level for the ternary counterexample route:
- the defect form (iv) is firewalled on every sofic subgroup of `G` containing `z` and the standard frame, and
  explicitly, without soficity, on `H^ω_≤` with `ω(0) <= ω(1)`;
- so a proof of `ternary-weakly-finite-representations-kill-two-root-defect` must use relations that hold in none
  of them;
- the smallest known input for `ternary-anti-central-summand-has-no-weakly-finite-image` is `Γ_5 = <S4, x_23(1)>`,
  which is OPEN, and soficity of `Γ_5` would refute it.

Every model built here is nontrivial, with `z -> -1` and `D != 0`. Nothing proves that rank models are trivial.
Gottschalk on `G`, the gate and Plan 1 stay OPEN.

### 36.1 The escape invariant (Section 1). PASS

- **Theorem 1.1, recomputed.** Put `A = s_0 t_1`, `A' = s_1 t_0`, `B = s_1 t_00` and `B' = s_00 t_1`, the four
  transvections minus `1`.
  - `B'A' = s_00 t_0`, `A'A = s_1 t_1` and `AB = s_0 t_00`.
  - `x = s_00 t_0 + s_1 t_1` and `y = s_0 t_00 + s_1 t_1` give `yx = s_0 t_0 + s_1 t_1 = 1`, because
    `t_00 s_1 = 0 = t_1 s_00`.
  - `xy = s_00 t_00 + s_1 t_1 = 1 − s_01 t_01`.
  - A conjugate of `<S4>` inside `H^ω_≤` would put the conjugated pair inside the stably finite `R^ω_≤`
    (`depth-monotone-leavitt-subalgebras-are-stably-finite`). The `≥` side is the same.
- **Remark 1.2, recomputed.** With `ω(0) = a` and `ω(1) = b`, the roots compare `a : b` (`A`), `b : a` (`A'`),
  `b : 2a` (`B`) and `2a : b` (`B'`).
  - `{A, A', B}` lies on the `≤` side and `{A, A', B'}` on the `≥` side, both with `a = b`.
  - `{A, B, B'}` lies on the `≤` side and `{A', B, B'}` on the `≥` side, both with `b = 2a`.
  - The inverses `1 − n` stay in each span.
- **Proposition 1.3.** It rests on Lemma 1.2 of `depth-monotone-leavitt-firewall-2026-09-12.md`, read at its lines
  66–72:
  - each `F_r` is finite-dimensional, `F_r ⊆ F_r'` for `r <= r'`, and `C = ∪_r F_r`;
  - `π(s_μ t_ν) F_r ⊆ F_r` when `ω(μ) <= ω(ν)` and `ω(μ) <= r`.

  So a finite combination of `≤` monomials preserves `F_r` for large `r` and is locally finite.
  - If `π(ugu^(-1))` is locally finite, so is `π(g) = π(u)^(-1) π(ugu^(-1)) π(u)`.
  - On the `≥` side, `(ugu^(-1))^* = (u^*)^(-1) g^* u^*` lies on the `≤` side.
- **Corollary 1.4, recomputed.** `x_0 = s_0 t_00 + s_10 t_01 + s_11 t_1`.
  - On `1_[1^n]` with `n >= 1`, only `s_11 t_1` contributes, and it gives `1_[1^(n+1)]`. So the orbit of `1_[1]`
    spans an infinite-dimensional space.
  - `x_0` is the element `00y -> 0y`, `01y -> 10y`, `1y -> 11y` of `V`, so `x_0^* = x_0^(-1)`.
  - An invertible locally finite operator maps each finite-dimensional invariant subspace bijectively onto itself,
    so its inverse is locally finite. Both sides fail for `x_0`.

### 36.2 The symbol image (Section 2). PASS

- **Theorem 2.1(a), recomputed.** For incomparable `σ = σ_1 σ'` and `κ = κ_1 κ'`, the formula
  `t_i s_σ t_κ s_j = δ_(i σ_1) δ_(j κ_1) s_(σ') t_(κ')` gives `Φ(S4) = {E_01(1), E_10(1), E_10(t_0), E_01(s_0)}`.
  - `e_10 (s_0 e_01) = s_0 e_11` and `(s_0 e_01) e_10 = s_0 e_00`, so `s_0 I` lies in the span, and likewise `t_0 I`.
    With `M_2(K)` this gives `M_2(T)`.
  - Conversely every generator and its inverse lies in `M_2(T)`.
  - `T = K<s_0, t_0>` is the Jacobson algebra, by the normal-form basis `s_0^a t_0^b`.
- **(b).** `E_01(1)` and `E_10(1)` generate `SL_2(F_3)`, which contains `−I`. So `z in <S4>`.
- **(c), recomputed.** Under `s_0 -> ζ`, `t_0 -> ζ^(-1)`:
  - `w(ζ) = E_01(ζ) E_10(−ζ^(-1)) E_01(ζ) = [[0, ζ], [−ζ^(-1), 0]]`, `w = w(1)`, and
    `w(ζ) w^(-1) = diag(ζ, ζ^(-1))`, the inverse of `h = diag(ζ^(-1), ζ)`;
  - conjugating `E_01(1)` and `E_01(ζ)` by `h^n` gives `E_01(ζ^(-2n))` and `E_01(ζ^(1-2n))`, so `E_01(p)` for every
    Laurent polynomial `p`, and conjugating by `w` gives `E_10(p)`;
  - `F_3[ζ, ζ^(-1)]` is Euclidean, so `E_2 = SL_2` and the image is `SL_2(F_3[ζ, ζ^(-1)])`, with `z -> −I`.
  - The kernel of `T -> F_3[ζ, ζ^(-1)]` is spanned by `s_0^a (1 − s_0 t_0) t_0^b = s_0^a s_1 t_1 t_0^b`.
- **(d) and Lemma 2.2.** A unital algebra map into a weakly finite algebra with `[z] -> −1` sends
  `ε_- = 2(1 − [z])` to `4 = 1`. So `ε_- F_3[<S4>]` maps unitally onto a nonzero weakly finite algebra. Conjugation
  gives an isomorphic group algebra.

### 36.3 Relations and algebra-level models (Section 3). PASS

- **Lemma 3.1.** `N_23 N_12 = ψ(s_10 t_11 · s_0 t_10)`, and `t_11 s_0 = t_1 t_1 s_0 = 0`. In a conjugate frame the
  product is `ψ(u · 0 · u^(-1))`.
- **Proposition 3.2, recomputed.**
  - (a) `Φ(s_0 t_10) = t_0 e_01`. `E_01(1) E_10(−1) E_01(1) = e_01 − e_10 = w` and `w e_10 w^(-1) = −e_01`, so
    `E_01(−t_0)` and its inverse `E_01(t_0)` lie in `Φ(<S4>)`.
  - (b) `Φ(s_10 t_11) = s_0 t_1 e_11`, and `s_0 t_1` is a normal-form monomial outside `span{s_0^a t_0^b}`.
  - (c) The `Φ`-entries of the six roots:
    - code `{0, 10, 11}`: `s_0 t_10 -> t_0`, `s_10 t_0 -> s_0`, `s_0 t_11 -> t_1`, `s_11 t_0 -> s_1`,
      `s_10 t_11 -> s_0 t_1`, `s_11 t_10 -> s_1 t_0`;
    - code `{1, 00, 01}`: `s_1 t_00 -> t_0`, `s_00 t_1 -> s_0`, `s_1 t_01 -> t_1`, `s_01 t_1 -> s_1`,
      `s_00 t_01 -> s_0 t_1`, `s_01 t_00 -> s_1 t_0`.

    Only `t_0` and `s_0` lie in `T`, and they come from `{0, 10}` and `{1, 00}`. The roots `x_12` and `x_23` of a code
    frame use the distinct pairs `{c_1, c_2}` and `{c_2, c_3}`.
- **Proposition 3.3, recomputed.**
  - (a) Incomparable `σ, κ` make `s_σ t_κ` square-zero, so `T^(-1) = 1 − λ s_σ t_κ`. `e_ki (λ m e_ij) e_jl = λ m e_kl`
    gives `m I`. Conversely every generator and inverse lies in `M_2(W)`.
  - (b) `Q = 1 − s_0 t_0` lies in `T`, and `ψ(t_0) ψ(s_0) = 1` forces `ψ(Q) = 0`.
    - If `β = 0^(j-1) 1 β''`, then `t_β = t_(β'') t_1 t_0^(j-1)`, and
      `m s_0^(j-1) Q t_0^(j-1) = s_α t_(β'') t_1 s_1 t_1 t_0^(j-1) = m`.
    - The case of `α` is the mirror image.
  - (c) On `K[Ω]` the relations `t_i s_j = δ_ij` and `s_0 t_0 + s_1 t_1 = 1` hold, since every sequence has a first
    letter.
    - If `β` contains a `1`, then `t_β e_(0^∞) = 0`. The line `K e_(0^∞)` is invariant, with `s_0, t_0 -> 1` and
      `m -> 0`.
    - If `β = 0^b` and `α` contains a `1`, then `s_0` and `t_0` preserve `U = span{e_ξ : ξ != 0^∞}`, and `m` sends
      `e_ξ` to `0` or to `e_(αξ')` with `αξ' != 0^∞`. On the one-dimensional quotient `s_0, t_0 -> 1` and `m -> 0`.
    - Otherwise `m = s_0^a t_0^b` lies in `T`, and `χ` is the symbol at `ζ = 1`.

    Over `F_3`, `M_2(χ)` sends `z` to `−I`.
  - (d) `Φ(s_01 t_1) = s_1 e_01` and `Φ(s_1 t_01) = t_1 e_10`, so `W = R`. A nonzero map from the simple algebra `R` is
    injective and keeps `t_0 s_0 = 1 != s_0 t_0`.
- **Corollary 3.4, recomputed.**
  - `t_0 · s_0 t_1 = t_1`, so `W_5 = K<s_0, t_0, t_1>`. Words reduce by `t_0 s_0 = 1` and `t_1 s_0 = 0` to the
    monomials `s_0^a t_ν`.
  - (b) The images of the `e_ij` are matrix units summing to `1`, so `W = M_2(W')`. `W'` is a corner of a weakly finite
    algebra, so it is weakly finite, and `ψ∘Φ^(-1) = M_2(ψ')`. Proposition 3.3(b) with `β = 1` gives `ψ'(s_0 t_1) = 0`.
  - (c) `t_ν s_0^b` is `t_(ν'')` if `ν = 0^b ν''`, is `s_0^(b-c)` if `ν = 0^c` with `c < b`, and is `0` otherwise.
    - So the product of two basis monomials is `s_0^a t_(λν'')`, `s_0^(a+b-c) t_λ` or `0`.
    - `σ_5` is multiplicative in each case, since `|λν''| = |λ| + |ν| − b`, and the value is `0` once `ν` or `λ` has a
      `1`.
    - `σ_5(s_0 t_1) = 0`, so `x_23(1) -> I`.

### 36.4 Weakly finite models with D != 0 (Section 4). PASS

- **Theorem 4.1, recomputed.**
  - `F_3[Γ_0]` is stably finite by `linear-sofic-group-algebra-is-stably-finite` (ESTABLISHED): `Γ_0` is countable,
    and sofic groups are linear sofic.
  - `[z]` is central with `[z]^2 = 1`, so `ε_-^2 = 4(2 − 2[z]) = 2(1 − [z])` mod `3`.
  - A corner at a central idempotent of a stably finite ring is stably finite. `ρ(gh) = ε_-[g] ε_-[h]`, and
    `ε_-[z] = −ε_-`.
  - `x_23(1) x_12(1) = 1 + s_0 t_10 + s_10 t_11`, because `s_10 t_11 s_0 t_10 = 0`.
    - The four elements `1`, `x_12(1)`, `x_23(1)`, `x_23(1) x_12(1)` are `1` plus distinct sums of the independent
      monomials `s_0 t_10` and `s_10 t_11`.
    - Their `z`-multiples have coefficient `−1 != 1` on the monomial `1`.
    - So the eight terms of `D_ρ`, each with coefficient `±2`, are distinct and `D_ρ != 0`.
- **Corollary 4.2.** `ω(0) <= ω(10) = ω(1) + ω(0)`, and `ω(10) <= ω(11)` if and only if `ω(0) <= ω(1)`. `H^ω_≤` is
  countable and sofic (`depth-monotone-leavitt-subalgebras-are-stably-finite`, ESTABLISHED).
- **Theorem 4.3, recomputed.**
  - For large `k`, `F_k` is invariant under `g`, `h` and `gh`, so `(gh)_k = g_k h_k` and `(g^(-1))_k = g_k^(-1)`.
  - `AB = I` in `M_n(Q_3)` means `A_k B_k = I` for all large `k`, so `B_k A_k = I` for all large `k`.
  - `z_k^(⊗3) = (−1)^3 = −1`.
  - `mn = π(s_10 t_11 s_0 t_10) = 0`.
    - `(1 + n)^(⊗3) − 1 = Σ_(S != ∅) n^S`, and `m^T n^S` carries `mn` on `S ∩ T`.
    - Each coordinate lies in `S`, in `T` or in neither, so there are `3^3 − 2^3 − 2^3 + 1 = 12` survivors. Each has
      coefficient `1`, and their patterns in `{1, n, m}^(⊗3)` are distinct.
  - Put `(π(s_μ t_ν) f)(μξ) = f(νξ)`. Then `n 1_[10] = 1_[0]`, `m 1_[10] = 0`, `n 1_[11] = 0` and
    `m 1_[11] = 1_[10]`.
    - So `1`, `n`, `m` are independent, and the `27` elementary tensors in them are independent.
    - So `D_k != 0` for all large `k`, which is `D_(ρ_3) != 0` in `Q_3`.
- **Remark 4.4.**
  - `(gh)^* = h^* g^*`, so `g -> (g^*)^(-1)` is an automorphism of `G`. It exchanges `H^ω_≥` and `H^ω_≤`, and it sends
    `x_12(1)` to `1 − s_10 t_0`.
  - Advisory 3 in 36.5 concerns this remark's wording.

### 36.5 Section 5, claim displays, entries, routes, subsumption and scope. PASS

- **Section 5, item 1: the route `summand-obstruction-from-four-transvection-defect`, recomputed.**
  - A unital `ψ : S_- -> W` gives `ρ(g) = ψ(ε_- g)`, a homomorphism `G -> W^x` with `ρ(z) = ψ(−ε_-) = −1`.
  - `D_ρ` involves only `x_12(1)` and `x_23(1)`, both in `Γ_5`, so the OPEN claim gives `D_ρ = 0`.
  - `weakly-finite-leavitt-representations-killing-defect-are-trivial` (ESTABLISHED, characteristic `p > 0`,
    `Γ = R^x`) makes `ρ` trivial. Then `−1 = 1`, so `W = 0` in characteristic three.
  - The target says that no nonzero quotient of `S_-` is weakly finite. Such a quotient is a `W` as above, so the
    implication is valid, and the route is correctly OPEN.
- **Refuters, recomputed.**
  - Soficity: Theorem 4.1 applies to a sofic `Γ_5`, since `z` and `x_12(1)` lie in `<S4>`.
  - Finite quotients: let a finite quotient `Q` separate the eight elements.
    - The image of `z` is central of order two, so `ε_-` is a central idempotent of the finite-dimensional algebra
      `F_3[Q]`.
    - The same eight-term `D` is nonzero there.
- **Item 2.**
  - `jacobson-elementary-subgroups-are-locally-finite-by-linear` is ESTABLISHED (Section 31.1 here).
  - The Tits alternative holds for finitely generated linear groups in every characteristic.
    `SL_2(F_p[ζ, ζ^(-1)])` is not virtually solvable, so `<S4>` is not amenable and lies in no `U_< ⋊ P`.
  - A graph of groups with sofic vertex groups and amenable edge groups is sofic.
- **Items 3–4** restate Propositions 3.3(d) and 3.2(c).
- **Claim displays.**
  - Escape claim: items 1–4 are Theorem 1.1, Remark 1.2, Proposition 1.3 and Corollary 1.4, as recomputed in 36.1.
  - Symbol claim: items 1–5 are Theorem 2.1(a)–(c), Lemma 2.2, and Propositions 3.2 and 3.3(c)–(d). The
    non-amenability consequence is item 2 above.
  - Defect claim: items 1–4 are Theorem 4.1, Corollary 4.2, Theorem 4.3 and Lemma 3.1. The Scope is Remark 4.4.
  - OPEN claim: the statement, the refuters and the algebra-level Attempt are as recomputed. The Attempt is
    Corollary 3.4(b): a weakly finite image kills `s_1 t_1` and `s_0 t_1`.
- **Entries.** The two entries on the ternary nodes summarize Sections 1–5 accurately, subject to advisory 1.
- **Routes.**
  - `four-transvection-escape-proof` requires `depth-monotone-leavitt-subalgebras-are-stably-finite`, which is
    ESTABLISHED. Its steps are 36.1.
  - `four-transvection-symbol-firewall-proof` requires only the Alahmedi–Alsulami–Jain–Zelmanov normal form
    (literature). Its steps are 36.2–36.3.
  - `depth-monotone-tensor-cube-defect-proof` requires the depth-monotone node and
    `linear-sofic-group-algebra-is-stably-finite`, both ESTABLISHED. Its steps are 36.3–36.4.
- **Advisories (wording only).**
  1. "Every five-transvection set" means `S4 ∪ {T}`. The phrase appears in the Scope of the escape claim and in the
     first ternary entry. Section 5, item 4 says that other five-transvection sets are not covered.
  2. The symbol claim's consequence "An anti-central model that is not an algebra homomorphism needs at least six
     transvections" is about obstructions, not models. Suggested wording: "for a set containing `S4`, an obstruction
     that no algebra-level model defeats needs at least six transvections, or a relation outside the span of the
     group".
  3. Remark 4.4 says that `z -> −1` and `D != 0` "fail together only for algebra-level models", which is not proved.
     What is proved is Lemma 3.1, plus the non-additive models of Theorems 4.1 and 4.3. No claim display uses the
     stronger wording.
- **Subsumption scan at `39971c4c98`.** Seven phrases hit 145 research files: "tensor cube", "weakly finite corner",
  "one-sided inverse pair", "transvection set", `EL_2(J`, `SL_2(F_3[` and "nonzero defect". I read the claim and
  route nodes among them by title and hit line.
  - **Unitriangular groups, no `z`.** `unitriangular-data-cannot-assemble-corner-leavitt-families` and
    `unipotent-frame-relations-cannot-assemble-corner-cuntz-family` give rank models with nonzero two-root defect on
    unitriangular groups. Those groups do not contain `z`, so neither is the anti-central form. The defect claim may
    list the first in `distinct_from`.
  - **Inputs to the route.** `ternary-weakly-finite-representations-give-anti-central-images` and
    `no-weakly-finite-representation-from-summand-obstruction` relate representations and summand images, which the
    route uses.
  - **Different targets.** `ternary-defect-is-full-in-largest-weakly-finite-image` is a different OPEN target, and
    `rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup` is about Kazhdan subgroups of `EL_2(J_k)`.
  - **Other senses.** The remaining hits use the phrases in other senses: A8 certificates, one-hot encodings, Hamming
    defects, and orbits of one-sided pairs.
  - **Recorded.** `distinct_from` already records `depth-monotone-configurations-cannot-force-ternary-minus-one`,
    whose models kill `D`. It also records `anti-central-sofic-data-cannot-force-defect-submultiplicativity` (rank
    `5/9` on cylinder defects) and `ternary-weakly-finite-representations-kill-two-root-defect`.

  No duplicate.
- **Scope.** Each firewall exhibits a nontrivial weakly finite model. None forces a rank model, or `theta`, to be
  trivial. Still OPEN: soficity of `<S4>` and of `Γ_5`, whether `<S6> = G`, and conjugate frames inside `<S4>`.

## 37. w7-sub-multiletter follow-up (07136ca640)

Sources:
- Artifact `multiletter-split-borel-and-coefficient-firewalls-2026-09-12.md` (blob `e60bf257`), Section 6.
- `lex-decreasing-units-with-order-preserving-letters-are-amenable` (blob `1d8fdf38`).
- `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (blob `915925b1`).

**Verdict: PASS. The correction of 35.4 has been applied.**
- **Lemma 6.1.** The hypothesis now requires that, for each of the frames at `A` and `A1`, all positive roots move
  points in one common direction.
  - The "Same direction" step carries the direction at `A` to `S[A10]T[A110]`, and so to the whole frame at `A1`.
  - The "Not preserved" step is unchanged.
  - This is the corrected statement of 35.4, proved by the same two steps.
- **Remark.** The added remark reproduces the counterexample of 35.4, including the block order
  `[A0] < [A10] < [A111] < [A110]`. It rests item 1 of Section 6 on the common-direction hypothesis, which is what
  Theorem 3.5 uses.
- **Wording.** Two places now say "monotone in one common direction":
  - the Scope of the lex claim;
  - the w7-sub-multiletter bullet on the SUB target.
- **Status.** No claim statement changed, so the PASS of Section 35 carries over to the new blobs.
