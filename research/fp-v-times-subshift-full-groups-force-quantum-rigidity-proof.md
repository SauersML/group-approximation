---
rg: 2
id: fp-v-times-subshift-full-groups-force-quantum-rigidity-proof
kind: route
title: Feed an arbitrary quantum family into the fibre of the V-orbit representation, check relators on the commuting window idempotents, and read commutation off one commutator; a scalar family of a near-miss point gives finite type
target: fp-v-times-subshift-full-groups-force-quantum-rigidity
requires: [v-times-ample-full-groups-are-generated-by-transpositions]
---

The notation is that of the target. The import is used only for the Corollary (`F(T) = A(T)`).
Parts 1 and 2 use:
- Tietze: a finitely presented group is finitely presented on every finite generating set;
- Lemma N (normal forms) of `fp-v-times-subshift-full-group-connected-differences-proof`, Section 0,
  which uses only the product topology of `T`;
- (part 2 only) Thompson's `V` is finitely generated and simple, and so has trivial centre
  (Cannon–Floyd–Parry; recalled, not re-read).

## 0. Set-up

This repeats the set-up of `fp-v-times-subshift-full-group-connected-differences-proof`, Section 1, with
arbitrary fibre operators in place of `2 × 2` matrices.
- `Γ` has a presentation on a finite set `Σ` that is closed under inverses and contains every `t_s`
  and `e_a`. It is a monoid presentation by relators `w = 1`, including every `σσ^(-1) = 1`. Every
  relator has length `<= n`.
- Each `σ ∈ Σ` has fixed normal-form data `(u_i, v_i, F_i, π_i, λ_i)`. The rectangles
  `[u_i] × [π_i]` partition `C × X`, and `σ(u_i w, x') = (v_i w, λ_i.x')` on them.
  - `t_s` has the single tuple `(∅, ∅, ∅, ∅, s)`.
  - `e_a` has the tuples `(00, 01, {1}, a, 1)`, `(01, 1, {1}, a, 1)`, `(1, 00, {1}, a, 1)`, and
    `(∅, ∅, {1}, b, 1)` for each `b ≠ a`.
- `F_i ⊆ B_r` and `|λ_i| <= ℓ` for all data. Put `R = nℓ + r` and `D_0 = R`.
- `C_0 ⊆ C` is the set of eventually-zero sequences. Prefix replacements preserve it, and it is dense.

**The representation attached to a family.** Let `E = (E_a(q))` be a family of operators on a
`k`-vector space `W_0`. Put `W = k[C_0] ⊗ k[Λ] ⊗ W_0`. For a pattern `π ∈ A^F` and `z ∈ Λ` put
`M_π(z) = ∏_(f ∈ F) E_(π(f))(z^(-1) f)` in a fixed order of `F`, with the empty product equal to `I`.
For `σ ∈ Σ` define

    ψ_E(σ)(δ_c ⊗ δ_z ⊗ u) = Σ_(i : c ∈ [u_i]) δ_(v_i w_i) ⊗ δ_(λ_i z) ⊗ M_(π_i)(z) u,

where `c = u_i w_i` in the `i`-th term. Extend `ψ_E` to words, multiplying right to left.

**Locality.** This is copied from the source. Let `w` be a word of length `j <= n`, and apply
`ψ_E(w)` to `δ_c ⊗ δ_z ⊗ u`.
- After `t` letters every term sits at a site `μz` with `|μ| <= tℓ`.
- The next letter uses operators `E_a(q)` with `q ∈ (μz)^(-1) F_i ⊆ z^(-1) B_(tℓ + r)`.

So only operators `E_a(q)` with `q ∈ z^(-1) B_(jℓ + r)` occur. For a relator this set is inside
`z^(-1) B_R`.

**The orbit action.** For `x' ∈ X`, the map `β_(x') : C_0 × Λ -> C × X`, `(c, z) -> (c, z.x')`, is
injective because `Λ` acts freely. Its image is `Γ`-invariant by Lemma N. Write `ψ_(x')` for `ψ_E`
with the scalar family `E_a(q) = [x'(q) = a]` on `W_0 = k`. As computed in the source, `ψ_(x')(w)`
permutes the basis `δ_c ⊗ δ_z`. It is the action of `w` transported through `β_(x')`.

## 1. Quantum families give representations

**Lemma R.** Let `D >= R` and let `E` be a `D`-quantum family on `W_0`. Then `ψ_E(w) = I` for every
relator `w`, so `ψ_E` defines a homomorphism `Γ -> GL(W)`.

*Proof.* Fix `c ∈ C_0` and `z ∈ Λ`, and let `Y = z^(-1) B_D`. Any two points of `Y` are at distance
`<= 2D`. For `α ∈ A^(B_D)` put `P_α = ∏_(f ∈ B_D) E_(α(f))(z^(-1) f)`.
- By (Q2) all `E_a(q)` with `q ∈ Y` commute. So the `P_α` are commuting idempotents, and the order of
  the product does not matter.
- By (Q1), `P_α P_β = 0` for `α ≠ β`, since they contain `E_a(q) E_b(q) = 0` with `a ≠ b` at some
  site. Expanding `∏_(f ∈ B_D) Σ_a E_a(z^(-1) f) = I` gives `Σ_α P_α = I`.
- By (Q3) with `p = z^(-1)`, `P_α = 0` unless `α` occurs in `X`. When it occurs, shift invariance
  gives `x' ∈ X` with `x'(z^(-1) f) = α(f)` for all `f ∈ B_D`.
- For `q ∈ Y`, `E_a(q) P_α = P_α E_a(q) = [x'(q) = a] P_α`. So `range(P_α)` is invariant under every
  `E_a(q)` with `q ∈ Y`, and each of them acts on it as the scalar `[x'(q) = a]`.

Let `w` be a relator and `u ∈ range(P_α)` with `P_α ≠ 0`.
- By locality, every operator in the computation of `ψ_E(w)(δ_c ⊗ δ_z ⊗ u)` is an `E_a(q)` with
  `q ∈ z^(-1) B_R ⊆ Y`, applied to a multiple of `u`.
- Replacing each of them by `[x'(q) = a]` changes nothing. So
  `ψ_E(w)(δ_c ⊗ δ_z ⊗ u) = ψ_(x')(w)(δ_c ⊗ δ_z) ⊗ u`.
- Since `w = 1` in `Γ ≤ F(T)`, `w` fixes `β_(x')(c, z)`. Injectivity of `β_(x')` gives
  `ψ_(x')(w)(δ_c ⊗ δ_z) = δ_c ⊗ δ_z`.

Summing over `α` gives `ψ_E(w) = I` on `δ_c ⊗ δ_z ⊗ W_0`, for every `c` and `z`. The relators
`σσ^(-1) = 1` make every `ψ_E(σ)` invertible. `∎`

Lemma R uses neither minimality nor finite type, only freeness of the action on `X`.

## 2. Part 1: commutation

Let `D >= D_0 = R`, let `k` be any field, and let `E` be a `D`-quantum family on `W_0` over `k`. Fix
`p, q ∈ Λ` and `a, b ∈ A`. For `g ∈ Λ`, write `t_g` for a word in the `t_s` representing translation
by `g`.

**Two commuting elements.** Put `g_1 = t_(p^(-1))^(-1) e_a t_(p^(-1))` and
`g_2 = t_(q^(-1))^(-1) e_b t_(q^(-1))`, both in `Γ`.
- In `F(T)`, `g_1(c, x') = (h^([x'(p) = a]) c, x')` and `g_2(c, x') = (h^([x'(q) = b]) c, x')`. Both fix
  the `X` coordinate and act on `C` by powers of the same `h`, so they commute.
- Hence `[g_1, g_2] = 1` in `Γ`, and `ψ_E(g_1)` commutes with `ψ_E(g_2)` by Lemma R.

**Their images.**
- `ψ_E(t_g)(δ_c ⊗ δ_z ⊗ u) = δ_c ⊗ δ_(gz) ⊗ u`.
- By (Q1), `Σ_(b' ≠ a) E_(b')(z^(-1)) = I - E_a(z^(-1))`. With `H` the permutation `δ_c -> δ_(hc)` of `k[C_0]`:

      ψ_E(e_a)(δ_c ⊗ δ_z ⊗ u) = δ_(hc) ⊗ δ_z ⊗ E_a(z^(-1)) u + δ_c ⊗ δ_z ⊗ (I - E_a(z^(-1))) u.

- `ψ_E(t_(p^(-1)))` moves `δ_1` to `δ_(p^(-1))`, where `ψ_E(e_a)` uses `E_a(p)`, and the inverse moves
  it back. So `k[C_0] ⊗ δ_1 ⊗ W_0` is invariant, and on it

      ψ_E(g_1) = I + (H - 1) ⊗ E_a(p),    ψ_E(g_2) = I + (H - 1) ⊗ E_b(q).

**Conclusion.** The commutator difference is
`ψ_E(g_1) ψ_E(g_2) - ψ_E(g_2) ψ_E(g_1) = (H - 1)^2 ⊗ (E_a(p) E_b(q) - E_b(q) E_a(p))`, and it is `0`.
- For `c = 0^∞`, the points `c`, `hc = 010^∞` and `h^2 c = 10^∞` are distinct. So `(H - 1)^2 δ_c` has
  coefficient `1` at `δ_c`, in every characteristic.
- Apply the difference to `δ_c ⊗ δ_1 ⊗ u`. The result is `(H - 1)^2 δ_c ⊗ δ_1 ⊗ [E_a(p), E_b(q)] u`,
  which is `0` only if `[E_a(p), E_b(q)] u = 0`.

So `E_a(p)` and `E_b(q)` commute, for all `p, q, a, b`. `X` is `D`-quantum rigid over `k`. `∎`

## 3. Part 2: finite type

Assume also `V × {1} ≤ Γ`.

**Approximating SFTs.** For `N >= 0` let `X_N` be the set of `y ∈ A^Λ` such that, for every `p ∈ Λ`,
the pattern `f -> y(pf)` on `B_N` occurs in `X`.
- `X_N` is an SFT containing `X`, the sequence `X_N` decreases, and `∩_N X_N = X`.
- If `X` is not of finite type, then `X_N ≠ X` for every `N`.

**Choice of `N`.** Fix generators `v_1, ..., v_s` of `V`. Write each `v_j × 1 ∈ Γ` as a word `u_j`
in `Σ` of length `<= n_V`. Put `N = max(R, n_V ℓ + r)`. Suppose `X` is not of finite type, and pick
`y ∈ X_N \ X`.

**The scalar family of `y`.** Put `E_a(q) = [y(q) = a]` on `W_0 = k`. (Q1) and (Q2) are clear. For
(Q3) at scale `N`, `∏_(f ∈ B_N) E_(α(f))(pf) = [y(pf) = α(f) for all f ∈ B_N]`, which is `0` when `α`
does not occur in `X`, because `y ∈ X_N`. By Lemma R, `ψ_y := ψ_E` is a homomorphism `Γ -> GL(k[C_0 × Λ])`.

**`ψ_y` on `V` and on conditioned 3-cycles.**
- *`V`.* By locality, `ψ_y(u_j)(δ_c ⊗ δ_z)` reads `y` only on `z^(-1) B_(n_V ℓ + r) ⊆ z^(-1) B_N`.
  There `y` agrees with some `x' ∈ X`. So the value equals `ψ_(x')(u_j)(δ_c ⊗ δ_z) = δ_(v_j c) ⊗ δ_z`,
  since `u_j` acts on `C × X` as `v_j × 1` and `β_(x')` is injective. By multiplicativity,
  `ψ_y(v × 1)(δ_c ⊗ δ_z) = δ_(vc) ⊗ δ_z` for every `v ∈ V`.
- *Conditioned 3-cycles.* For `f ∈ Λ`, `a ∈ A` and `v ∈ V`, put
  `τ(f, a, v) = (v × 1) t_(f^(-1))^(-1) e_a t_(f^(-1)) (v × 1)^(-1) ∈ Γ`, and `h_v = v h v^(-1)`.
  - In `F(T)`: `τ(f, a, v)(c, x') = (h_v^([x'(f) = a]) c, x')`.
  - Under `ψ_y`: `δ_c ⊗ δ_z -> δ_(h_v^([y(z^(-1) f) = a]) c) ⊗ δ_z`, by the formulas of Section 2 with
    `u ∈ k`.

**Iterated commutators in `V`.** There are `v_1', v_2', ... ∈ V` with the following property. Put
`c_1 = h_(v_1')` and `c_j = [c_(j-1), h_(v_j')]`. Then every `c_j ≠ 1`.
- Choose them inductively. If `c_(j-1) ≠ 1` commuted with every conjugate of `h`, it would centralize
  the normal closure of `h`.
- That normal closure is `V`, since `V` is simple and `h ≠ 1`. The centre of `V` is trivial.

**The word.** `y ∉ X` and `X` is closed, so `y` carries, at some position `p`, a pattern
`π ∈ A^F` (`F = {f_1, ..., f_k}` finite) that does not occur in `X`: `y(p f_i) = π(f_i)`. Put
`w_1 = τ(f_1, π(f_1), v_1')` and `w_j = [w_(j-1), τ(f_j, π(f_j), v_j')]`.
- *In `Γ`.* Elements of the form `(c, x') -> (γ_(x') c, x')` compose and commute fibrewise. So
  `w_k(c, x') = (c_k^(ε(x')) c, x')`, where `ε(x') = 1` if `x'(f_i) = π(f_i)` for all `i`, and `0`
  otherwise. Since `π` does not occur in `X`, `ε ≡ 0`, and `w_k = 1` in `Γ`.
- *Under `ψ_y`.* In the same way, `ψ_y(w_k)(δ_c ⊗ δ_z) = δ_(c_k^(ε_y(z)) c) ⊗ δ_z`, where
  `ε_y(z) = 1` if `y(z^(-1) f_i) = π(f_i)` for all `i`, and `0` otherwise.
- Take `z = p^(-1)`, so that `ε_y(z) = 1`. `c_k ≠ 1` is a homeomorphism of `C`, so it moves a nonempty
  open set, which meets the dense set `C_0`. So `ψ_y(w_k) ≠ I`.

This contradicts `w_k = 1` in `Γ`. So `X` is of finite type. `∎`

`N` is fixed before `y` is chosen. The words `w_k` can be arbitrarily long, but their `V` letters are
products of the fixed words `u_j`, and their other letters are `t_s` and `e_a`, which read one site.
So no locality bound on `w_k` is needed.

## 4. Scale and metric

**Monotonicity.** A `D'`-quantum family with `D' >= D` is a `D`-quantum family.
- (Q1) is unchanged, and (Q2) at `2D` is weaker.
- For (Q3), let `α` on `B_D` not occur in `X`. Insert `I = Σ_b E_b(pf)` for each `f ∈ B_(D') \ B_D`.
  All factors lie in `pB_(D')` and commute by (Q2). So `∏_(f ∈ B_D) E_(α(f))(pf)` is the sum, over
  extensions `β` of `α` to `B_(D')`, of the `B_(D')` products. No `β` occurs in `X`, so every term is
  `0` by (Q3) at `D'`.

Hence `D`-rigidity implies `D'`-rigidity. The same argument compares two metrics `d, d'` with
`d <= c d'` and `d' <= c d`, for example two word metrics, or the `l^1`, `l^∞` and Euclidean norms
on `Z^2`.
- A `d'`-family at scale `cD` is a `d`-family at scale `D`, since `B_D ⊆ B'_(cD)` and
  `d(q, q') <= 2D` implies `d'(q, q') <= 2cD`.
- So `d`-rigidity at `D` implies `d'`-rigidity at `cD`, and "rigid at all large scales" does not depend
  on the metric.

For `Λ = Z^2` and an SFT `X` with forbidden patterns in `B_r`, part 1 therefore gives `D`-quantum rigidity
in the sense of `sft-crossed-product-fp-iff-quantum-rigid` for some `D >= r`, over every field `k`. That
node then makes `LC(X, k) ⋊ Z^2` finitely presented.

## 5. Corollary and remarks

- **Corollary.** By `v-times-ample-full-groups-are-generated-by-transpositions`, `F(T) = A(T)`.
  `F(T)` contains every `t_s`, every `e_a` (a 3-cycle of a degree-3 multisection) and `V × {1}`. If
  `A(T)` is finitely presented, take `Γ = F(T)` in parts 1 and 2.
- **Wall families.** The family of `fp-v-times-subshift-full-group-connected-differences-proof`,
  Section 1, is a `D`-quantum family on `k^2` whenever the two parts are at distance `> 2D`. Every set
  of diameter `<= 2D` (a window, or a pair of sites in (Q2)) misses one
  part of the split, so on it the family is simultaneously conjugate to diagonal scalar families of
  points of `X`, and (Q1)–(Q3) hold. Part 1 therefore contains that theorem.
- **What part 1 does not use.** It uses neither minimality nor finite type, and needs `V` only through
  the operator `H` on `k[C_0]` with `(H - 1)^2 ≠ 0`.
