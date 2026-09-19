---
rg: 2
id: iwahori-depth-drift-bounds-smooth-vertex-mismatch-proof
kind: route
title: "Clifford eigenline count at depth >= 2, Mackey--Bruhat at depth 1, and a signed depth-drift certificate"
target: iwahori-depth-drift-bounds-smooth-vertex-mismatch
requires: []
artifacts:
  - experiments/sl2-pq-iwahori-mismatch-2026-09-17/depth_drift.py
---

Notation is as in the target. `K(q^a)` is the principal congruence subgroup
of `K_0`. `K_1(q^a) = g K(q^a) g^(-1)` is the set of matrices with
`a, d ≡ 1 mod q^a`, `b ≡ 0 mod q^(a+1)` and `c ≡ 0 mod q^(a-1)`.

Both families are normal in `I`, and

```text
K_1(q^(a+1)) ⊂ K(q^a),      K(q^(a+1)) ⊂ K_1(q^a).       (P1)
```

For a representation `V` of `I` and a normal subgroup `N`, the fraction of
`V` fixed by `N` equals the dimension-weighted fraction of `I`-constituents
that are trivial on `N`.

## Step 0: range of the drift

By `(P1)`, `d_0 <= d_1 + 1` and `d_1 <= d_0 + 1`. So `Φ ∈ {-1,0,1}`.

## Step 1: depth n >= 2

Let `ρ` be irreducible for `K_0` of depth `n >= 2`, so that `ρ` is trivial on
`K(q^n)` but not on `K(q^(n-1))`.

**No constituent has depth below `n`.**
- `K(q^(n-1))` is normal in `K_0` and contained in `I`.
- Its fixed space is therefore a proper `K_0`-subrepresentation, which must be zero.
- So every `I`-constituent `τ` has `d_0(τ) = n`, and none is trivial.
- Hence `E Φ = P(d_1 = n+1) - P(d_1 = n-1) = 1 - P(d_1 <= n) - P(d_1 <= n-1)`.

**The abelian layer.** Put `A_n = K(q^(n-1))/K(q^n)`.
- Since `2n-2 >= n`, the map `X ↦ 1 + q^(n-1)X` is an isomorphism `sl_2(F_q) → A_n`.
- `K_0` acts on `A_n` by conjugation through `SL_2(F_q)`.
- The trace pairing identifies the dual of `A_n` with `gl_2(F_q)/scalars`, by `β ↦ ψ_β(X) = e(tr(βX)/q)`. This works in every characteristic, because the scalars are exactly the annihilator of `sl_2` under the nondegenerate trace form of `gl_2`.
- By Clifford's theorem, `ρ|_(A_n) = m ⊕_(β ∈ O) ψ_β` for a single `SL_2(F_q)`-orbit `O` of non-scalar classes.

**The subgroups in the layer.**
- The image of `K_1(q^n)` in `K_0/K(q^n)` is the lower nilpotent line `{X = [[0,0],[y,0]]}` of `A_n`.
- `ψ_β` is trivial on that line if and only if `β_12 = 0`, that is, if `e_2` is an eigenline of `β`.
- `SL_2(F_q)` is transitive on `P^1(F_q)`, so double counting the pairs (β in O, eigenline of β) gives

  ```text
  P(d_1 <= n) = #{β ∈ O : β_12 = 0}/|O| = e(O)/(q+1),
  ```

  where `e(O)` is the number of eigenlines: 2 if split, 1 if non-semisimple, 0 if elliptic.
- `K_1(q^(n-1)) ∩ K(q^(n-1))` maps onto `{X ∈ sl_2 : X_12 = 0}`. Use lifts
  `[[1+q^(n-1)x, 0],[q^(n-1)y, (1+q^(n-1)x)^(-1)]]`.
- A vector fixed by `K_1(q^(n-1))` therefore lies in the sum of the `ψ_β` with
  `β_12 = 0` and `β_11 = β_22`, that is `β ≡ t E_21` modulo scalars.
- Such `β` lie in the non-semisimple orbit and form a subset of the `β_12 = 0` part of it. So:
  - `P(d_1 <= n-1) <= 1/(q+1)`;
  - `P(d_1 <= n-1) = 0` unless `e(O) = 1`.

**Conclusion at depth `n >= 2`.** In every case
`P(d_1 <= n) + P(d_1 <= n-1) <= 2/(q+1)`. Hence `E Φ >= c`, and `(DD2)`
holds because `dim ρ^I = 0`.

## Step 2: depth 1

Now `ρ` is a nontrivial irreducible of `G = SL_2(F_q)`, and `I/K(q)` is the
lower Borel subgroup `B^-`.

**Reducing to two fixed-vector fractions.**
- Every constituent has `d_0 = 1`, and `d_1 ∈ {1,2}` by `(P1)`.
- `K_1(q)` maps onto the lower unipotent subgroup `U^-`, so `Φ(τ) = 0` exactly when `τ` is trivial on `U^-`.
- Write `u = dim ρ^(U^-)/dim ρ` and `t = dim ρ^(B^-)/dim ρ`, and conjugate to the upper Borel `B = TU`.
- `(DD2)` becomes `u + c t <= 2/(q+1)`.

**Two standard formulas.**
- Frobenius reciprocity gives `dim ρ^U = Σ_χ <ρ, Ind_B^G χ>`, summed over the characters `χ` of `T ≅ F_q^×`.
- Mackey's formula over `B\G/B = {1, w}` gives `<Ind χ, Ind χ'> = δ(χ,χ') + δ(χ',χ^(-1))`.

**Case check.**
- `χ^2 ≠ 1`: `Ind χ ≅ Ind χ^(-1)` is irreducible of dimension `q+1`. Then `u = 2/(q+1)` and `t = 0`.
- `Ind 1 = 1 ⊕ St`, where `St` has dimension `q`: `u = t = 1/q`, so `u + ct = (1/q)(2q/(q+1)) = 2/(q+1)`.
- `χ_0` quadratic, `q` odd: `Ind χ_0 = ρ_+ ⊕ ρ_-` with `ρ_+` and `ρ_-` distinct, so `u = 1/dim ρ_±` and `t = 0`.
  - `h = diag(ε,1)` with `ε` a nonsquare normalizes `B` and fixes `χ_0`.
  - `h w h^(-1) = w diag(ε^(-1), ε)`, and `χ_0(ε^(-1)) = -1`.
  - So twisting by `h` negates the intertwiner `A_w` supported on `BwB`.
  - `A_w^2` is scalar and `A_w` is not, so its two eigenspaces `ρ_±` are exchanged.
  - Hence `dim ρ_± = (q+1)/2` and `u = 2/(q+1)`.
- `ρ` cuspidal (`ρ^U = 0`): `u = t = 0`.

In every case `(DD2)` holds, with equality in the first three.

## Step 3: the mirror

`w' = [[0,q],[1,0]] = g·[[0,1],[1,0]]` satisfies `w'^2 = q`, which is central. So:
- conjugation by `w'` swaps `K_0` and `K_1` and normalizes `I`;
- it maps `K(q^a)` to `K_1(q^a)` and back.

For `τ' = τ ∘ Ad(w')` we get `d_0(τ') = d_1(τ)` and `d_1(τ') = d_0(τ)`, so
`Φ(τ') = -Φ(τ)`.

Let `σ` be a nontrivial irreducible of `K_1`, and `ρ = σ ∘ Ad(w')`, an
irreducible of `K_0`, with `t = dim ρ^I/dim ρ`. Using `(DD2)` for `ρ`:

```text
E_(σ|I) f = -(E_(ρ|I) f + c t) - c t <= -c - 2ct <= -c.
```

For the trivial `σ`, `E f = -c`.

## Step 4: the certificate

Decompose `σ_0|_I = M ⊕ R_0` and `σ_1|_I = M ⊕ R_1`, with `M` a maximal
common subrepresentation and `dim R_i = εd`. Then:

- `E_(σ_0) f >= θ_0(-c) + (1-θ_0)c`, by Steps 1 and 2;
- `E_(σ_1) f <= -c`, by Step 3;
- `E_(σ_0) f - E_(σ_1) f = (tr_(R_0) f - tr_(R_1) f)/d <= 2ε`, because `|f| <= 1`.

Hence `2ε >= 2c(1-θ_0)`. Exchanging the roles through `w'` gives the bound
with `θ_1`, which is `(DD1)`.

For `K_i × P`, the irreducibles of `I × P` are `τ ⊗ λ`. Put `f(τ ⊗ λ) = f(τ)`;
every step above is unchanged.

**Machine check.** `depth_drift.py` recomputes `d_0` and `d_1` from the
character tables of `I/K(q^(k+1))`. It asserts
`min_(nontrivial χ) E_0 f >= c` and `max_χ E_1 f <= -c` in exact rationals.
Both bounds are attained, so Steps 1 to 3 are tight. ∎
