---
rg: 2
id: fp-simple-q-algebras-embed-in-fp-simple-rings-proof
kind: route
title: The centre of R_L is Q, so tensoring with R_L moves finite presentation from Q to Z
target: fp-simple-q-algebras-embed-in-fp-simple-rings
requires:
  - leavitt-resolvent-ring-is-fp-simple-of-char-zero
  - fp-simple-ring-of-characteristic-zero-exists
---

Lane proof. Refereed PASS by gq-referee-b
(`gq-referee-b-rational-function-fields-embed-in-fp-simple-rings.md`, which covers this claim), and by
gq-referee-a for parts 1–3 (`gq-referee-a-fp-simple-q-algebras-embed-in-fp-simple-rings.md`; referee a did
not check the Consequence). Trust record: `research/artifacts/gq-gq-fp-simple-rings-char-zero-writeup.md` §6.

## 1. The centre of R_L
Use `R_L ≅ O_ψ`, with base `B = Q[N][(N+c)^(-1)]`, letters `1, 2`, `σ_1(f) = f(N+1)` and
`σ_2(f) = f(0)`, as in `leavitt-resolvent-ring-is-fp-simple-of-char-zero-proof`, §3.
Let `z` be central.
- **Only degree zero.** Each homogeneous component `z_k` commutes with the core `C`,
  which lies in degree `0`. So `z_k = 0` for `k ≠ 0`, by aperiodicity (§5 of that proof).
- **A diagonal element.** At a level `L`, write `z = Σ_(|μ|=|ν|=L) s_μ Z_(μν) t_ν`, with
  `Z` unique by part 1 of `leavitt-nekrashevych-completion-simplicity-criterion`.
  Commuting with the matrix units `s_a t_b` of level `L` forces `Z = w·I` for some `w ∈ B`.
- **A constant.** At level `L + 1` the same element has coefficient matrix
  `diag(σ_1(w), σ_2(w))` on each block, and this must again be scalar. So
  `w(N+1) = σ_1(w) = σ_2(w) = w(0) ∈ Q`, and `w` is a constant `c ∈ Q`.

Hence `z = c ∈ Q`.

## 2. Tensoring with R_L
Let `S = Q<a_1..a_r | f_1..f_l>`, with `f_j ∈ Q<a>` and `S` simple.
- **Simple.** `R_L` is simple with centre `Q` (§1, and
  `leavitt-resolvent-ring-is-fp-simple-of-char-zero`). By the tensor lemma of
  `polynomially-representable-envelopes-via-leavitt-tensors`, §2 (`A` simple and `B`
  simple with centre `K` give `A ⊗_K B` simple; here `K = Q`, `A = S`, `B = R_L`),
  `R_L ⊗_Q S` is simple.
- **Finitely presented over `Z`.** Present it by
  - the generators and relators of `R_L`;
  - generators `a_1..a_r`, each commuting with every generator of `R_L`;
  - the relators `f_j`, where each rational coefficient `p/q` is written as the ring word
    `p·u_q`, with `u_q = t_2 t_1^(q-1) A s_1^(q-1) s_2` the inverse of `q` in `R_L`.

  This ring is `R_L ⊗_Z Z<a> / (f_j)`. Since `R_L` is a `Q`-algebra,
  `R_L ⊗_Z Z<a> = R_L ⊗_Q Q<a>`, and the quotient is `R_L ⊗_Q S` by exactness of
  `R_L ⊗_Q -`.
- **Unital embedding.** `S -> R_L ⊗_Q S` is injective because `R_L ≠ 0` and `Q` is a
  field.

## 3. The equivalence
- **Rings to `Q`-algebras.** Let `A ⊆ R` with `R` a finitely presented simple ring and
  `A ≠ 0` (the case `A = 0` is trivial). Pick a nonzero `a ∈ A`.
  - `R` has characteristic `0`: if `p·1_R = 0` for a prime `p`, then
    `a = p·((1/p)a) = (p·1_R)((1/p)a) = 0`, where `(1/p)a ∈ A` is taken in the
    `Q`-algebra `A`. The centre of
    the simple unital ring `R` is then a field containing `Q`, so `R` is a `Q`-algebra.
  - The two `Q`-structures on `A` agree: `R` is torsion-free, and both `(1/m)a` are the
    unique `x` with `m x = a`.
  - `R` is finitely presented as a `Q`-algebra by the same generators and relators,
    since `R = Q ⊗_Z R`.
- **`Q`-algebras to rings.** If `A ⊆ S` with `S` a finitely presented simple
  `Q`-algebra, then `A ⊆ S ⊆ R_L ⊗_Q S`, by §2. ∎
