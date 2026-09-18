---
rg: 2
id: noncrossing-interval-of-5-3-3-11-is-not-a-lattice-proof
kind: route
title: The wall form of c restricted to the moved space of any rank-2 noncrossing element has positive determinant, and an exact certificate gives two reflections below two rank-3 elements whose span has negative determinant
target: noncrossing-interval-of-5-3-3-11-is-not-a-lattice
requires: []
artifacts:
  - experiments/artin-dual-lattice-2026-09-17/verify_bowtie.py
  - experiments/artin-dual-lattice-2026-09-17/rank3_bowties.py
  - experiments/artin-dual-lattice-2026-09-17/lattice_bowties.py
  - experiments/artin-dual-lattice-2026-09-17/cert-53311.json
  - experiments/artin-dual-lattice-2026-09-17/cert-353.json
  - experiments/artin-dual-lattice-2026-09-17/cert-5311.json
  - experiments/artin-dual-lattice-2026-09-17/results.txt
---

**Verification tier.**
- Sections 1–4 are a complete proof by hand.
- Section 5 is an exact certificate. It is checked in exact arithmetic in `Q(√5)` by `verify_bowtie.py`
  (sympy). The verifier shares no code with the search that found the certificate.
- Nothing here is refereed.

## 0. Notation

- `(W, S)` is a Coxeter system, `S = {s_1, …, s_n}`, `V = R^n` with basis `α_1, …, α_n`, and
  `B(α_i, α_j) = −cos(π/m_ij)`.
- **Standing assumption:** `B` is nondegenerate. This holds for the three groups of the claim, which are compact
  hyperbolic, so `B` has signature `(n−1, 1)`.
- `s_i(x) = x − 2B(x, α_i)α_i`, and `W ⊂ O(V, B)`.
- Real roots `Φ = W·{α_i}`. Each `β ∈ Φ` has `B(β, β) = 1`, and `s_β(x) = x − 2B(x, β)β` is the reflection
  `w s_i w^{-1}` when `β = wα_i`.
- `T = {s_β}` is the set of reflections. Every `t ∈ T` is `s_β` for exactly the two roots `±β`.
- `ℓ_T` is reflection length. `u ≤_T w` means `ℓ_T(u) + ℓ_T(u^{-1}w) = ℓ_T(w)`, and `[1,c]_W = {w : w ≤_T c}`.
- For `g ∈ O(V, B)`: `Mov(g) = im(1−g)` and `Fix(g) = ker(1−g)`.
- **Fact 0.1.** `Fix(g) = Mov(g)^⊥`.
  - Proof: `B((1−g)x, y) = B(x, (1−g^{-1})y)`, and `ker(1−g^{-1}) = ker(1−g)`.
- **Fact 0.2.** `Mov(gh) ⊆ Mov(g) + Mov(h)`.
  - Proof: `1 − gh = (1−h) + (1−g)h`. Hence `dim Mov(w) ≤ ℓ_T(w)` for `w ∈ W`, since `Mov(s_β) = Rβ`.
- **Fact 0.3.** `≤_T` is transitive.
  - Proof: if `y ≤_T z ≤_T w`, then `ℓ_T(y) + ℓ_T(y^{-1}w) ≤ ℓ_T(y) + ℓ_T(y^{-1}z) + ℓ_T(z^{-1}w) = ℓ_T(w)`, and
    the reverse inequality is subadditivity of `ℓ_T`.

## 1. The reflection length of c and moved spaces

**Lemma M0.** For `c = s_1 ⋯ s_n`, `Fix(c) = 0`, so `dim Mov(c) = n = ℓ_T(c)`.

*Proof.*
1. Let `cx = x`. Then `s_2 ⋯ s_n x = s_1 x = x − 2B(x, α_1)α_1`.
2. The left side is `x` modulo `span(α_2, …, α_n)`. The simple roots are linearly independent, so `B(x, α_1) = 0`.
   Then `s_1 x = x` and `s_2 ⋯ s_n x = x`.
3. Inductively `B(x, α_i) = 0` for all `i`, so `x = 0` because `B` is nondegenerate.
4. So `n = dim Mov(c) ≤ ℓ_T(c) ≤ n` (Fact 0.2). ∎

**Lemma M1.** Let `z ≤_T u ≤_T c`.
- (i) `ℓ_T(z) = dim Mov(z)`.
- (ii) `Mov(u) = Mov(z) ⊕ Mov(z^{-1}u)`. In particular `Mov(z) ⊆ Mov(u)`.
- (iii) If `ℓ_T(z) = ℓ_T(u)`, then `z = u`.

*Proof.*
1. Put `k_1 = z^{-1}u` and `k_2 = u^{-1}c`. Then `c = z k_1 k_2` and `ℓ_T(z) + ℓ_T(k_1) + ℓ_T(k_2) = n`.
2. By Fact 0.2 and Lemma M0, `n = dim Mov(c) ≤ dim Mov(z) + dim Mov(k_1) + dim Mov(k_2) ≤ n`. So each
   `dim Mov` equals the corresponding `ℓ_T`.
3. The same argument applied to `c = z (z^{-1}c)` gives (i) for every element of `[1,c]_W`. In particular it holds
   for `u`.
4. Then `dim Mov(u) = ℓ_T(u) = ℓ_T(z) + ℓ_T(k_1) = dim Mov(z) + dim Mov(k_1)`. With `Mov(u) ⊆ Mov(z) + Mov(k_1)`,
   this gives (ii).
5. For (iii), `ℓ_T(z^{-1}u) = 0`. ∎

**Subword lemma.** Let `w = t_1 ⋯ t_m` with `t_i ∈ T` and `ℓ_T(w) = m`, and let `S = {i_1 < ⋯ < i_k}`. Put
`p = t_{i_1} ⋯ t_{i_k}`. Then `p ≤_T w`, `ℓ_T(p) = k`, and `t_i ≤_T p` for every `i ∈ S`. (For `w = c` and `m = n`,
Lemma M0 supplies `ℓ_T(c) = n`.)

*Proof.*
1. If `j ∉ S` directly precedes `i ∈ S`, rewrite `t_j t_i = t_i (t_i t_j t_i)`. The letter `t_i` moves left
   unchanged, and `t_j` is replaced by a reflection.
2. Repeating this gives `w = p · t'_1 ⋯ t'_{m−k}` with `t'_r ∈ T`.
3. So `ℓ_T(p) ≤ k` and `ℓ_T(p^{-1}w) ≤ m−k`. Their sum is at least `ℓ_T(w) = m`, so both are equalities and
   `p ≤_T w`.
4. The same argument applied to the length-`k` factorization of `p` and `S = {i}` gives `t_i ≤_T p`. ∎

## 2. The wall form

For `g ∈ O(V, B)` define `χ_g` on `Mov(g)` by `χ_g(u, v) = B(x, v)`, where `u = (1−g)x`. This is well defined by
Fact 0.1: changing `x` by an element of `Fix(g)` does not change `B(x, v)` for `v ∈ Mov(g)`.

**Lemma M2.**
- (a) `χ_g(u, u) = B(u, u)/2`. In particular `χ_{s_β}(β, β) = 1/2`.
- (b) Let `h = g k` with `Mov(h) = Mov(g) ⊕ Mov(k)`. Then `χ_h|Mov(g) = χ_g`, and `χ_h(u, v) = 0` for `u ∈ Mov(g)`
  and `v ∈ Mov(k)`.
- (c) If `Fix(c) = 0`, then `χ_c(u, v) = B((1−c)^{-1}u, v)`.

*Proof.*
- (a) `B(u, u) = B(x−gx, x−gx) = 2B(x, x) − 2B(x, gx) = 2B(x, u)`.
- (b)
  1. Let `u ∈ Mov(g)` and `u = (1−h)x = (1−k)x + (1−g)kx`.
  2. The first summand lies in `Mov(k)` and the second in `Mov(g)`. Since the sum is direct, `(1−k)x = 0`.
  3. So `kx = x` and `u = (1−g)x`. Hence `χ_h(u, v) = B(x, v) = χ_g(u, v)` for `v ∈ Mov(g)`.
  4. For `v ∈ Mov(k)`, `x ∈ Fix(k) = Mov(k)^⊥`, so `B(x, v) = 0`.
- (c) is the definition. ∎

**Lemma D.** Let `z ∈ [1,c]_W` have rank `k`, and let `e_1, …, e_k` be any basis of `Mov(z)`. Then
`det[χ_c(e_i, e_j)] > 0`.

*Proof.*
1. By Lemma M1 (with `u = c`) and Lemma M2(b) (with `h = c`, `g = z`, `k = z^{-1}c`), `χ_c|Mov(z) = χ_z`. So it
   suffices to show `det[χ_z(e_i, e_j)] > 0`.
2. The sign of the determinant does not depend on the basis: a change of basis `P` multiplies it by `det(P)^2`.
3. Induct on `k`; for `k = 0` there is nothing to prove.
4. Write `z = t_1 ⋯ t_k` with `t_i = s_{β_i}` and `k = ℓ_T(z)`. Put `y = t_1 ⋯ t_{k−1}`. By the subword lemma,
   `y ≤_T z`, so `y ≤_T c` by Fact 0.3, and `rank y = k−1`.
5. By Lemma M1(ii), `Mov(z) = Mov(y) ⊕ Rβ_k`.
6. By Lemma M2(b) (with `h = z`, `g = y`, `k = t_k`), `χ_z|Mov(y) = χ_y` and `χ_z(Mov(y), β_k) = 0`.
7. In a basis of `Mov(y)` followed by `β_k`, the matrix `[χ_z(e_i, e_j)]` is block triangular, with diagonal blocks
   `[χ_y]` and `χ_z(β_k, β_k) = 1/2` (Lemma M2(a)).
8. So `det χ_z = det χ_y / 2 > 0` by induction. ∎

**Matrix form.**
- Take coordinates in the simple-root basis, with `G_B` the Gram matrix of `B` and `E` the `n × k` matrix of a
  basis of `Mov(z)`.
- By M2(c), `E^T G_B (1−c)^{-1} E` is the transpose of `[χ_c(e_i, e_j)]`, so it has the same determinant.
- This is the quantity the scripts compute.

## 3. The certificate criterion

**Proposition.** Suppose:
- `a ≠ b` are reflections in `[1,c]_W`, with roots `α_a` and `α_b`;
- `p ≠ q` are rank-3 elements of `[1,c]_W` with `a, b ≤_T p` and `a, b ≤_T q`;
- `det(E^T G_B (1−c)^{-1} E) ≤ 0` for `E = [α_a, α_b]`.

Then `a` and `b` have no join in `[1,c]_W`, so `[1,c]_W` is not a lattice.

*Proof.*
1. Suppose `z = a ∨ b` exists. Then `z ≤_T p` and `z ≤_T q`, so `rank z ≤ 3`.
2. If `rank z = 3`, Lemma M1(iii) gives `z = p` and `z = q`, a contradiction.
3. If `rank z = 1`, then `z` is a reflection and `a = z = b` by M1(iii), a contradiction. And `z ≠ 1`, since
   `a ≤_T z`.
4. So `rank z = 2`. By M1(ii), `Rα_a` and `Rα_b` lie in `Mov(z)`.
5. `α_a` and `α_b` are independent: `α_b = λα_a` with `B(α_b, α_b) = B(α_a, α_a) = 1` forces `λ = ±1`, so
   `a = b`. Hence `Mov(z) = span(α_a, α_b)`.
6. Lemma D gives `det(E^T G_B (1−c)^{-1} E) > 0`, contradicting the hypothesis. ∎

**Remarks.**
- The criterion never fires for spherical `W`.
  - On `span(α_a, α_b)` the matrix of `χ_c` is `S + K`. Here `S` is the Gram matrix of `B/2` on the span, which is
    positive definite, and `K = [[0, κ], [−κ, 0]]` is antisymmetric (Lemma M2(a) polarized: `χ + χ^T = B`).
  - For a `2 × 2` matrix, `det(S + K) = det S + κ^2 > 0`.
  - This agrees with the lattice theorem of Bessis and Brady–Watt.
- The criterion also cannot fire in rank 3, where `c` is the only rank-3 element. This agrees with
  arXiv:2206.14518.
- It needs `B` to be indefinite on `span(α_a, α_b)`, that is `|B(α_a, α_b)| > 1`.

## 4. All Coxeter elements

- For a tree diagram all Coxeter elements are conjugate in `W`. This is classical: moving the first letter to the
  end conjugates by a generator and turns a source of the orientation into a sink, and any two orientations of a
  tree are related by such moves. See e.g. H. Eriksson and K. Eriksson, *Conjugacy of Coxeter elements*, Electron.
  J. Combin. 16(2) (2009).
- Conjugation by `w ∈ W` preserves `T` and `ℓ_T`, so it is a poset isomorphism `[1,c]_W → [1, wcw^{-1}]_W`.
- So it suffices to treat `c = s_1 ⋯ s_n`.

## 5. The certificates

- Coordinates are in the simple-root basis, with `φ = (1+√5)/2`, and the nodes are numbered as in the claim.
- Each witness is a factorization `c = s_{β_1} ⋯ s_{β_n}` into reflections, with a 3-element subset `S` of positions.
- Its length is `n = ℓ_T(c)`, so the subword lemma applies.

**`[5,3,3^{1,1}]`**
- Edges: `(1,2)` label 5; `(2,3)`, `(3,4)`, `(3,5)` label 3.
- The roots are `α_a = α_1 + φα_2 + φα_3 + φα_5` and `α_b = α_1 + φα_2 + φα_3 + φα_4`. `B(α_a, α_b) = −φ`.
- Four length-5 factorizations of `c`, all with `S` as shown:

| Witness | `β_1` | `β_2` | `β_3` | `β_4` | `β_5` | `S` | Subword |
|---|---|---|---|---|---|---|---|
| p1 | `α_5` | `α_3+α_5` | `α_2+α_3+α_5` | `α_a` | `α_4` | `{1,4,5}` | `p = s_{α_5} s_{α_a} s_{α_4}` |
| p2 | `α_4` | `α_3+α_4` | `α_2+α_3+α_4` | `α_b` | `α_5` | `{1,4,5}` | `p = s_{α_4} s_{α_b} s_{α_5}` |
| q1 | `α_3` | `α_2+α_3+α_5` | `α_a` | `α_4` | `α_2+α_3+α_4` | `{2,3,5}` | `q = s_{α_2+α_3+α_5} s_{α_a} s_{α_2+α_3+α_4}` |
| q2 | `α_3` | `α_2+α_3+α_4` | `α_b` | `α_5` | `α_2+α_3+α_5` | `{2,3,5}` | `q = s_{α_2+α_3+α_4} s_{α_b} s_{α_2+α_3+α_5}` |

- The verifier checks:
  - every `β_i` is a real root: `B(β, β) = 1`, and root descent reaches a simple root;
  - each product equals `c`;
  - the two `p`-subwords agree, and so do the two `q`-subwords;
  - `α_a` lies in the p1 and q1 subwords, and `α_b` in the p2 and q2 subwords;
  - `p ≠ q`.
- The form matrix is `E^T G_B (1−c)^{-1} E = [[1/2, −φ/2], [−φ/2, 1/2]]`, with determinant `(1 − φ^2)/4 = −φ/4 < 0`.
- By Section 3, `[1,c]_W` is not a lattice.
- The diagram automorphism swapping `s_4 ↔ s_5` fixes `c` (since `s_4 s_5 = s_5 s_4`), exchanges `α_a ↔ α_b`, and
  fixes `p` and `q`.

**`[3,5,3]` and `[5,3^{1,1}]`**
- The full factorizations are in `cert-353.json` and `cert-5311.json`.
- `[3,5,3]`: `α_a = φ^2α_2 + φ^2α_3 + φα_4` and `α_b = φα_1 + φα_2 + φ^2α_3 + φα_4`.
- `[5,3^{1,1}]`: `α_a = φα_1 + φ^2α_2 + α_3 + φ^2α_4` and `α_b = φα_1 + φ^2α_2 + φ^2α_3 + α_4`.
- In both, `B(α_a, α_b) = −φ` and the form matrix is again `[[1/2, −φ/2], [−φ/2, 1/2]]`, with determinant `−φ/4`.

**Reproduction** (from `experiments/artin-dual-lattice-2026-09-17/`, single-threaded; each run takes under a minute):

```sh
python3 verify_bowtie.py cert-53311.json     # prints CERTIFIED
python3 verify_bowtie.py cert-353.json
python3 verify_bowtie.py cert-5311.json
CERT_OUT=cert-53311.json python3 rank3_bowties.py 53311 7   # regenerates the search
```

**Calibration.**
- The same search with the same criterion finds no certificate for the spherical groups `A_4, D_4, H_4, A_5, D_5`.
  This is forced by the remark in Section 3.
- The verifier rejects a non-certified candidate: `CONTROL=1 CERT_OUT=ctrl.json rank3_bowties.py H4 6`, then
  `verify_bowtie.py ctrl.json` prints `det = 1/4`, NOT CERTIFIED, and exits 1.
- On every run the search's second exclusion test agrees exactly with the determinant sign. That test checks whether
  `s_a z_U2` is a reflection, with `z_U2` given by the formula `g = 1 − E M^{-1} E^T G_B` for `g ≤ c` with `Mov(g) = U`.
- The search logs are in `results.txt`.

## 6. What this does and does not settle

- **Settled.** For `[5,3,3^{1,1}]` (and for the rank-4 groups `[3,5,3]`, `[5,3^{1,1}]`) the lattice step of the dual
  Garside approach fails, for every Coxeter element.
- **Not settled.**
  - Here, the lattice question for `[5,3,3,3]`, `[5,3,3,5]`, `[4,3,3,5]`, `[4,3,5]` and `[5,3,5]`. It is settled (not a
    lattice) with the same criterion and larger certificates in
    [[lanner-tree-noncrossing-intervals-are-not-lattices-proof]].
  - Whether a lattice enlargement in the style of McCammond–Sulway exists for `[5,3,3^{1,1}]`.
  - The K(π,1) conjecture itself for any of these groups.
