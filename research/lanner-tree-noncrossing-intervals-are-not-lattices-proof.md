---
rg: 2
id: lanner-tree-noncrossing-intervals-are-not-lattices-proof
kind: route
title: Lemma D (the wall form of c has positive determinant on the moved space of every noncrossing element) turns an exact bowtie certificate into a missing join, and exact certificates exist for [5,3,3,3], [4,3,3,5], [5,3,3,5], [4,3,5] and [5,3,5]
target: lanner-tree-noncrossing-intervals-are-not-lattices
requires: []
artifacts:
  - experiments/artin-dual-lattice-2026-09-17/bowties_label4.py
  - experiments/artin-dual-lattice-2026-09-17/verify_bowtie_label4.py
  - experiments/artin-dual-lattice-2026-09-17/cert-5333.json
  - experiments/artin-dual-lattice-2026-09-17/cert-5334.json
  - experiments/artin-dual-lattice-2026-09-17/cert-5335.json
  - experiments/artin-dual-lattice-2026-09-17/cert-435.json
  - experiments/artin-dual-lattice-2026-09-17/cert-535.json
  - experiments/artin-dual-lattice-2026-09-17/results-lanner.txt
---

**Verification tier.**
- Sections 1–4 are a complete proof by hand. They hold for every Coxeter system with nondegenerate Tits form and tree
  diagram, and repeat (in condensed form) sections 1–4 of
  [[noncrossing-interval-of-5-3-3-11-is-not-a-lattice-proof]] so that this route stands alone.
- Section 5 consists of exact certificates. `verify_bowtie_label4.py` checks each in exact symbolic arithmetic in
  `Q(√2, √5)` (sympy). It shares no code with the search `bowties_label4.py` that found them.
- Nothing here is refereed.

## 0. Notation and standing facts

- `(W, S)` is a Coxeter system, `S = {s_1, …, s_n}`, `V = R^n` with basis `α_1, …, α_n`, and
  `B(α_i, α_j) = −cos(π/m_ij)` with Gram matrix `G_B`.
- **Standing assumption:** `B` is nondegenerate. The five groups here are compact hyperbolic (Lannér), so `B` has
  signature `(n−1, 1)`.
- `s_β(x) = x − 2B(x, β)β` for a real root `β ∈ Φ = W·{α_i}`, and `T = {s_β : β ∈ Φ}`; `s_β = s_γ` iff `γ = ±β`.
- `ℓ_T` is reflection length. `u ≤_T w` means `ℓ_T(u) + ℓ_T(u^{-1}w) = ℓ_T(w)`, and `[1,c]_W = {w : w ≤_T c}`.
- For `g ∈ O(V, B)`: `Mov(g) = im(1−g)` and `Fix(g) = ker(1−g)`.
- **0.1** `Fix(g) = Mov(g)^⊥`, because `B((1−g)x, y) = B(x, (1−g^{-1})y)` and `ker(1−g^{-1}) = ker(1−g)`.
- **0.2** `Mov(gh) ⊆ Mov(g) + Mov(h)`, because `1 − gh = (1−h) + (1−g)h`. So `dim Mov(w) ≤ ℓ_T(w)`.
- **0.3** `≤_T` is transitive: if `y ≤_T z ≤_T w`, then
  `ℓ_T(y) + ℓ_T(y^{-1}w) ≤ ℓ_T(y) + ℓ_T(y^{-1}z) + ℓ_T(z^{-1}w) = ℓ_T(w)`, and the reverse inequality is
  subadditivity.

## 1. Reflection length and moved spaces below c

**Lemma M0.** For `c = s_1 ⋯ s_n`, `Fix(c) = 0` and `ℓ_T(c) = n`.

*Proof.* If `cx = x`, then `s_2 ⋯ s_n x = s_1 x = x − 2B(x, α_1)α_1`. The left side is `x` modulo
`span(α_2, …, α_n)`, so `B(x, α_1) = 0`, `s_1x = x` and `s_2 ⋯ s_n x = x`. Inductively `B(x, α_i) = 0` for all `i`,
so `x = 0` by nondegeneracy. Then `n = dim Mov(c) ≤ ℓ_T(c) ≤ n` by 0.2. ∎

**Lemma M1.** Let `z ≤_T u ≤_T c`. Then (i) `ℓ_T(z) = dim Mov(z)`; (ii) `Mov(u) = Mov(z) ⊕ Mov(z^{-1}u)`; (iii) if
`ℓ_T(z) = ℓ_T(u)` then `z = u`.

*Proof.* With `k_1 = z^{-1}u`, `k_2 = u^{-1}c` we have `c = z k_1 k_2` and `ℓ_T(z) + ℓ_T(k_1) + ℓ_T(k_2) = n`. By
0.2 and M0, `n = dim Mov(c) ≤ dim Mov(z) + dim Mov(k_1) + dim Mov(k_2) ≤ n`, so each `dim Mov` equals the
corresponding `ℓ_T`; the same applied to `c = u (u^{-1}c)` gives (i) for `u`. Then
`dim Mov(u) = dim Mov(z) + dim Mov(k_1)` together with `Mov(u) ⊆ Mov(z) + Mov(k_1)` gives (ii). For (iii),
`ℓ_T(z^{-1}u) = 0`. ∎

**Subword lemma.** Let `w = t_1 ⋯ t_m` with `t_i ∈ T` and `ℓ_T(w) = m`, let `S = {i_1 < ⋯ < i_k}` and
`p = t_{i_1} ⋯ t_{i_k}`. Then `p ≤_T w`, `ℓ_T(p) = k`, and `t_i ≤_T p` for every `i ∈ S`.

*Proof.* If `j ∉ S` directly precedes `i ∈ S`, rewrite `t_j t_i = t_i (t_i t_j t_i)`. Repeating gives
`w = p · t'_1 ⋯ t'_{m−k}` with `t'_r ∈ T`, so `ℓ_T(p) ≤ k` and `ℓ_T(p^{-1}w) ≤ m − k`; their sum is at least `m`, so
both are equalities. Applying this to the factorization of `p` and `S = {i}` gives `t_i ≤_T p`. ∎

## 2. The wall form and Lemma D

For `g ∈ O(V, B)` define `χ_g` on `Mov(g)` by `χ_g(u, v) = B(x, v)` for `u = (1−g)x`. It is well defined by 0.1.

**Lemma M2.** (a) `χ_g(u, u) = B(u, u)/2`. (b) If `h = gk` with `Mov(h) = Mov(g) ⊕ Mov(k)`, then
`χ_h|Mov(g) = χ_g` and `χ_h(u, v) = 0` for `u ∈ Mov(g)`, `v ∈ Mov(k)`. (c) If `Fix(c) = 0`, then
`χ_c(u, v) = B((1−c)^{-1}u, v)`.

*Proof.* (a) `B(u, u) = 2B(x, x) − 2B(x, gx) = 2B(x, u)`. (b) For `u = (1−h)x = (1−k)x + (1−g)kx ∈ Mov(g)`, the
first summand lies in `Mov(k)` and the second in `Mov(g)`, so directness gives `(1−k)x = 0`, `kx = x` and
`u = (1−g)x`; hence `χ_h(u, v) = B(x, v) = χ_g(u, v)` for `v ∈ Mov(g)`, and for `v ∈ Mov(k)` we get `B(x, v) = 0`
since `x ∈ Fix(k) = Mov(k)^⊥`. (c) is the definition. ∎

**Lemma D.** Let `z ∈ [1,c]_W` have rank `k` and let `e_1, …, e_k` be any basis of `Mov(z)`. Then
`det[χ_c(e_i, e_j)] > 0`.

*Proof.* By M1 and M2(b) (with `h = c`, `g = z`, `k = z^{-1}c`), `χ_c|Mov(z) = χ_z`. A change of basis multiplies the
determinant by a square, so the sign is basis-independent. Induct on `k` (for `k = 0` there is nothing to prove).
Write `z = t_1 ⋯ t_k` with `t_i = s_{β_i}` and put `y = t_1 ⋯ t_{k−1}`. By the subword lemma and 0.3, `y ∈ [1,c]_W`
has rank `k−1`, and by M1(ii) `Mov(z) = Mov(y) ⊕ Rβ_k`. By M2(b) (with `h = z`, `g = y`, `k = t_k`) the matrix of
`χ_z` in a basis of `Mov(y)` followed by `β_k` is block triangular with diagonal blocks `χ_y` and
`χ_z(β_k, β_k) = 1/2` (M2(a)). So `det χ_z = det χ_y / 2 > 0`. ∎

In coordinates (M2(c)), `E^T G_B (1−c)^{-1} E` is the transpose of `[χ_c(e_i, e_j)]` for the `n × k` matrix `E` of
a basis of `Mov(z)`; this is what the scripts compute.

## 3. The certificate criterion

**Proposition.** Suppose `a ≠ b` are reflections with roots `α_a, α_b`, `p ≠ q` are rank-3 elements of `[1,c]_W` with
`a, b ≤_T p` and `a, b ≤_T q`, and `det(E^T G_B (1−c)^{-1} E) ≤ 0` for `E = [α_a, α_b]`. Then `a` and `b` have no
join in `[1,c]_W`, so `[1,c]_W` is not a lattice.

*Proof.* Suppose `z = a ∨ b` exists. Then `z ≤_T p, q`, so `rank z ≤ 3`. Rank 3 gives `z = p = q` by M1(iii), and
rank 1 gives `a = z = b`, both contradictions; `z ≠ 1` since `a ≤_T z`. So `rank z = 2`, and by M1(ii) `α_a, α_b ∈
Mov(z)`. They are independent, since `α_b = λα_a` with both of `B`-norm 1 forces `λ = ±1` and `a = b`. Hence
`Mov(z) = span(α_a, α_b)`, and Lemma D contradicts the hypothesis. ∎

**Remark.** On `span(α_a, α_b)` the matrix of `χ_c` is `S + K`, with `S` the Gram matrix of `B/2` and `K`
antisymmetric (M2(a) polarized gives `χ + χ^T = B`). For `2 × 2` matrices `det(S + K) = det S + κ^2`, so the criterion
needs `|B(α_a, α_b)| > 1` and never fires for spherical `W`, in agreement with Bessis and Brady–Watt.

## 4. All Coxeter elements

For a tree diagram all Coxeter elements are conjugate in `W`: moving the first letter of `s_{σ(1)} ⋯ s_{σ(n)}` to the
end conjugates by a generator and turns a source of the associated orientation into a sink, and any two orientations
of a tree are related by such moves (see H. Eriksson and K. Eriksson, *Conjugacy of Coxeter elements*, Electron. J.
Combin. 16(2) (2009)). Conjugation preserves `T` and `ℓ_T`, so it is a poset isomorphism
`[1,c]_W → [1, wcw^{-1}]_W`. It suffices to treat `c = s_1 ⋯ s_n`.

## 5. The certificates

- Nodes are numbered along the path, `s_1 −m_1− s_2 −m_2− ⋯`, as in the claim. Coordinates are in the simple-root
  basis, with `φ = (1+√5)/2`. So `B(α_i, α_{i+1})` is `−1/2`, `−√2/2` or `−φ/2` for label 3, 4 or 5.
- A witness is a factorization `c = s_{β_1} ⋯ s_{β_n}` into reflections together with a 3-element set `S` of positions.
  Its length is `n = ℓ_T(c)` (M0), so by the subword lemma the subword product over `S` is a rank-3 element of
  `[1,c]_W`, and each of its letters lies below it.
- Each certificate has four witnesses. The two `p`-witnesses have the same subword product `p` and contain `α_a` and
  `α_b` respectively; likewise for `q`; and `p ≠ q`. The full factorizations are in `cert-<group>.json`.
- `verify_bowtie_label4.py` checks, in exact arithmetic:
  - every `β_i` is a real root: `B(β, β) = 1`, and root descent by simple reflections reaches a simple root;
  - each factorization multiplies to `c`;
  - the letters `α_a`, `α_b` occur in the subwords as stated;
  - the two `p`-subwords agree, the two `q`-subwords agree, and `p ≠ q` (also checked numerically to 50 digits, so it
    does not rest on a failed simplification);
  - the value of `det(E^T G_B (1−c)^{-1} E)` for `E = [α_a, α_b]`.

| Group | `α_a` | `α_b` | `B(α_a, α_b)` | `det χ_c` on `span(α_a, α_b)` |
|---|---|---|---|---|
| `[5,3,3,3]` | `(1+φ)α_1 + 2φα_2 + φα_3 + φα_4 + φα_5` | `(1+φ)α_1 + 2φα_2 + 2φα_3 + φα_4` | `−φ` | `−φ/4` |
| `[5,3,3,4]` | `φα_1 + (1+φ)α_2 + φα_3 + φα_4` | `(1+φ)α_1 + 2φα_2 + φα_3 + φα_4 + φ√2 α_5` | `−(5+√5)/4` | `−φ/4` |
| `[5,3,3,5]` | `φα_1 + (1+φ)α_2 + φα_3 + (1+2φ)α_4 + (1+φ)α_5` | `(1+φ)α_1 + 2φα_2 + φα_3 + φα_4 + (1+φ)α_5` | `−φ^2` | `−φ/2` |
| `[4,3,5]` | `φα_2 + (1+φ)α_3 + φα_4` | `φ√2 α_1 + φα_2 + 2φα_3 + (1+φ)α_4` | `−(5+√5)/4` | `−φ/4` |
| `[5,3,5]` | `φα_2 + (1+φ)α_3 + φα_4` | `(1+φ)α_1 + φα_2 + 2φα_3 + (1+φ)α_4` | `−φ^2` | `−φ/2` |

(`[5,3,3,4]` is `[4,3,3,5]` with the nodes read in the opposite order; `c` is taken as `s_1 ⋯ s_5` in the order
`5, 3, 3, 4`. By Section 4 the choice of Coxeter element does not matter.)

**Witnesses for `[5,3,3,3]`** (positions numbered from 1):

| Witness | `β_1` | `β_2` | `β_3` | `β_4` | `β_5` | `S` |
|---|---|---|---|---|---|---|
| p1 | `α_5` | `φ(α_1+α_2+α_3+α_4+α_5)` | `φα_1 + (1+φ)α_2 + α_3 + α_4 + α_5` | `α_a` | `α_3` | `{1,4,5}` |
| p2 | `α_3` | `φ(α_1+α_2+α_3+α_4)` | `φα_1 + (1+φ)α_2 + (1+φ)α_3 + α_4` | `α_b` | `α_5` | `{1,4,5}` |
| q1 | `φ(α_1+α_2+α_3+α_4)` | `φα_1 + (1+φ)α_2 + α_3 + α_4 + α_5` | `α_a` | `φα_1 + (1+φ)α_2 + (1+φ)α_3 + α_4` | `(1+φ)α_1 + (1+2φ)α_2 + 2φα_3 + φα_4` | `{2,3,5}` |
| q2 | `φ(α_1+α_2+α_3+α_4)` | `φα_1 + α_2 + α_3 + α_4 + α_5` | `φα_1 + (1+φ)α_2 + (1+φ)α_3 + α_4` | `α_b` | `α_2` | `{2,4,5}` |

So `p = s_{α_5} s_{α_a} s_{α_3} = s_{α_3} s_{α_b} s_{α_5}`, and `q` is the product of the q1-subword, which equals the
product of the q2-subword; the verifier checks both equalities.

**Reproduction** (from `experiments/artin-dual-lattice-2026-09-17/`, single-threaded, each search under 70 seconds, the
full log is `results-lanner.txt`):

```sh
CERT_OUT=cert-5333.json python3 bowties_label4.py 5333 13 13 && python3 verify_bowtie_label4.py cert-5333.json
CERT_OUT=cert-5334.json python3 bowties_label4.py 5334 12 13 && python3 verify_bowtie_label4.py cert-5334.json
CERT_OUT=cert-5335.json python3 bowties_label4.py 5335 13 13 && python3 verify_bowtie_label4.py cert-5335.json
CERT_OUT=cert-435.json  python3 bowties_label4.py 435 11 13  && python3 verify_bowtie_label4.py cert-435.json
CERT_OUT=cert-535.json  python3 bowties_label4.py 535 13 13  && python3 verify_bowtie_label4.py cert-535.json
```

**Calibration.**
- The spherical groups `B_4`, `F_4` (height 8) and `B_5` (height 6) give 0 candidates, as the remark in Section 3
  forces.
- The verifier rejects an uncertified candidate: `CONTROL=1` dumps an `F_4` pair, and the verifier prints `det = 1/4`,
  NOT CERTIFIED, and exits 1.
- Smaller height bounds found nothing (`[5,3,3,3]` at 9, `[5,3,3,4]` at 10, `[5,3,3,5]` at 11, `[4,3,5]` at 8). The
  bowties only appear once roots of height 11–13 are allowed.

## 6. What this does and does not settle

- **Settled.** For every Coxeter element `c` of each of the five groups, `[1,c]_W` is not a lattice: the reflections
  `a`, `b` above have no join. With [[noncrossing-interval-of-5-3-3-11-is-not-a-lattice]] this covers all four rank-5
  compact hyperbolic tree groups `[5,3,3,3]`, `[4,3,3,5]`, `[5,3,3,5]`, `[5,3,3^{1,1}]` and all four rank-4 compact
  hyperbolic tree groups `[3,5,3]`, `[5,3^{1,1}]`, `[4,3,5]`, `[5,3,5]`.
- **Consequence.** The dual Garside route to K(π,1) (Bessis; Brady–Watt; Paolini–Salvetti through McCammond–Sulway)
  starts from a Garside structure on the interval group of `[1,c]_W`, which needs `[1,c]_W` to be a lattice. That step
  is false for every compact hyperbolic 4-simplex tree group, for every Coxeter element.
- **Not settled.**
  - The cyclic Lannér diagrams, where Coxeter elements are not all conjugate. The rank-5 cyclic group `(3,3,3,3,4)` is
    already covered for K(π,1) by Huang.
  - Whether some lattice enlargement of `[1,c]_W`, in the style of McCammond–Sulway, exists for these groups.
  - The K(π,1) conjecture itself for any of these groups.
