---
rg: 2
id: kt-kernel-overgroups-polynomial-via-vertex-compressors-proof
kind: route
title: Compressors whose rows share one Newton-polytope vertex turn every column into a monomial times a unimodular vector, which forces polynomial transvections
target: kt-compressor-stable-kernel-overgroups-are-polynomial
requires:
  - kt-kernel-overgroup-reduces-to-rank-one-transvections
artifacts:
  - experiments/kt-vertex-compressors-2026-09-17/vertex_compressor_check.py
  - experiments/kt-vertex-compressors-2026-09-17/run-25-seed7.txt
---

Notation as in the target. `A = F_q[x_1,…,x_d] ⊂ R = F_q[x_1^(±1),…,x_d^(±1)]`, `r ≥ 3`,
`d ≥ 1`. `P ∈ Mon = SL_d(Z) ∩ M_d(N)` acts by the ring automorphism `x^m ↦ x^(Pm)` of `R`,
entrywise on matrices. `SL_r(A) ≤ H ≤ SL_r(R)`, `P·H ≤ H` for `P ∈ Mon`, and
`H ∩ U_12(R) = U_12(A)`. Conjugating by signed permutation matrices in `SL_r(A)` gives
`H ∩ U_ij(R) = U_ij(A)` for all `i ≠ j`. For `f = Σ c_m x^m ∈ R`, `supp f = {m : c_m ≠ 0}`.
Since `P` is a bijection of `Z^d`, `supp(P·f) = P·supp f`: compressors never cancel
monomials.

The previous attempt (`kt-kernel-overgroup-rank-one-transvections-proof` §4) used
compressors chosen for one column shape, `I + kE_21`. Their certified exponent cone
`∩ P^(-1)(N^d)` was larger than `N^d`. Here the compressor is chosen *after* the column,
from the normal fan of the column's Newton polytope. Then one compressor, with all rows
close to a coordinate vector, does both jobs at once: it makes the column unimodular, and it
detects the bad exponent.

## 1. Vertex-cone lemma

**Lemma 1.** Let `u ∈ R^r` be unimodular over `R` and `S = ∪_k supp u_k ≠ ∅`. Let
`P ∈ SL_d(Z)` have rows `ρ_1,…,ρ_d`, and let `m* ∈ S` be the unique minimizer of every
`ρ_i` on `S`:

```text
⟨ρ_i, m*⟩ < ⟨ρ_i, m⟩     for all i and all m ∈ S ∖ {m*}.
```

Then `w := x^(−P m*)·(P·u)` lies in `A^r` and is unimodular over `A`.

*Proof.* `w_k = Σ_(m ∈ supp u_k) c_(k,m) x^(P(m − m*))`, and `(P(m − m*))_i = ⟨ρ_i, m − m*⟩ ≥ 0`,
so `w ∈ A^r`. By the Nullstellensatz it suffices that the entries of `w` have no common zero
`t ∈ F̄_q^d`.

* If every `t_i ≠ 0`, then `t` lies in the torus. `P·u` is `R`-unimodular, because `P` is a
  ring automorphism of `R`. So `(P·u)(t) ≠ 0`, and `x^(−Pm*)` is a unit at `t`.
* If `t_i = 0` for some `i`, then for `m ≠ m*` the monomial `x^(P(m − m*))` contains
  `x_i^(⟨ρ_i, m−m*⟩)` with a positive exponent, so it vanishes at `t`. The monomial for
  `m = m*` is `1`. Hence `w(t) = (c_(k,m*))_k`, which is nonzero because `m* ∈ S`. ∎

**Lemma 2.** Let `S ⊂ Z^d` be finite and nonempty, `m ∈ Z^d` with `m_(i0) < 0`. There is a
`P ∈ Mon` and an `m* ∈ S` such that `m*` is the unique minimizer on `S` of every row of `P`,
and every row `ρ` of `P` has `⟨ρ, m⟩ < 0`.

*Proof.* Let `0 < ε < 1/|m|` and
`V = {ρ ∈ R^d_(>0) : |ρ/|ρ| − e_(i0)| < ε}`, an open cone. On `V`,
`⟨ρ, m⟩ = |ρ|(m_(i0) + ⟨ρ/|ρ| − e_(i0), m⟩) < |ρ|(−1 + ε|m|) < 0`. The set of `ρ` with a non-unique
minimizer on `S` is contained in the finite union of the hyperplanes `⟨ρ, m' − m''⟩ = 0`
(`m' ≠ m'' ∈ S`). So some `ρ_0 ∈ V` has a unique minimizer `m*`. The set
`C = {ρ ∈ V : m* is the unique minimizer of ρ on S}` is an open cone (finitely many strict
inequalities) and contains `ρ_0`. Rational directions are dense, so `C` contains a
primitive integer vector `w`. Extend `w` to a basis `w, b_2,…,b_d` of `Z^d` with
`det(w, b_2,…,b_d) = 1` (change the sign of `b_2` if needed). For `N ≥ 1` the rows
`w, b_2 + Nw, …, b_d + Nw` also have determinant `1`. Since `(b_k + Nw)/N → w ∈ C` and `C` is an
open cone, all rows lie in `C` for `N` large. They are integer vectors in `R^d_(>0)`, so
`P ∈ SL_d(Z) ∩ M_d(N) = Mon`. ∎

## 2. Every conjugated transvection is polynomial

Let `h ∈ H`, `i ≠ j`, `T = h e_ij(1) h^(-1) = I + Y`, `Y = u v^T`, `u = h e_i`,
`v^T = e_j^T h^(-1)`, `v^T u = 0`. The column `u` is `R`-unimodular, being a column of
`h ∈ SL_r(R)`.

**Claim.** `Y ∈ M_r(A)`.

Suppose not. Then some entry of `Y` has a monomial `x^m` with `m ∉ N^d`, say `m_(i0) < 0`. Take
`P`, `m*` from Lemma 2 for `S = ∪_k supp u_k` and this `m`.

1. `P·h ∈ H` by stability, and `P·e_ij(1) = e_ij(1)`, so
   `P·T = (P·h) e_ij(1) (P·h)^(-1) = I + (P·u)(P·v)^T ∈ H`.
2. By Lemma 1, `P·u = x^(Pm*) w` with `w ∈ A^r` unimodular. `r ≥ 3` and `A` is a polynomial
   ring over a field, so `SL_r(A)` acts transitively on unimodular columns (Suslin 1977;
   Quillen–Suslin suffices: complete `w` to a matrix in `GL_r(A)`, fix the determinant in
   `A^* = F_q^*` by scaling another column). Pick `g ∈ SL_r(A)` with `g w = e_r`. Then
   `T' = g(P·T)g^(-1) = I + e_r y^T ∈ H` with `y^T = x^(Pm*)(P·v)^T g^(-1)`. From
   `(P·v)^T(P·u) = P·(v^T u) = 0` we get `y_r = y^T e_r = 0`.
3. For `p ≠ q`, both different from `r`, put `X = e_r y^T`. Then `E_pq X = 0`,
   `X E_pq = y_p E_rq` and `X E_pq X = 0`, so
   `T' e_pq(1) T'^(-1) = I + E_pq + y_p E_rq = e_pq(1) e_rq(y_p) ∈ H`. Hence
   `e_rq(y_p) ∈ H ∩ U_rq(R) = U_rq(A)`, and `y_p ∈ A`. Every `p ≠ r` has such a `q`, since
   `r ≥ 3`. With `y_r = 0` this gives `y ∈ A^r`. (This is part 2 of
   `kt-kernel-overgroup-reduces-to-rank-one-transvections`.)
4. So `P·Y = (P·u)(P·v)^T = g^(-1) e_r y^T g ∈ M_r(A)`.
5. The monomial `x^m` of `Y` becomes the monomial `x^(Pm)` of `P·Y` in the same entry, with
   the same coefficient, since `P` does not cancel monomials. By Lemma 2,
   `(Pm)_k = ⟨ρ_k, m⟩ < 0` for every `k`. So `P·Y ∉ M_r(A)`. This contradicts step 4. ∎

## 3. Conclusion

By §2 every `h e_ij(1) h^(-1)` with `h ∈ H` has `uv^T ∈ M_r(A)`. The transvection criterion
(part 1 of `kt-kernel-overgroup-reduces-to-rank-one-transvections`, via Skolem–Noether and
`Pic A = 0`) gives `H ≤ SL_r(A)`. Hence `H = SL_r(A)`. ∎

## Remarks

* **What the compressors are used for.** Only one `P ∈ Mon` per bad exponent: a positive
  unimodular matrix whose rows all lie in one open normal cone of `conv(S)` near a
  coordinate vector. The Koszul-type columns singled out in the previous attempt, e.g.
  `u = (x_1,x_2,x_3)`, are not special. For `u = (x_1,x_2,x_3)` Lemma 1 just says that one
  column `Pe_a` of `P` is componentwise below the other two. Then `P·u` is a monomial times a
  vector with a constant entry.
* **Calibration (`d = 1`).** `Mon = {1}`. Lemma 2 holds with `P = 1` for every `m < 0`
  (`m* = min S`), and Lemma 1 says a Laurent column divided by its lowest power of `t` is
  `F_q[t]`-unimodular. So §2 reproves that an overgroup of `SL_r(F_q[t])` in
  `SL_r(F_q[t^(±1)])` with polynomial root contents is `SL_r(F_q[t])`, which is consistent
  with the maximality in `kt-compressor-sandwich-equivalent-to-kernel-polynomiality`
  §4. No density argument is needed.
* **Where stability is used.** Only in step 1, for a single `P` depending on `(u, m)`. For
  `d ≥ 2`, `P = I` fails Lemma 2 (its rows `e_k` for `k ≠ i0` need not be negative on `m`) and
  can fail Lemma 1 (`u = (x_1, x_2, x_3)`). The compressors are exactly what turns the
  one-variable argument into a `d`-variable one.
* **Computation.** `experiments/kt-vertex-compressors-2026-09-17/vertex_compressor_check.py`
  builds the `P` of Lemma 2 for random columns of random elements of `SL_3(F_3[x^(±1)])`
  (`d = 3`) and for the Koszul pair `u = (x_1,x_2,x_3)`, `v = (x_1^(-1), −x_2^(-1), 0)`. For each
  bad exponent it verifies unimodularity of `x^(−Pm*)P·u` by a Gröbner basis over `F_3`, and
  that `Pm < 0`. In `run-25-seed7.txt` all 40 checked (column, bad exponent) pairs are
  certified, and one Gröbner computation was skipped after 30 s. Only 8 of the 25 columns
  are unimodular without a compressor, after dividing by their monomial content.
