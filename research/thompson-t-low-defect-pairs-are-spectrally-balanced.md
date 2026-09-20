---
rg: 2
id: thompson-t-low-defect-pairs-are-spectrally-balanced
kind: claim
title: Low-defect Z/4 * Z/3 pairs for Thompson's T are tracially a·trivial + (1-a)·regular, irreducible ones have a <= sqrt(5/17), and T is MF iff some low-defect sequence has regular trace and balanced spectra
distinct_from:
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that is the operator-norm criterion itself (T not MF iff irreducible nontrivial pairs have a uniform defect gap); this adds the tracial constraint every low-defect sequence obeys, bounds the trivial weight of irreducible ones, and sharpens the criterion to sequences whose traces converge to the regular character.
  no-proper-character-groups-avoid-amenable-orbit-full-groups: that proves T has no proper characters and applies it to orbit full groups; this consumes that character simplex for operator-norm approximate representations of the Lochak--Schneps presentation.
  thompson-v-character-simplex: that is the character simplex of V; this uses the one of T and draws spectral consequences for T's defect criterion.
  thompson-t-has-full-mf-radical: that is the open target; this is an ESTABLISHED structural constraint on any would-be MF model of T, not a proof or refutation of the target.
artifacts:
  - experiments/thompson-t-far-sector-census-2026-09-17/census.py
  - experiments/thompson-t-far-sector-census-2026-09-17/census2.py
  - experiments/thompson-t-far-sector-census-2026-09-17/out2_n4.jsonl
  - experiments/thompson-t-far-sector-census-2026-09-17/out2_n5.jsonl
  - experiments/thompson-t-far-sector-census-2026-09-17/out2_n6.jsonl
  - experiments/thompson-t-far-sector-census-2026-09-17/out2_n7.jsonl
  - experiments/thompson-t-far-sector-census-2026-09-17/out2_n8.jsonl
  - experiments/thompson-t-far-sector-census-2026-09-17/out2_n10.jsonl
  - experiments/thompson-t-far-sector-census-2026-09-17/out2_n12.jsonl
---

**ESTABLISHED** by `thompson-t-low-defect-pairs-spectrally-balanced-proof`.

## Setting

As in `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`:
`G0 = Z/4 * Z/3 = <alpha, beta>`, `T = G0 / <<r_1, r_2, r_P>>`, and a pair is
`(A, B) in U(n)^2` with `A^4 = B^3 = 1`, of defect
`D(A,B) = max_j ||r_j(A,B) - 1||` (operator norm, `j = 1, 2, P`).
`tau = tr/n`. For a pair, `f_A(j)` is the fraction of eigenvalues of `A`
equal to `i^j`, `f_B(j)` the fraction equal to `e^(2 pi i j/3)`.

## Statement

1. **(Tracial limit.)** Let `(A_k, B_k)` be pairs with `D(A_k,B_k) -> 0` and
   let `omega` be a free ultrafilter. There is `a in [0,1]` such that for
   every word `w` in `alpha, beta`,
   `lim_omega tau(w(A_k,B_k)) = 1` if `w = e` in `T`, and `= a` otherwise.
   The same `a` serves every nontrivial element of `T`.
2. **(The T-line.)** Consequently, along `omega`:
   - `f_A(0) -> (1+3a)/4`, `f_A(j) -> (1-a)/4` for `j = 1,2,3`;
   - `f_B(0) -> (1+2a)/3`, `f_B(j) -> (1-a)/3` for `j = 1,2`;
   - the spectral measure of `C = BA` converges weakly to
     `a delta_1 + (1-a) * (uniform on the 5th roots of unity)`.
3. **(Uniform gap off the line.)** For every finite set `S` of nontrivial
   elements of `T` (given by words) and every `eta > 0` there is
   `c(S, eta) > 0` such that every pair, in every dimension, with
   `D < c` satisfies `|tau(w(A,B)) - tau(A)| < eta` for all `w in S`. In
   particular pairs whose multiplicity fractions stay `eta`-far from the
   T-line of item 2 have defect bounded below uniformly in `n`
   (non-effective).
4. **(Irreducible pairs are mostly regular.)** If the `(A_k,B_k)` are
   nontrivial and irreducible, then `a <= sqrt(5/17) = 0.5423...`. If they are nontrivial
   irreducible exact representations of `Delta(4,3,5) = G0/<<r_P>>`
   (so `(BA)^5 = 1`), then `a <= sqrt(13/133) = 0.3126...`.
5. **(Class kill: trivial-heavy sequences.)** Any family of low-defect
   pairs with `tau(g) -> 1` for a single nontrivial `g in T` has `a = 1`.
   So no such family consists, eventually, of nontrivial irreducible pairs. Examples:
   - near-central pairs, `||[A^2, B]|| -> 0`, since `[alpha^2, beta] != e`
     in `T`;
   - pairs with `f_A(0) -> 1` or `f_B(0) -> 1`;
   - pairs close to `1` in normalized 2-norm.
6. **(Sharpened criterion.)** `T` is MF iff there are pairs `(A_k,B_k)`
   with `D(A_k,B_k) -> 0` and `tau(w(A_k,B_k)) -> 0` for every `w != e` in
   `T`. Such a sequence has asymptotically balanced spectra:
   `f_A(j) -> 1/4`, `f_B(j) -> 1/3`, and `C = BA` equidistributed on the
   5th roots of unity.
7. **(Spectral shape.)** Under item 1, for any self-adjoint
   `h = sum c_g g` in `C[T]` with a word lift `H_k = h(A_k,B_k)`, the
   empirical eigenvalue distribution of `H_k` converges along `omega` to
   `a delta_(sum c_g) + (1-a) mu_h`, where `mu_h` is the spectral measure
   of `lambda(h)` in the group von Neumann algebra `L(T)` with its trace.
   For `h = alpha + alpha^* + beta + beta^*`, `mu_h` has support bounded
   away from `4`, since `T` is not amenable (`thompson-t-is-not-amenable`).

## What this changes

- **Where to look for an MF model.** Item 6 reduces the search to
  balanced types. A census over types sorted by imbalance, such as
  `experiments/thompson-t-far-sector-census-2026-09-17/census2.py`, is
  asymptotically looking in the right place only if the trivial eigenvalue
  is not deficient. Types such as `A = (2,3,4,3)` at `n = 12` (trivial
  eigenvalue *least* frequent) are at distance at least `1/12` from the
  T-line, so item 3 bounds their defect below uniformly in `n`.
- **Near-central classes are dead.** Item 5 gives, non-effectively and in
  every dimension, what the golden near-central bound gives effectively in
  small dimension: near-central low-defect pairs are 2-norm trivial and so
  cannot be irreducible.
- **What an MF model of T must be.** By item 6 it can be taken to be an
  operator-norm asymptotic representation that is simultaneously a
  tracial (Connes-type) model of `L(T)`. A proof that `T` is not MF may
  therefore use the regular trace of `T` as an extra hypothesis on the
  approximating sequence, and in particular the non-amenability spectral
  gap of item 7.

## Numerical side-check (not load-bearing)

The census in `experiments/thompson-t-far-sector-census-2026-09-17/` (exact
`Delta(4,3,5)` representations; `D12 = max(||r_1 - 1||, ||r_2 - 1||)`)
found no irreducible exact representation with `D12 < 0.89` in the far
sector (`||[A^2,B]|| > 0.9`) for `4 <= n <= 12` (`n = 9, 11` not run).
The search was a local optimizer with few restarts (files `out2_n*.jsonl`,
residual `||BA - C||_F < 1e-7`, commutant dimension 1), so this is not a
lower bound. The best far values found were:

| n | best D12 | type (mA / mB / mC) |
|---|---|---|
| 5 | 0.9607 | 1121 / 122 / 11111 |
| 6 | 0.8946 | 2121 / 222 / 21111 |
| 7 | 0.9607 | 1222 / 133 / 11221 |
| 8 | 1.1636 | 2222 / 422 / 22112 |
| 10 | 0.9605 | 2242 / 244 / 22222 |
| 12 | 1.2391 | 4323 / 444 / 23223 |

At `n = 4` the only irreducible values found were `1.618`.

The value `0.9606` with `||[A^2,B]|| = 0.960` recurs as an irreducible
critical value at `n = 5, 6, 7, 10`, which suggests a structured family. No
value approaches the near-central golden bound `0.618`.
