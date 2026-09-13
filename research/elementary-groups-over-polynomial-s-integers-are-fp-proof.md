---
rg: 2
id: elementary-groups-over-polynomial-s-integers-are-fp-proof
kind: route
title: Pull the stable K_2 kernel back to the finitely presented group SL_n(Z[1/m])
target: elementary-groups-over-polynomial-s-integers-are-fp
requires:
  - steinberg-finite-presentation-and-kazhdan-theorem
artifacts:
  - research/artifacts/bh-sl3-zt-host-2026-09-12.md
---

Full details are in §3 of the artifact. Here `K_2(n,S) = ker(St_n(S) -> E_n(S))`.

**Imports (literature, not re-proved).**
1. `steinberg-finite-presentation-and-kazhdan-theorem` (Krstić–McCool Thm 3).
   `St_n(S)` is finitely presented for every finitely presented ring `S` and
   `n >= 4`. Both `A` and `R` are finitely presented rings.
   - *Primary source (review lane `bh-poly-linear-review`, 2026-09-12).* The
     Krstić–McCool paper was not obtained, only a secondary quotation of it.
   - U. Rehmann and C. Soulé, *Finitely presented groups of matrices*, Algebraic
     K-Theory (Evanston 1976), LNM 551, was read.
     - Their Theorem 2: for `A` as in their Theorem I and `Φ` a reduced
       irreducible root system of rank at least 3, `St(Φ, A)` is finitely
       presented.
     - Type `A_(n-1)` with `n >= 4` gives `St_n(A)` and `St_n(R)`.
   - Their Theorem I assumes a finitely generated commutative ring of Krull
     dimension `d` with `K_1` and `K_2` finitely generated.
     - `A = Z[1/m]` qualifies: its units are finitely generated and
       `K_2(Z[1/m])` is finite.
     - Their remark says the hypotheses pass from a regular `A` to `A[t]`, so
       `R` qualifies too.
2. **Stability** (van der Kallen; Weibel, *K-book* III, Remark 5.5.2). For `S`
   commutative noetherian of Krull dimension `d`, `K_2(n,S) -> K_2(S)` is an
   isomorphism for `n >= d+3`. Here `dim R = k+1` and `dim A = 1`.
3. **Homotopy invariance** (~~Weibel III, Ex. 5.2.3~~). `K_2(S) -> K_2(S[t])` is an
   isomorphism for regular noetherian `S`. Iterate along
   `A ⊂ A[t_1] ⊂ ... ⊂ R`.
   - *Corrected citation (review lane `bh-poly-linear-review`, 2026-09-12).*
     Ex. 5.2.3 proves this only for fields and defers regular rings to Chapter V.
   - The source is Weibel V, Thm 6.3 (Quillen): for regular noetherian `S`,
     `K_n(S) ≅ K_n(S[s])` for all `n`.
   - Weibel IV, Cor. 1.7.1 identifies that `K_2` with the `K_2` of Chapter III.
4. **`SL_n(Z[1/m])` is finitely presented for `n >= 3`.** Borel–Serre 1976 on
   `S`-arithmetic groups, the reference Zaremsky's Thm 1.2 uses; classical for
   `m = 1`. `Z[1/m]` is Euclidean, so `SL_n(A) = E_n(A)`.

**Proof.**
1. In the commutative square of stabilization maps, the left map
   `K_2(n,A) -> K_2(A)` is onto and the right map `K_2(n,R) -> K_2(R)` is
   injective, by import 2 with `n >= k+4`. The bottom map `K_2(A) -> K_2(R)` is
   onto by import 3.
2. So `K_2(n,A) -> K_2(n,R)` is onto.
3. `St_n(A)` and `St_n(A)/K_2(n,A) = E_n(A)` are both finitely presented (imports 1
   and 4). So `K_2(n,A)` is the normal closure of finitely many elements
   `w_1, ..., w_q`.
4. Their images normally generate `K_2(n,R)` in `St_n(R)`.
5. So `E_n(R) = St_n(R) / <<w_1,...,w_q>>`, a finitely presented group by import 1. ∎

**For `m = 1`.** Weibel III, Ex. 5.2.2 gives `K_2(Z) = Z/2`, so
`K_2(n, Z[t_1..t_k])` has order 2 in the same range.
