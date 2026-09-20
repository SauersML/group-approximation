---
rg: 2
id: lifted-thompson-t-central-displacement-gap
kind: claim
title: "Thompson's T is full exactly when corona displacements of the central translation of T-bar avoid an interval (0, eta); so the descent (D) holds iff T-bar has corona representations whose z-spectrum lies in arbitrarily short arcs"
distinct_from:
  lifted-thompson-t-mf-descends-to-t: that is (D); this proves (D) equivalent to the approximate forms (Arc) and (Small), which need no exact scalar and no commutant projection, and proves the first conjunct equivalent to a uniform gap.
  lifted-thompson-t-twist-set-is-trivial-or-the-circle: that classifies the exact scalar twists Sigma and the spectra S; this classifies the operator-norm displacement set N and shows that approximate twists near 1 already decide T.
  simple-kazhdan-mf-lives-in-gap-near-representations: that is local rigidity near the trivial tuple for rationally perfect groups; this applies the same Zassenhaus mechanism to the central translation of T-bar, where it is a statement about far-from-trivial representations with small central displacement.
  rotation-centralizer-rotation-gaps-are-uniform: that is a uniform gap for exact-order quotients at every displacement c and is equivalent to the flagship; this gap is only at small displacement, only for T-bar itself, and is equivalent to thompson-t-has-full-mf-radical, the other conjunct.
  lifted-thompson-t-centre-has-commutant-eigencorners: that asks for exact eigencorners; item 5 here shows that, when T is full, commutant corners cannot even localize rho(z) to a short arc.
---

**ESTABLISHED** by `lifted-thompson-t-central-displacement-gap-proof`.

**Notation.** `T̄`, `z`, `t_j = lambda^j(z)`, `Sigma` and `S` are as in
`lifted-thompson-t-twist-set-is-trivial-or-the-circle`. A *corona
representation* is a homomorphism `rho : T̄ -> U(Q)` into some norm matrix
corona `Q = prod_n M_(k_n) / (+)_n M_(k_n)` (the sizes are allowed to vary
with `rho`). Its *displacement* is `||rho(z) - 1||`. Put

```text
N = { ||rho(z) - 1|| : rho a corona representation of T̄ }  ⊆  [0, 2].
```

"`T` full" means `Rad_MF(T) = T`, i.e. `thompson-t-has-full-mf-radical`.

## Statement

0. **(Zassenhaus gap, any C\*-algebra.)** Fix a finite generating set
   `s_1, ..., s_m` of `T̄`. There is `delta > 0` such that every unital
   homomorphism `sigma : T̄ -> U(D)`, into any unital C\*-algebra `D`, satisfies
   `max_i ||sigma(s_i) - 1|| ∈ {0} ∪ [delta, 2]`.
1. `N` is closed.
2. **(First conjunct as a gap.)** `T` is full iff `0` is an isolated point of
   `N`, i.e. iff there is `eta > 0` with `N ∩ (0, eta) = ∅`. The same `eta`
   then works in every commutant corner: if `P != 0` is a projection in
   `rho(T̄)' ∩ Q` and `||(rho(z) - 1) P|| < eta`, then `rho(g) P = P` for all
   `g`.
3. `T` is MF iff `N = [0, 2]`.
4. **(Trichotomy.)** Exactly one of the following holds.
   - `N = {0}`. This is `lifted-thompson-t-is-not-mf`.
   - `N = [0, 2]`. This is "`T` is MF".
   - `N != {0}` and `N ⊆ {0} ∪ [eta, 2]` for some `eta > 0`. This is exactly
     the world in which `lifted-thompson-t-mf-descends-to-t` (D) fails.

   Consequently each of the following is equivalent to (D).
   - **(Small)** If `N != {0}`, then `inf (N \ {0}) = 0`.
   - **(Arc)** If `T̄` is MF, then for every `eps > 0` some corona
     representation `rho` has `rho(z) != 1` and `sp(rho(z))` contained in an
     arc of length `eps` (anywhere on the circle).
5. **(Spread when `T` is full.)** Suppose `T` is full and let `eta` be as in
   item 2. Let `rho` be a corona representation, `P != 0` a projection in
   `rho(T̄)' ∩ Q`, and `X_P` the spectrum of `rho(z) P` in `PQP`. Then either
   `X_P = {1}` and `rho(g) P = P` for all `g`, or
   `diam X_P = max {|x - y| : x, y ∈ X_P} >= eta`. The same holds with `z`
   replaced by `t_j` and `rho(T̄)` by `rho(lambda^j T̄)`, for every `j >= 0`.
6. **(Homotopy constructions are dead.)** Let `Y` be a connected space and
   `D` a unital C\*-algebra. Every homomorphism `pi : T̄ -> U(C(Y, D))` that
   is scalar at one point of `Y` is trivial. In particular `T̄` has no
   nontrivial homomorphism into the unitary group of a cone
   `C_0((0,1], D)~` or a suspension `C_0((0,1), D)~`.
