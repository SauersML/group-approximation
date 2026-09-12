---
rg: 2
id: prime-field-leavitt-tensor-powers-have-trivial-k-theory
kind: claim
title: For every prime p every tensor power of L_(F_p)(1,2) has K_1 = K_2 = 0
distinct_from:
  leavitt-tensor-powers-have-trivial-k-theory: that is the characteristic-two case; this is every prime field, needed for the positive-characteristic linear class at transcendence degree three and above.
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that imports vanishing for L ⊗ R with R regular supercoherent, covering one and two factors; this asks for three or more factors, over every prime field.
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

**OPEN.** For every prime `p` and every `d >= 3`, with `L_p = L_(F_p)(1,2)`,
`K_1(L_p^(⊗d)) = K_2(L_p^(⊗d)) = 0`.

It is true for `d = 1, 2`: Ara--Brustenga--Cortiñas Theorem 7.6, and
Ara--Cortiñas Lemma 6.1 with Proposition 6.2 over `k = F_p`, as used in
`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`. For `p = 2` it is
`leavitt-tensor-powers-have-trivial-k-theory`.

## Attempts

1. **Transfer from characteristic two.** Every recorded formulation on
   `leavitt-tensor-powers-have-trivial-k-theory` is characteristic-free:
   - `KH(A ⊗ L_k(1,2)) = 0` for every ring `A` (ABC Theorem 8.6);
   - the twisted-Nil formula of ABC Theorem 5.10 for H-unital coefficient
     rings;
   - Ara--Cortiñas Proposition 6.2 for regular supercoherent coefficients.

   So a characteristic-free proof there settles this claim.
   *Stops* where that claim stops: regular coherence of free algebras over
   `L_p^(⊗(d-2))[t_1, ..., t_n]`, equivalently vanishing of the twisted Nil
   groups `NK(L_0 ⊗ A; φ^(±1))` in degrees 1 and 2 for
   `A = L_p^(⊗(d-1))`.
2. **Only one consumer needs `K_1`.** For the positive-characteristic linear
   class, `leavitt-power-projective-elementary-groups-finitely-presented` is
   enough, and it is equivalent to finite normal generation of an unstable
   Steinberg kernel. This claim is a sufficient condition, not a necessary one.
3. **Coherence is refuted over every field.**
   `leavitt-tensor-powers-are-not-left-coherent` holds over `F_p`, so the route
   `prime-field-leavitt-powers-k-theory-via-coherence` is invalidated.
   - The free algebras of attempt 1 are not coherent either. `L_p^(⊗(d−1))` is a
     flat universal localization of `L_p^(⊗(d−2))<e,f>`, and flat universal
     localizations inherit coherence.
   - Only the twisted Nil groups remain.
