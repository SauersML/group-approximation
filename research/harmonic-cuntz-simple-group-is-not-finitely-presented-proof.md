---
rg: 2
id: harmonic-cuntz-simple-group-is-not-finitely-presented-proof
kind: route
title: The central rational scalars of the perfect group EL_3(C_h) are not finitely generated
target: harmonic-cuntz-simple-group-is-not-finitely-presented
requires:
  - harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q
  - harmonic-cuntz-ring-is-purely-infinite-simple
  - leavitt-scalar-commutators-block-fp-central-quotients
---

Lane proof, not independently reviewed. Let `N >= 3`, `H = EL_N(C_h)` and
`Z = H ∩ {λI : λ ∈ Q^x}`.

1. **Z is central in H.** `Q ⊆ Z(C_h)` (`harmonic-cuntz-ring-is-purely-infinite-simple`,
   parts 1 and 4), so each `λI` commutes with every matrix over `C_h`.
2. **H is perfect.** For distinct `i, k, j` in `[N]` (here `N >= 3` is used),
   `e_ij(r) = [e_ik(r), e_kj(1)]`. So every generator of `H` is a commutator, and
   `[H,H] = H`. Hence `Z ≤ Z(H) ∩ [H,H]`.
3. **Z is not finitely generated.** Part 6 of `harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q`
   gives `Z = Q^x·I ≅ Z/2 × Z^(∞)` for `N = 3`. An independent check for every
   `N >= 3`: `C_h` has the Leavitt family `s_0, s_1, t_0, t_1` (`t_i s_j = δ_ij`,
   `s_0 t_0 + s_1 t_1 = 1`), and `Q ⊆ Z(C_h)` is infinite. So part 2 of
   `leavitt-scalar-commutators-block-fp-central-quotients` (`d = 2`, `K = Q`) gives
   `GL_N(L_Q(1,2)) = EL_N(L_Q(1,2)) ≤ EL_N(C_h)`, which contains `λI` for every
   `λ ∈ Q^x`. So `Z = Q^x·I`, and `Q^x` is not finitely generated.
4. **Group lemma.** Part 0 of `leavitt-scalar-commutators-block-fp-central-quotients`,
   with `C_0 = Z`, says that `H/C` is not finitely presented for any
   `Z ≤ C ≤ Z(H)`. The mechanism: for a central extension `1 -> C -> H -> P -> 1`,
   the five-term sequence `H_2(H) -> H_2(P) -> C -> H_1(H) -> H_1(P)` shows that
   `C ∩ [H,H]` is the image of `H_2(P; Z)`. That group is finitely generated when
   `P` is finitely presented.
5. **Conclusion.** For `N = 3` and `C = Z`, `Λ_h = H/Z` is not finitely presented.
   This contradicts `harmonic-cuntz-simple-group-is-finitely-presented`. By part 1 of
   `harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q`, every proper normal subgroup of
   `H` consists of central scalars, so `Z(H) = Z`. The case `C = Z(H)` is therefore the
   same group.
