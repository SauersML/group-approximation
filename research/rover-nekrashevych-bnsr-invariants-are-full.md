---
rg: 2
id: rover-nekrashevych-bnsr-invariants-are-full
kind: claim
title: Every BNSR invariant of a Rover--Nekrashevych group is its whole character sphere, the sphere of sum-invariant characters
distinct_from:
  rover-nekrashevych-finite-presentation-criteria: that records finiteness properties, simplicity of the commutator subgroup and the abelianization; this computes the BNSR invariants on the character sphere.
---

**OPEN (candidate answer to Zaremsky Problem 1.14).** Let `G <= Aut(T_d)`, `d >= 2`,
be a finitely generated self-similar group, and put `Γ = V_d(G)`.

1. **Sphere.** Restriction to `G` (acting on one cone) identifies `Hom(Γ,R)` with
   the space of characters `χ: G -> R` satisfying `χ(g) = Σ_{x in X} χ(g|_x)` for all `g`.
2. **Invariants.** `Σ^m(Γ) = S(Γ)` for every `m >= 1` such that `Γ` has type `F_m`.

Model tests. With `G` trivial, `Γ = V_d` has finite abelianization, so both
statements are vacuous. For the binary odometer `a = σ(1, a)` the sphere is `S^0`.
There, item 2 says both kernels of `Γ -> Z` are of type `F_m` whenever `Γ` is.

## Attempts

- **Item 1 and `m = 1` (lane z1-14-rover-nek, 2026-09-13).** Both have written proofs,
  landing as separate claims: `rover-nekrashevych-characters-are-sum-invariant`
  and `rover-nekrashevych-groups-have-full-bns-invariant`. The `m = 1` proof
  realizes a character by elements supported on arbitrarily small cones. Those
  elements commute with every generator that fixes a cone pointwise.
- **Higher `m`, proposed route.** Let `X` be the Stein–Farley complex of `Γ`
  (vertices with `n` feet, cloning-system complex). Its cell stabilizers are
  finite-index subgroups of `G^n ⋊ S_n`.
  - Key observation: `χ(Stab σ) = χ(G) = χ(Γ)`, so `ker χ · Stab σ = Γ`. Hence
    `ker χ` acts cocompactly on every cocompact `Γ`-subcomplex, for discrete `χ`.
  - Cell stabilizers in `ker χ` are `K_n ⋊ P` with `K_n = ker(χ ⊕ ... ⊕ χ: G^n -> R)`.
    When `G` has type `F_m` and `n >= m+1`, `K_n` has type `F_m` by Meinert's product
    inequality (source to verify).
  - Ascending links in `X` are simplices, so `X_{>= n_1}` is homotopy equivalent to
    `X`. The low-feet cells, whose stabilizers may fail, can therefore be discarded.
    Descending links are those used to prove `Γ` is of type `F_m`.
  - With Brown's criterion this would give `ker χ` of type `F_m` for every discrete
    `χ`. Rational points would then lie in `Σ^m`; the irrational points need a
    Morse argument on `X × R`.
  - Missing, to verify from sources: the exact Stein–Farley complex and descending
    links for `V_d(G)` (Skipper–Witzel–Zaremsky 2019; Witzel–Zaremsky cloning systems),
    Meinert's inequality, and the stabilizer form of the Σ-criterion.
- **Caution.** A contracting `G` that is not finitely presented can still have
  `V_d(G)` finitely presented (Nekrashevych, Theorem 5.9). An example is the Basilica
  group, whose sum-invariant characters `χ(a) = χ(b)` exist assuming its abelianization
  `Z^2` (Grigorchuk–Żuk, not re-derived here). The stabilizer route says nothing
  there. `Σ^2(V_2(Basilica))` is the first test case where item 2 could fail.
