---
rg: 2
id: lamp-character-orbit-separation-proof
kind: route
title: Split the cone along the lamp kernel and apply Clifford's theorem
target: lamp-character-orbit-separation
requires: [hilbert-embeddable-is-representation-realized]
artifacts:
  - notes/TRUE_LAMP_CHARACTER_ORBIT_SEPARATION.md
---

# Split the cone along the lamp kernel and apply Clifford

The complete argument is §§1–2 of the cited note.

**The splitting.** By `hilbert-embeddable-is-representation-realized` every
Hilbert embeddable invariant length with `ℓ(1) = 0` is a nonnegative
combination of the generators `ψ_χ(h) = χ(1) − Re χ(h)`, one per nontrivial
irreducible. Partitioning the index set by whether `L ⊆ ker χ` splits `ℓ` into
`ℓ_I + ℓ_II` with both summands nonnegative and conditionally negative
definite, and `ψ_χ|_L ≡ 0` for `χ ∈ Irr_I` because `χ(h) = χ(1)` there.

**Clifford's theorem.** For `χ ∈ Irr_II`, `χ|_L` is `e` times the sum over a
single `K`-orbit of irreducible characters of `L`. Abelianness of `L` makes
those linear, so `χ(1) = et`; and if the orbit contained the trivial character
it would be the whole orbit, forcing `L ⊆ ker χ`, i.e. `χ ∈ Irr_I`. Evaluating
`ψ_χ` at `h ∈ L` and dividing by `χ(1) = et` cancels `e` and leaves
`1 − (1/t)Σ_i θ_i(h)`.

**The hypercube computation.** For `L = (ℤ/2)^Sites`, `θ_S(a) = (−1)^{|S ∩
supp(a)|}`, so `(1/t)Σ_S θ_S(a) = 1 − 2f` with `f` the fraction of the orbit
meeting `supp(a)` in an odd number of sites; hence `ψ_χ(a)/χ(1) = 2f`. Taking
`supp(a) = {p, q}` gives the two-site mark and `supp(a) = {p}` the single lamp.

**The three conclusions.** Genericity of orbits gives the non-dilution
statement; identification of the two marked cosets in a genuine finite quotient
sends every `f` to zero, reproducing `finite-quotient-blindness`; and the
relative gap bounds `ψ_χ` from below only on `L`, so it cannot see a defect
that the two-site rigidity theorem places off `L`.
