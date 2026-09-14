---
rg: 2
id: complex-lamplighter-linearizations-are-normal-iff-surjective
kind: claim
title: The complex linearization of an injective automaton is a normal endomorphism of the lamplighter von Neumann algebra iff the automaton is surjective
distinct_from:
  bijective-ca-preserve-uniform-bernoulli-measure: that proves bijective automata preserve the uniform measure; this reads an arbitrary automaton as a *-endomorphism of the group algebra of Z/q wr G and shows that trace, rank-function and normality arguments in characteristic zero detect surjectivity exactly through absolute continuity of the output measure.
  injective-measure-preserving-ca-is-surjective: that is the measure statement; this is its operator-algebraic dictionary, recorded as the exact reach of characteristic-zero linearization.
artifacts:
  - research/artifacts/amenable-extension-surjunctivity-transfer-2026-09-12.md
---

**ESTABLISHED** by `complex-lamplighter-linearization-proof`.

Identify `A` with `Z/q`, put `H = Z/q wr G`, and write `C[H] = LC(A^G) x|_alg G` by Fourier expansion. For an automaton
`tau` put `Phi_tau(sum f_g u_g) = sum (f_g o tau) u_g` and `nu = tau_* lambda`.

1. `Phi_tau` is a unital *-endomorphism of `C[H]` fixing `C[G]`.
2. `tau` is injective iff `Phi_tau` is surjective, and surjective iff `Phi_tau` is injective.
3. `tr o Phi_tau` is the trace of `nu`, and the von Neumann rank of `Phi_tau(f)` is `nu(supp f)` for `f in C[L]`.
4. For infinite `G` and injective `tau`, these are equivalent: `tau` is surjective; `Phi_tau` preserves the canonical
   trace; `Phi_tau` extends to a normal endomorphism of `L(H)`; `nu << lambda`.

**Consequence (proved).** A strict automaton is a surjective, non-injective, non-normal *-endomorphism of `C[Z/q wr G]`.

**Interpretation (not part of the theorem).** The theorem computes only the canonical trace and the von Neumann rank
function of `L(H)`. For those two, detecting surjectivity is exactly proving `nu << lambda`, which is
`every-injective-ca-preserves-uniform-bernoulli-measure`, equivalent to the goal. Our reading is that characteristic-zero
arguments of this kind give no independent access to the conjecture. This is not proved: other Sylvester rank
functions on `C[Z/q wr G]`, and non-tracial characteristic-zero invariants, are not addressed.

Proof: Section 1.3 of the linked artifact.
