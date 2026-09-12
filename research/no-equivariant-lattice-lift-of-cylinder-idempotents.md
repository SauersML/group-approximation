---
rg: 2
id: no-equivariant-lattice-lift-of-cylinder-idempotents
kind: claim
title: No Thompson-equivariant Boolean lattice lift of the cylinder idempotents exists
distinct_from:
  odd-measure-space-has-no-honest-thompson-compression: that forbids clopen compressions of the odd-measure space moved by V; this forbids any uniform V-equivariant Boolean section of the Dirac evaluation, the scheme a nested mixed-depth lift would need.
  natural-leavitt-pair-lifts-have-partial-symmetry-defect: that computes the defect of one natural lift; this rules out removing such defects by a functorial lattice lift at all depths.
artifacts:
  - research/artifacts/ternary-cohn-mixed-depth-lifts-2026-09-12.md
---

Let `X = {0,1}^N`, `V` Thompson's group acting on `X`, and `M_-` the odd-measure space of
`signed-thompson-algebra-is-odd-measure-crossed-product`, with Dirac measures `delta_x`. There is no map
`Phi` from the clopen algebra of `X` to the clopen algebra of `M_-` such that

1. `Phi` is a Boolean algebra homomorphism (preserves `∅`, `X`, intersections and complements);
2. `Phi(gC) = g Phi(C)` for every `g in V`, with `V` acting on `M_-` by push-forward.

So there is none that also satisfies 3, `delta_x in Phi(C)` iff `x in C`, as a lift of the evaluation
would have to. The proof does not use 3.

A companion statement holds in all of `B = C(M_-, F_3) x| V`. There is no map `Phi : Clopen(X) -> B`
that is additive on disjoint unions, has `Phi(X) = eps_-`, and satisfies `Phi(gC) = [g] Phi(C) [g]^-1`.
The `F_3`-valued Haar trace turns such a `Phi` into a `V`-invariant finitely additive measure of mass `1`.
See artifact Remark 3.2.

Why it matters. The honest lifts `P_C = 1_(U_C)` satisfy 2 and 3 but only the XOR law
`U_(C xor D) = U_C xor U_D`, not 1. That is exactly why honest lifts of nested or orthogonal cylinders
fail to be nested or orthogonal, and why the natural lift of `(s_0, t_0)` leaves the kernel defect of
`natural-leavitt-pair-lifts-have-partial-symmetry-defect`. The claim says no uniform lifting scheme
repairs this at all depths: a Cohn-family witness must break equivariance or the lattice structure
somewhere, through finitely many non-functorial choices or through coefficients outside `{0,1}`.

Proof sketch. By Stone duality `Phi = r^-1` for a continuous `r : M_- -> X`, and item 2 gives
`r(g mu) = g r(mu)`. The Haar measure `lambda` of `M_-` is
`V`-invariant, so `r_* lambda` is a `V`-invariant probability measure on `X`. None exists: some `g in V`
maps `0` onto `00` and some maps `0` onto `01`, forcing `nu(0) = nu(00) = nu(01)` and `nu(0) = 0`;
the swap gives `nu(1) = 0`. Full proof: Section 3 of the artifact.
