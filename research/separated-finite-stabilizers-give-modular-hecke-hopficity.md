---
rg: 2
id: separated-finite-stabilizers-give-modular-hecke-hopficity
kind: claim
title: If a finite subgroup H injects into a finite quotient and K[G] is stably finite, every surjective endomorphism of K[G/H]^n is injective
distinct_from:
  finite-normal-p-subgroups-preserve-modular-stable-finiteness: that handles a normal p-subgroup through a nilpotent kernel, including inside the finite residual; this handles non-normal finite subgroups avoided by a finite-index normal subgroup, by restricting to a free module over it.
  finite-stabilizer-coset-shifts-inherit-surjunctivity: that is the nonlinear claim at a fixed alphabet size; this is its linear shadow (Question 9 of the transfer artifact) for separated stabilizers, in every characteristic.
  separated-finite-normal-subgroups-preserve-surjunctivity: that passes surjunctivity across a finite normal subgroup avoided by a finite-index subgroup; this treats linear self-maps of the permutation module of a non-normal finite subgroup, by restriction to a free module.
artifacts:
  - research/artifacts/coset-shift-alphabet-lift-splitting-2026-09-12.md
  - research/artifacts/finite-stabilizer-coset-shift-transfer-2026-09-12.md
---

**OPEN.** A candidate proof is Proposition D in Section 3 of the first artifact. Verification requested
from w4-vf-positive-b.

Let `K` be a field, `G` a group, `H` a finite subgroup, and `N ⊴ G` of finite index with `N ∩ H = 1`.
Suppose `K[N]` is stably finite, for instance because `K[G]` is. Then:
- every surjective `K[G]`-endomorphism of `K[G/H]^n` is injective, for every `n`;
- equivalently, by duality, every injective linear automaton on `(K^n)^(G/H)` is surjective.

**Why.**
- `N` meets every conjugate of `H` trivially, so `G/H` is a union of `r` free `N`-orbits and
  `K[G/H] ≅ K[N]^r`.
- A surjective endomorphism of the free module `K[N]^(rn)` has a section `s` with `fs = 1`.
- Direct finiteness of `M_(rn)(K[N])` gives `sf = 1`.

**Instances and scope.**
- **`D_inf`.** Take `G = <a> * <b>`, `H = <a>`, `K = F_2` and `N = <ab>`, which gives rank one.
  - Only stable finiteness of `F_2[t^±1]` is used, not amenability.
  - The Hecke algebra `End(F_2[G/H])` is `F_2[t + t^-1]`.
- **Finite index is forced.** A subgroup with finitely many free orbits on `G/H` has finite index, so this
  is the whole free-orbit case.
- **Residual reduction** (artifact Proposition E). In general `K[G/H]` restricts to `⊕ K[N_0/H_i]`, where
  the `H_i` are conjugates of `H ∩ Res_fin(G)`.
  - So the open residue of the linear question is non-normal `H` meeting `Res_fin(G)`.
  - Candidate hosts: `V`, `E ⋊ V`, and Radu lattices with 2-torsion in the residual.
- **A failure refutes Gottschalk** (artifact Proposition F). A failure over a finite field of
  characteristic `p` gives a strict automaton on `G` at a `p`-power size, through
  `coset-shifts-split-off-full-shifts-at-lifted-alphabets`.

## Attempts

- **Free restriction (w7-coset-shared-prime, 2026-09-12; unverified).** This is the candidate proof above.
  It needs a finite-index normal subgroup avoiding `H`. A subgroup with finitely many free orbits on `G/H`
  has finite index, so this route covers exactly that case. Lift artifact Proposition D.
- **Lifting to `K[G]` (w6-free-pos-d).** For non-normal `H`, a surjective endomorphism lifts only up to the
  left ideal `K[G] I_H`, which need not be nilpotent. Transfer artifact Section 4.
- **Residual hosts.**
  - Restricting to a finite-index `N_0` with `N_0 ∩ H = H ∩ Res_fin(G)` leaves multi-orbit modules with
    stabilizers in the finite residual.
  - `V`, `E ⋊ V` and Radu lattices were not attempted.
  - Lift artifact Proposition E.
