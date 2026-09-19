---
rg: 2
id: leavitt-cone-head-bound-holds-for-semisimple-ring-shadows
kind: claim
title: The cone-cover head bound (QC) holds with a linear constant for every representation of Gamma that factors through St_20 of a finite semisimple ring shadow
distinct_from:
  leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding: that splits non-hyperlinearity of Delta into (QC) and (HR) and leaves (QC) open; this proves (QC) on one explicit class of genuine representations, the ring shadows over finite semisimple rings, and names the exact representations it leaves out.
  leavitt-cone-cover-kernel-is-dense-in-every-compact-model: that is exact (relators exactly trivial force the head trivial in compact models); this is quantitative, with relators only delta-trivial and a dimension-free linear constant, on the ring-shadow class.
  leavitt-cuntz-cone-halves-have-rf-amalgam-cover: that builds Gamma and its relators; this bounds the head of Gamma-representations through the relators.
artifacts:
  - research/leavitt-cone-head-bound-semisimple-ring-shadows-proof.md
---

**ESTABLISHED** (route `leavitt-cone-head-bound-semisimple-ring-shadows-proof`; lane
swarm-0917-w17-w17-ptl-pull, obstruction-miner, finite-models; unreviewed).

**Setting** (`leavitt-cuntz-cone-halves-have-rf-amalgam-cover`,
`leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`).
- `R = L_(F_2)(1,2)`, with `t_i s_j = delta_ij` and `s_1 t_1 + s_2 t_2 = 1`. Put `q = s_1 t_1`.
- `R_+ = <s_1, s_2, q>` and `R_- = <t_1, t_2, q>`. The halves are `Delta_+- = St_20(R_+-)`, and
  they meet in `Delta_0 = St_20(F_2 1 + F_2 q) = SL_20(F_2)^2`.
- `Gamma = Delta_+ *_(Delta_0) Delta_-`, with `K = ker(Gamma -> Delta)` the normal closure of
  `k_1, ..., k_r`. The head is `z = x_13(q)`.
- Norms are normalized Hilbert--Schmidt.

**Ring shadows.** A *ring shadow* over a finite ring `B` is a pair of unital ring homomorphisms
`phi_+- : R_+- -> B` that agree on `F_2 1 + F_2 q`. The pair induces a homomorphism
`Phi : Gamma -> St_20(B)`. A representation `rho` of `Gamma` *factors through the shadow* if
`rho = pi o Phi` for a unitary representation `pi` of `St_20(B)`. Every Cohn shadow into
`M_2(F_2)` is a ring shadow.

**Theorem.** There is a constant `L`, depending only on the chosen relators `k_i`, with the
following property. Let `B` be any finite semisimple ring, let `(phi_+, phi_-)` be any ring shadow
over `B`, and let `pi` be any finite-dimensional unitary representation of `St_20(B)`. Then
`rho = pi o Phi` satisfies

```text
||rho(z) - 1||_2  <=  L * max_i ||rho(k_i) - 1||_2.                          (RS)
```

In particular `(QC)` holds on this class, with `delta = eps / L` independent of `B`, `pi` and the
dimension.

**Proof idea.**
1. *Six defects.* The Leavitt relations `t_i s_j = delta_ij`, `s_1 t_1 = q` and
   `s_2 t_2 = 1 - q` give six elements `g_d` of `K`. Each is a root commutator, and its image
   under `Phi` is a root element `x_13(d)`. Every `g_d` is a fixed product of `L_d` conjugates of the
   `k_i^(+-1)`.
2. *The defects generate B.* The quotient of `B` by the ideal `D` that the six defects generate
   receives a unital map from `R`. A nonzero finite ring cannot, so `D = B`, and every simple block
   of `B` sees some defect.
3. *Orbit averaging.* The spectral measure of `pi` on the row group `x_1k(B)`, `2 <= k <= 19`, is
   invariant under `SL_(18n)` on the left and `GL_n` on the right, in each block. So a character is,
   up to an error `2^-17`, a uniform functional on the maps that vanish on a uniformly random
   subspace `K_j` of fixed dimension. This gives `m(e) = ||pi(x_13(e)) - 1||_2^2 / 4` to within a
   factor `1 +- 2^-16` of `N(e)/2`, where `N(e)` is the probability that `im(e) ⊄ K`. By the
   Grassmannian bound, `N(e)` is 0 or at least `1/2` in each dimension profile.
4. So `m(q) <= 3 * sum_d m(d)`, which gives `(RS)` with `L = sqrt(18) * max_d L_d`.

## What this settles and kills

- **Class killed (refutation side of (QC)): common-ring congruence refutations.**
  - Failure of `(QC)` would make `Delta` hyperlinear and refute `(LNC3)`.
  - Next step 1 of `leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding` is to search pairs
    of congruence representations of the halves. The pairs that factor through one common finite
    semisimple ring cannot refute `(QC)`, whatever the ring, the representation or the dimension.
    This includes all Cohn shadows and all shadows into products of matrix algebras over finite
    fields.
  - *Invariant:* the Leavitt defect ideal. It is all of `B` because `R` has no nonzero finite
    quotient ring, and it is read on one row group whose character measure is orbit-uniform.
  - *Death step:* the uniform comparison `m(q) <= 3 * sum_d m(d)` of step 3.
- **Relation to the Hamming head bound.** A concurrently landed lane
  (`leavitt-cone-cover-hamming-head-bound-holds`, not yet in this worktree's graph) proves `(QC)` for
  permutation and finite-phase monomial representations, using nonsoficity of `R^x`. It leaves
  non-monomial unitary representations as the survivors. The class here is different: `pi` is an
  arbitrary unitary representation of `St_20(B)`, for example a cuspidal representation of
  `SL_(20n)(F_q)`, and so is in general far from monomial. The argument is a direct character-orbit
  computation and does not use soficity.
- **What survives, exactly.** Any counterexample to `(QC)` must be one of two kinds.
  1. *Radical shadows.* A shadow over a finite ring `B` with nonzero Jacobson radical, where `pi` sees
     the radical part of `x_13(B)`. Here the right-`GL_n` orbit averaging fails, since the units of
     `B` do not act transitively on the kernel data.
  2. *Non-ring gluings.* Genuine representations of the halves through different finite quotients
     `St_20(B_+)` and `St_20(B_-)`, glued over `Delta_0` by an intertwiner that no common ring
     induces.
- **Status of the hole.** `agent-leavitt-not-bcs-negative-root-corner` stays OPEN. This is a class
  kill on the refutation side of `(QC)`, not a proof of `(QC)`.
