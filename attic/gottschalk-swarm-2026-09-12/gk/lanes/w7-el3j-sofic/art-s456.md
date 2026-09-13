
## 4. Approaches that die, and where

**4.1 Reduction to a known open group.**
* **Attempt.** Find `V`, `T`, `R^x`, `EL_3(C_2)`, Thompson's `F` or `BS(2,3)` inside `E`.
* **Dies.** None embeds (Corollary 1.5). Every finitely generated subgroup is locally finite by residually finite
  linear.

**4.2 Permutation models of the truncations.**
* **Attempt.** Take the natural finite images `E_N <= GL_(3N)(F_2)`, obtained by truncating the shift orbit at level
  `N` as in the path-permutation criterion on `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`. Let them act on
  vectors, flags or Grassmannians of `F_2^(3N)`.
* **Dies.** The head is a transvection `1 + v ⊗ φ`.
  - **Vectors.** It fixes half of `F_2^(3N)`, namely `ker φ`. So it is not asymptotically free.
  - **Bounded-dimensional subspaces.** It fixes every `k`-subspace inside `ker φ`. That is a proportion bounded below
    for fixed `k`.
  - **Large Grassmannians.** For `k, 3N - k -> ∞`, a rank-one perturbation of the identity fixes about
    `2^(k-3N) + 2^(-k)` of the `k`-subspaces. So bounded-rank elements move almost every point.
  - **The same count applies to relation errors.** It applies equally to the bounded-rank far-end error of a relation
    in `E_N`. So relations then fail almost everywhere.
  - **The errors cannot be removed.** The endomorphism `ψ` of that criterion would remove them, but it does not extend
    (entry "Dead: `ψ` does not extend" on that node): the constants detect the orientation of the turn at index `0`.
  - **Summary.** Switching the action decides which of the two fails, but not whether one fails.

**4.3 Gluing the halves.**
* **Attempt.** Combine finite or sofic models of `H_+` and `H_-` (Section 3) that agree on `H_0`.
* **Dies.** These are models of the amalgam `H_+ *_(H_0) H_-`, and `E` is a proper quotient of it (Proposition 3.5).
  The first failing relations are the Toeplitz commutators, for example `[x_12(T), x_23(S)] = x_13(1)`.

**4.4 Weak soficity.**
* **Attempt.** Upgrade the weak soficity recorded in `binary-jacobson-core-is-weakly-sofic-with-fd-head-radical`.
* **Dies.** Weak soficity allows arbitrary bi-invariant metrics on the finite groups and is not known to imply
  soficity. Nothing in that node controls the normalized Hamming length.

**4.5 Permanence.**
* **Attempt.** Use the extension `1 -> L -> E -> SL_3(F_2[z,z^(-1)]) -> 1`.
* **Dies.** The kernel is locally finite, hence amenable, and the quotient is linear, hence sofic. So `E` is
  amenable by sofic.
  - `sofic-kernel-amenable-quotient-permanence` is the other direction, sofic by amenable.
  - Amenable-by-sofic permanence is open even for finite cyclic kernels. This is recorded on main in
    `binary-jacobson-weak-sofic-status-proof` Section 5 (ABFG, arXiv:1802.04688, Section 4.4); I read that node, not
    the paper.
  - `E` is also not a split or central extension of the easy kind. `C_E(L) = 1` (Proposition 1.4).

**4.6 Residual amenability.**
* **Attempt.** Approximate `E` by amenable quotients.
* **Dies.** Every amenable quotient kills `L` (Proposition 1.4).

**4.7 Embedding into a LEF group.**
* **Attempt.** Embed `E` in a group already known to be LEF.
* **Dies.** Subgroups of LEF groups are LEF, so this is the same as proving `E` LEF. By Section 2 it is also the only
  route through amenable local embeddings.

**4.8 Uniform constructions.**
* **Attempt.** Build approximations for `EL_n(J)` uniformly in `n`.
* **Dies.** An amenable scheme would make `EL_4(J)` LEA, hence LEF (Section 2), contradicting
  `cohn-elementary-group-is-not-lef`.

## 5. The characteristic-three twin

Let `J_3 = F_3<S,T | TS=1>`, `E_3 = EL_3(J_3)` and `L_3 = ker π`.

* **Section 1 holds verbatim for `F = F_3`.**
  - `L_3` is locally finite.
  - Subgroups of `E_3` are locally finite by linear.
  - `E_3` contains no `V`, no `T`, and no finitely generated locally finite extension of an infinite simple group.
* **The monolith is `SL_fin(N x {1,2,3}, F_3)`.**
  - **It lies in `L_3`.** `L_3` contains the transvections `x_ij(c E_kl)` with `i != j`. The commutator
    `[t_(u,w)(c), t_(w,u')(1)] = t_(u,u')(c)` through a basis vector `w` in another column gives the transvections
    inside a column. So `L_3 >= SL_fin(N x {1,2,3}, F_3)`.
  - **Its centralizer is trivial.** An element of `E_3` centralizing `SL_fin` is `±1` on `V^3`. Now `-1` is not in
    `E_3`, since its symbol has determinant `-1`. So `C_(E_3)(SL_fin) = 1`.
  - **Minimality.** Conjugation by an element of `E_3` preserves the finitary determinant, so `E_3` normalizes
    `SL_fin`. For nontrivial `N ⊲ E_3` we get `1 != [N, SL_fin] <= N ∩ SL_fin`, and `SL_fin` is simple. So `N` contains
    `SL_fin`.
  - **Not settled here.** Whether `L_3` is all of `GL_fin(N x {1,2,3}, F_3)`, that is, whether a symbol-trivial element
    of finitary determinant `-1` lies in `E_3`.
* **Section 2.** `E_3` is Kazhdan, and it is LEA iff it is LEF. A non-LEF theorem in rank four over `F_3` is not on
  main.
* **Section 3 holds for every finite field.** The halves are LEF and retain the head. `E_3` is a proper quotient of
  their amalgam, and the Toeplitz commutator `[x_12(T), x_23(S)] = x_13(1)` is a mixed relation.

## 6. Where it stops

* **Not decided.**
  - Whether `E` is sofic.
  - Whether `E` is LEF, which by Section 2 is the same as LEA.
  - The characteristic-three analogues.
* **Firewalls.**
  - `E` is not a known open case in disguise (Section 1).
  - Amenable approximations are finite approximations (Section 2).
  - Any head-killing or nonsoficity argument must use relations mixing `S`-roots and `T`-roots, since relations inside
    one half never kill the head (Section 3).
* **What each outcome would do.**
  - **Sofic.** `binary-jacobson-el3-rank-radical-is-the-finitary-kernel` is false: a sofic approximation gives
    permutation matrices in which the head has normalized `F_2`-rank near `1/2`. In that case there is no route to
    invalidate on the L1 cylinder target. `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` has no routes.
  - **Nonsofic.** A relation-only strict deficit at two disjoint cylinders would give nonsoficity. By Section 3 that
    deficit must be carried by the Toeplitz commutators.
* **Next attempts, sharpest first.** The path-permutation LEF criterion on the rank-radical node is already dead, since
  its endomorphism `ψ` does not extend.
  1. Decide whether `E` is finitely presented. If it is, `E` is not LEF, since for finitely presented groups LEF is the
     same as residual finiteness, and every finite quotient kills the head. Then `E` is not LEA either, and soficity
     would need nonamenable approximations.
  2. Describe `ker(H_+ *_(H_0) H_- -> E)`. It contains the Toeplitz relator `[x_12(T), x_23(S)] x_13(1)^(-1)`. By
     Section 3, any obstruction lives in this kernel.
