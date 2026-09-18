---
rg: 2
id: infranormal-sources-never-saturate-sofic-mapping-tori
kind: claim
title: In a sofic mapping torus of a Kazhdan kernel no source infranormal in the kernel saturates the kernel, for every number of beads, because saturation makes the kernel nilpotent
distinct_from:
  infranormal-kernel-sources-die-in-sofic-mapping-tori: that kills gcd 1 and kernels with a unique maximal normal subgroup and leaves every necklace with g >= 2 beads alive; this kills every necklace, for every g, by adding the degree-zero root lemma and the bead-residue intersection central series.
  necklace-defects-need-deep-bead-overlaps: that kills g = 2 and amenable deep overlaps and leaves non-amenable overlaps with g >= 3 alive; this kills all of them with no condition on the overlaps, and supersedes its (NB4) kill.
  compression-defects-need-strict-kernel-centralizer-towers: that kills kernels with tame Kazhdan centralizer towers, a condition on the kernel; this kills a condition on the source (infranormal in K) over an arbitrary Kazhdan kernel.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that is the open construction problem; this proves every witness has a source that is not infranormal in its kernel.
artifacts:
  - research/infranormal-sources-never-saturate-sofic-mapping-tori-proof.md
  - research/infranormal-kernel-sources-die-in-sofic-mapping-tori.md
  - research/necklace-defects-need-deep-bead-overlaps.md
  - research/sofic-groups-kill-rigid-compression-defects.md
---

**ESTABLISHED (obstruction).** Setting, as in
`infranormal-kernel-sources-die-in-sofic-mapping-tori`:
- `G` is a countable sofic group, `K` is normal in `G` with `G/K = Z`, and `s in G` has degree 1;
- `K` is a nontrivial Kazhdan group;
- `L <= K` is Kazhdan and infranormal in `K` (`Comp_K(L)` generates `K`);
- `N = <<L>>^K`, `A_j = s^j N s^-j`, and `D_G(L)` is the intrinsic defect (ICD1).

When a strict compressor exists, normalize so strict degrees are positive, let `P` be their
semigroup and `g = gcd P`, and put

```text
W_rho = < A_j : j = rho (mod g) >,      W_S = intersection_{rho in S} W_rho,
I_k   = product over |S| = k of W_S     (S a set of residues mod g).          (BW)
```

**Theorem.**
1. **(DZ) Roots have degree zero.** `C_G(L) <= K`. So every root `u c u^-1` lies in
   `C_K(A_(deg u))`, and every defect generator lies in `C_K(A_m) ∩ N` with `m in P`.
2. **(BF) Bead factorization with ownership.** If `D_G(L) = K`, then for every tuple
   `(j_rho)` with `j_rho = rho (mod g)`:
   ```text
   K = (C_K(A_(j_0)) ∩ W_0) (C_K(A_(j_1)) ∩ W_1) ... (C_K(A_(j_(g-1))) ∩ W_(g-1)).
   ```
3. **(NC) Central series.** If `D_G(L) = K`, then `[I_k, K] <= I_(k+1)` for `1 <= k <= g`,
   with `I_1 = K` and `I_(g+1) = 1`. So `K` is nilpotent of class at most `g`.
4. **(Kill)** `D_G(L) != K`. A nilpotent Kazhdan group is finite, and a finite `N` cannot be
   strictly compressed.

No torsion-freeness, finite presentation, quotientlessness, or condition on the overlaps is
used. Soficity enters only through `C_G(L) = C_G(N)` (IS0 of the parent node).

## What this kills

- **Every infranormal source, every necklace.** In `torsion-free-sofic-extrinsic-kazhdan-defect-kernel`
  and `split-cyclic-kazhdan-defect-exact-mf-radical`, a sofic `G = K semidirectProduct Z` with
  `D_G(L) = K` must have a Kazhdan source `L` that is **not** infranormal in `K`. This closes the
  necklace survivor left by Attempts 16 and 17, for `g >= 3` as well as `g <= 2`.
  - The need "Kazhdan kernel realizing g >= 3 necklaces, or a kill of g >= 3" is answered by
    the kill.
  - The calibration example of `necklace-defects-need-deep-bead-overlaps` is recovered without
    computing `H^+`.
- **Invariant.** The bead-residue intersection filtration `I_k` of (BW), which is `G`-invariant.
- **Step where every member dies.** (DZ) puts each defect generator inside its own bead `A_e` as
  well as inside the centralizer `C_K(A_(e+m))` of a deeper bead of the same residue. So in
  (BF) the factor of residue `rho` both centralizes `A_(j_rho)` and lies in `W_rho`. An element
  lying in the beads of the residues in `S` then commutes with every factor except those of
  residues outside `S`, and the commutator lands in beads of one more residue. After `g` steps
  it is central, so `K` is nilpotent.
- **What survives.** Sources `L` whose compressors in `K` generate a proper subgroup of `K`.
  For such sources, `N` and the translates `A_j` need not be normal in `K`, and neither the
  finite-product step nor the commutator calculus of (NC) is available.

Proof: `infranormal-sources-never-saturate-sofic-mapping-tori-proof`.
