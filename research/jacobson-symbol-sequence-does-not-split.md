---
rg: 2
id: jacobson-symbol-sequence-does-not-split
kind: claim
title: The symbol sequence of the binary Jacobson elementary group does not split, not even over Z/3 x Z, because an odd-order constant cuts an isotypic block of nonzero Fredholm index
distinct_from:
  binary-jacobson-gkm-semidirect-hypotheses-fail: that checks the hypotheses of the GKM extension theorem on the kernel and records that splitting of the symbol sequence is "a separate and unaddressed question"; this settles that question negatively for every n >= 3, so the semidirect form needed by that theorem, or by any other semidirect-product permanence result, is unavailable for EL_n(J) itself.
  jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group: that uses the total Fredholm index to show every symbol has determinant 1 (MQ1); this uses an equivariant index, taken on the isotypic block of an odd-order finite subgroup, whose value is not forced to vanish, to show that no section exists.
  jacobson-one-sided-symbol-preimages-are-lef: that proves the preimages of the one-sided subgroups SL_n(F_2[z]) and SL_n(F_2[z^-1]) are LEF, and over those subgroups the sequence splits by analytic Toeplitz lifts; this shows the splitting cannot extend to the two-sided symbol group, and names the exact finite piece (Z/3 x Z) where it breaks.
  binary-jacobson-mark-dichotomy-holds-from-rank-two: that identifies the kernel L = GL_fin and the dichotomy for the MF radical; this is a statement about the extension class, not about any approximation.
---

**ESTABLISHED** (route `jacobson-symbol-sequence-does-not-split-proof`).

**Notation** (as in `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`).
- `J = F_2<S,T | TS = 1>` acts on `V_+ = F_2^(N)` by `S e_k = e_(k+1)`, `T e_0 = 0` and `T e_(k+1) = e_k`.
- `A = F_2[z,z^(-1)]`, with symbol `pi : S -> z, T -> z^(-1)`. The kernel of `J -> A` is the ideal of finite-rank operators.
- `n >= 3`, `E = EL_n(J) = GL_n(J)` acting on `V = V_+^n`, and `Q = SL_n(A) = EL_n(A)`.
- The symbol sequence is `1 -> L -> E -> Q -> 1`, with `L = GL_fin(V)`.

**Theorem.** Put:
- `c = diag(c_0, 1, ..., 1)`, where `c_0 = [[0,1],[1,1]]` has order 3 in `GL_2(F_2)`. So `c` is a constant element of order 3 in `Q`.
- `h = diag(z, z, z^(-2), 1, ..., 1)`, which lies in `Q`.

Then `c` and `h` commute, and generate `A_0 = <c> x <h> ≅ Z/3 x Z <= Q`, but:

```text
(NS)  no element c~ in E with symbol c and c~^3 = 1 commutes with any element h~ in E with symbol h.
```

Hence the preimage of `A_0` in `E` does not split over `A_0`. In particular **the symbol sequence of `EL_n(J)` does not split, for every `n >= 3`.** It also does not split over any subgroup of `Q` that contains a conjugate of `c` together with a nonzero power of `h`.

**General form (G).** Let `F <= GL_n(F_2)` be a finite subgroup of odd order, and let `e` be a central idempotent of `F_2[F]`.
- Every `g in Q` that centralizes `F` restricts to an `A`-linear automorphism of the free `A`-module `e A^n`.
- Its determinant there is `lambda z^(m_e(g))`, with `lambda in F_2^x = {1}`.
- If `m_e(g) ≠ 0` for some `e`, then no homomorphism `F -> E` lifting `F` has a lift of `g` in its centralizer.
- The theorem is the case `F = <c>`, `e = c + c^2`, `m_e(h) = 2`.

**Why the total index does not see it.** The Fredholm index of any lift of `g` is `-deg det g = 0`; this is (MQ1). Here the index is taken on the block that an exact odd-order lift cuts out. On that block the index is `-m_e(g)`, which is nonzero.

**What is not settled.**
- Every finite-order element of a congruence subgroup `ker(SL_n(A) -> SL_n(A/fA))`, with `f` a nonunit, is unipotent.
- So (G) says nothing about the finite-index, odd-torsion-free subgroups of `Q`.
- **Virtual splitting** remains open: does the sequence split over some finite-index subgroup of `Q`?
- If it does, then `E` contains the semidirect product `L x| Gamma` with finite index, and hyperlinearity of `EL_n(J)` reduces to hyperlinearity of a genuine semidirect product of `L` by a Kazhdan residually finite group.

**Impact.**
- This settles the question left open in `binary-jacobson-gkm-semidirect-hypotheses-fail`.
- It kills every approach that treats `EL_n(J)` as `L x| Q`: semidirect-product permanence theorems, and approximations built from an action of `Q` on `L` by automorphisms that are pulled back along a section.
- What remains is the twisted form, `R x|_(alpha,omega) Q` at the von Neumann level, or a splitting over a finite-index subgroup.
- The two one-sided sections over `SL_n(F_2[z])` and `SL_n(F_2[z^(-1)])` (`jacobson-one-sided-symbol-preimages-are-lef`) agree on the constants. By (NS), no choice of sections over the halves extends to `Q`.
- **Limits.** The argument uses the Fredholm index of the defining action on `V`, where the kernel acts by finite-rank perturbations. It says nothing about whether the 2-cocycle `omega` of the crossed-product decomposition `L(E) = R x|_(alpha,omega) Q` is a coboundary in `U(R)`. In the trace representation, elements of `L` are far from `1`, and there is no index. That von Neumann-level question stays open in `agent-leavitt-not-bcs-negative-root-corner`.
