---
rg: 2
id: compression-defects-grow-under-centralizer-closure
kind: claim
title: Compression defects only grow under centralizer closure, so kernel-saturating sources may be taken closed and closure-infranormal sources die in sofic mapping tori
distinct_from:
  compression-defects-need-strict-kernel-centralizer-towers: that records the one-step inclusion C_G(L) <= s C_G(L) s^-1 for a compressor and kills tame kernels; this proves the defect itself is monotone along the Galois closure L -> C_G(L) -> C_G(C_G(L)), with an exact compressor duality on closed pairs, and kills a class of sources rather than kernels.
  infranormal-sources-never-saturate-sofic-mapping-tori: that kills sources infranormal in the kernel; this shows its proof needs only that K normalizes C_G(L), and kills every source whose closed kernel core contains a Kazhdan subgroup infranormal in K over L, a strictly larger class because compressors only grow under closure.
  intrinsic-compression-defect-functoriality-and-saturation: that is functoriality of the defect under homomorphisms and saturation of simple cores; this is monotonicity of the defect in the source inside one fixed group, along the centralizer Galois connection.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that is the open construction problem; this reduces its witnesses to closed sources and removes the closure-infranormal ones.
artifacts:
  - research/compression-defects-grow-under-centralizer-closure-proof.md
  - research/intrinsic-compression-defect-functoriality-and-saturation.md
  - research/infranormal-sources-never-saturate-sofic-mapping-tori.md
  - research/infranormal-sources-never-saturate-sofic-mapping-tori-proof.md
  - research/sofic-groups-kill-rigid-compression-defects.md
---

**ESTABLISHED.** For `X <= G` write `X^c = C_G(X)`, and let `Comp_G(X)` and `D_G(X)` be the
compressor monoid and the intrinsic defect of (ICD1). Recall `X <= X^cc` and `X^ccc = X^c`.

## Part A: pure group theory, any group `G`, any `L <= G`

1. **(GC1) Compressor duality.** `Comp_G(L)^-1 <= Comp_G(L^c)`, hence
   `Comp_G(L) <= Comp_G(L^cc)`. On closed subgroups it is exact:
   `Comp_G(L^cc) = Comp_G(L^c)^-1`.
2. **(GC2) Monotonicity.** `D_G(L) <= D_G(L^c) = D_G(L^cc)`.
3. **(GC3) Kernel closure.** Let `K` be normal in `G` and `L <= K`. Put
   `L^ = L^cc ∩ K = C_K(C_G(L))`, the *closed kernel core*. Then `C_G(L^) = L^c`,
   `(L^)^ = L^`, and
   ```text
   Comp_G(L) <= Comp_G(L^) = Comp_G(L^c)^-1,
   D_G(L)    <= D_G(L^)    <= D_G(L^c) = D_G(L^cc).                            (GC3)
   ```

So if `D_G(L) = K` then `D_G(L^) = K`: a kernel-saturating source may be replaced by its closed
core. The replacement keeps the centralizer, only enlarges the compressor monoid, and makes
the whole defect a function of the single centralizer `Z = C_G(L)`:

```text
D_G(L^) = << [u^-1 c u, x] : u in Comp_G(Z), c in Z, x in C_K(Z) >>_G.
```

## Part B: sofic mapping tori

Let `G` be sofic and countable, `K` normal in `G`, `G/K = Z`, `K` a nontrivial Kazhdan group,
and `L <= K` any subgroup (not necessarily Kazhdan).

4. **(PT) Normalized centralizers never saturate.** If `K` normalizes `C_G(L)`, then
   `D_G(L) != K`. No soficity is used here.
5. **(CI) Closure-infranormal sources die.** Suppose some Kazhdan `Gamma` with
   `L <= Gamma <= L^` is infranormal in `K`. Then `D_G(L) != K`. More generally the conclusion
   holds when some Kazhdan `Gamma <= K`, infranormal in `K`, has `C_G(Gamma) = C_G(L)`.

Since `Comp_K(L) <= Comp_K(L^)`, a source whose compressors in `K` generate a proper subgroup
can still have an infranormal closed core. (CI) kills it, while
`infranormal-sources-never-saturate-sofic-mapping-tori` does not apply.

## What survives

A witness for (EK1) needs a source `L`, and its closed core `L^`, such that:
- `K` does not normalize `Z = C_G(L)`, equivalently `K` does not normalize `Z^c`;
- no Kazhdan `Gamma` with `C_G(Gamma) = Z` is infranormal in `K`. In particular, if `L^` is
  Kazhdan, then `Comp_K(L^)` generates a proper subgroup of `K`.

These are the survivor conditions. Each is a condition on `Z` alone.

---

### Proof

compression-defects-grow-under-centralizer-closure-proof
