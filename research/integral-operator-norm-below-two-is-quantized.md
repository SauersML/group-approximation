---
rg: 2
id: integral-operator-norm-below-two-is-quantized
kind: claim
title: Over every group a self-adjoint integral matrix of norm below two has norm 2cos(pi/q) and purely atomic spectrum at cosines of rational angles
distinct_from:
  integral-spectra-of-small-capacity-are-finite: that derives finite spectrum from a capacity bound; this is its consequence for the operator norm, through Kronecker's theorem
  torsion-free-small-spread-spectra-are-integer-atomic: that assumes a torsion-free group and a spectral interval shorter than four and gets integer masses; this holds over every group, assumes only norm below two, and gets cosine atoms with rational Galois-equal masses
  finite-spectrum-integral-elements-obey-determinant: that proves rational Galois-equal masses once the spectrum is finite; this supplies finiteness and the cosine form from the norm alone
---

**ESTABLISHED** by `integral-operator-norm-quantization-proof`. Unreviewed.

Let `G` be any group and `A in M_n(Z[G])` self-adjoint and nonzero, acting on
`l^2(G)^n`.

1. `||A|| >= 1`.
2. If `||A|| < 2`, then `||A|| = 2cos(pi/q)` for some integer `q >= 2`. The
   spectrum of `A` is finite and lies in `{2cos(pi p/q') : p, q' in N}`, and the
   spectral measure is purely atomic, with rational masses that are equal on
   Galois conjugates.
3. **Either `||A|| = 1` and `A^2` is a projection, or `||A|| >= sqrt 2`.**

Thom proves 2 and 3 for integer operators, hence for integral group rings of
sofic groups (arXiv:math/0701294v3, Theorem 6.1 (ii) and Corollary 6.5). He
introduces 3 as "an easy corollary of the quantization theorem, for which we do
not know any elementary proof." Here both hold for every group, with no
approximation: Pólya's rationality theorem replaces the sofic models.

**Reading for the determinant problem.** Norm quantization below 2 is
unconditional over every group. The volume bound `det >= 1` is open exactly
where the spectrum has capacity at least one, which is where Pólya's theorem is
silent.

Literature check, bounded: Thom 2007 and Lück arXiv:1901.00827v2 were read; the
all-groups form was not found there.
