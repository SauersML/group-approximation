---
rg: 2
id: normalizer-kernel-generation-forces-haar-action
kind: claim
title: Kernel generation forces a Haar algebraic normalizer action
distinct_from:
  haar-algebraic-actions-have-permutation-koopman-spectrum: that derives spectral and stabilizer-moment consequences from an already algebraic Haar action; this reconstructs the compact dual directly from a regular-trace group of Cartan normalizers under a kernel-generation hypothesis.
  full-group-subgroup-trace-generation-dichotomy: that treats undecorated full-group unitaries and separates free from nonfree actions; this allows arbitrary phase-decorated Cartan normalizers and identifies the extra hypothesis which forces algebraicity.
---

Let `(M,tau)` be finite with a diffuse Cartan algebra `A`, and let
`Gamma <= N_M(A)` be a countable group of normalizing unitaries such that

```text
tau(g)=0 for g != 1,             W*(Gamma)=M.            (NK1)
```

Put `K=Gamma cap U(A)`.  If `W*(K)=A`, then `K` is abelian, its canonical
map into `M` extends to a trace-preserving identification

```text
A = L(K) = L^infinity(K-hat, Haar),                      (NK2)
```

and conjugation by `Gamma/K` acts on `K-hat` by continuous group
automorphisms.  Choosing a section of `Gamma -> Gamma/K` identifies `M=L(Gamma)`
with the corresponding Haar algebraic crossed product, with the section's
`K`-valued extension cocycle if the extension does not split.

Thus phase-decorated normalizers force precisely the desired compact-abelian
Haar structure once their base-unitary kernel generates the Cartan.  The
substantive remaining issue is kernel generation; canonical trace and total
generation alone do not imply it.

