---
rg: 2
id: free-abelianized-cover-fd-radical-is-commutator
kind: claim
title: Over a base with full MF radical the free abelianized cover has no finite-dimensional theory beyond its abelianization
distinct_from:
  free-abelianized-cover-has-nontrivial-fd-radical: that only needs the base to be non-residually-finite and only produces one nontrivial element of the radical; this needs the much stronger full-MF-radical hypothesis and computes the radical exactly, as the whole commutator subgroup.
  full-mf-radical-uniform-asymptotic-collapse: that is an equivalence between a full MF radical and pointwise triviality of every asymptotic representation of the same group; this transports a full MF radical downstairs into an exact finite-dimensional statement about a different group, the cover, whose own MF radical is left completely undetermined.
  full-mf-radical-forces-perfect-commutator-bound: that derives perfectness and a quadratic displacement bound for the group carrying the hypothesis; this derives a representation-theoretic collapse for the cover above it, and the cover is never perfect -- its abelianization is free abelian of full rank.
artifacts:
  - research/artifacts/torsion-free-cover-fd-radical-and-heisenberg-2026-09-08.md
---

**ESTABLISHED.**  Keep the notation of
`free-abelianized-cover-has-nontrivial-fd-radical`: a countable `G`, a
generating set `X`, a dummy generator `z` with `q(z) = 1`, and

```text
F = F(X u {z}),   R = ker q,   E = F/[R,R],   A = R/[R,R].
```

Suppose `G` has a **full MF radical**, `Rad_MF(G) = G` -- equivalently, by
`universal-mf-quotient`, every homomorphism from `G` to a countable MF group
is trivial.  Then every exact finite-dimensional unitary representation of `E`
has abelian image, and

```text
Rad_fd(E) = [E,E].                                                    (FDC1)
```

Moreover `E/[E,E]` is free abelian on `X u {z}`, and if `G != 1` then
`[E,E] != 1`, so the radical in `(FDC1)` is nontrivial.

Equivalently: the exact finite-dimensional unitary theory of the cover is
exactly the character theory of a free abelian group, and sees nothing else.

**This is not a non-MF criterion, and does not close the transfer.**  The
conclusion `(FDC1)` is a statement about `Rad_fd`, the larger radical.  The
group `E` is non-MF exactly when `Rad_MF(E) != 1`, and
`rational-heisenberg-fd-radical-is-commutator-and-mf` exhibits a torsion-free
countable group satisfying the full conclusion `(FDC1)` which is nevertheless
operator MF.  So `(FDC1)` cannot be upgraded, and
`free-abelianized-cover-reflects-mf` remains the open implication that a
torsion-free transfer needs.

Inputs with a full MF radical are freely available -- see
`defect-saturation-full-mf-radical` for a finitely presented one -- so the
hypothesis here is not the obstacle.  The obstacle is the gap between the two
radicals.
