---
rg: 2
id: caprace-kassabov-hyperbolic-kazhdan-alternating-quotients
kind: claim
title: Some infinite hyperbolic groups with property (T) have infinitely many alternating quotients
distinct_from:
  sp21-lattice-few-alternating-and-large-rank-quotients: that is the open assertion that an arithmetic Sp(2,1) lattice has only finitely many alternating and large-rank simple quotients; this is the established fact that hyperbolicity and property (T) alone do not bound the alternating quotients
---

**ESTABLISHED (literature import).** There are infinite word-hyperbolic groups
with Kazhdan's property (T) that surject onto infinitely many alternating
groups. The examples are explicit finite presentations.

Source: P.-E. Caprace and M. Kassabov, *Tame automorphism groups of polynomial
rings with property (T) and infinitely many alternating group quotients*,
arXiv:2210.00730v3 (25 May 2023). Quoted from the PDF text (see the citation
route for how it was read):

- Abstract: "As a consequence, we obtain explicit presentations of Gromov
  hyperbolic groups with property (T) and infinitely many alternating group
  quotients."
- §1.2, on the KMS groups `G_HC(1)(p) = <a,b,c | a^p, b^p, c^p, ...>` and
  `G_HBC(3)(p)`: "By [7, Theorem 1.3], those two finitely presented groups are
  infinite hyperbolic as soon as p is an odd prime; they have property (T) if
  p ≥ 7 (resp. p ≥ 11)."
- Corollary 1.4: for a prime `p ≥ 5`, `G_HC(1)(p)` maps onto an alternating
  group for each prime `ℓ ≥ 3`, of degree growing with `ℓ`. The degree formula
  is not reproduced here because the extracted text garbles it.
- §1.2 also gives a second, non-explicit route to such groups:
  - every finitely presented Kazhdan group is a quotient of a hyperbolic
    Kazhdan group (their reference [4, Cor. 1.2]);
  - `Aut(F_n)` is finitely presented, has property (T) for `n ≥ 4`, and has
    infinitely many alternating quotients.

## What it changes here

- **Fence on the lattice route.** A proof of
  `sp21-lattice-few-alternating-and-large-rank-quotients` cannot use only the
  hyperbolicity and property (T) of the lattice. It has to use arithmeticity or
  superrigidity, which bounded-rank families already exploit.
- **Scope of the fence.** The KMS examples have torsion, since their generators
  have order `p`. So they say nothing about the torsion-free separation form
  `sp21-noncongruence-simple-kernels-separate-points`. Whether some element of
  infinite order in them has bounded order along infinitely many of their
  alternating quotients was not checked.

Imported; see `caprace-kassabov-hyperbolic-kazhdan-alternating-citation`.
