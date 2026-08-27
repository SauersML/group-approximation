---
rg: 2
id: jnvwy-ldpc-synchronization-audit-proof
kind: route
title: Read the tensor-code theorem against the repeated-overlay interface
target: jnvwy-pasting-does-not-close-ldpc-synchronization
requires: []
---

Primary-source audit of Ji--Natarajan--Vidick--Wright--Yuen,
[Quantum soundness of testing tensor codes](https://arxiv.org/abs/2111.08131).

Definition 3.1 places all projective measurements of a tracial strategy in
one von Neumann algebra `A`.  Lemma 4.4 constructs `{G_c} subset A`, and the
proof of Theorem 4.1 projectivizes and completes that measurement in `A`.
This proves the positive same-algebra assertion.

Theorem 4.1 and Lemmas 4.2--4.4 state the parameter dependence recorded in
`(JTP1)`: the self-improvement and pasting errors have polynomial dependence
on `m,t,r`, the pasting parameter satisfies `r>=12mt`, and the residual term
is `exp(-Omega(r/m^2))`.  These statements do not provide one modulus
independent of a growing tensor dimension.

Figure 1 and Definition 3.2 give the geometry.  The line test samples one of
the `m` axis directions through a point.  The subcube commutation test samples
`j in {1,...,m}`, a nested subcube, and two independent points in it, then
asks for their joint outcome.  Therefore the theorem assumes both the common
point names and the growing incidence which occurrence splitting is meant to
remove.

Finally, a binary `[n,k,d]` base code has `2^k` line-codeword outcomes and
`C^(tensor m)` has vector-space dimension `k^m`.  The elementary dichotomy in
the claim follows immediately and does not depend on hidden constants in the
paper.
