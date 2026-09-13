---
rg: 2
id: shell-isotropy-germs-fail-bhm-germ-hypothesis
kind: claim
title: Shell envelopes of inputs that are not virtually cyclic fail the germ hypothesis of the Belk–Hyde–Matucci finiteness corollary
distinct_from:
  shell-cantor-embeddings-are-finite-germ-extensions: that realizes E_nu as a finite germ extension of V and identifies its isotropy germ group; this shows that group is too large and too unnormalized for the germ hypothesis of the finiteness corollary.
  decidable-inputs-have-fp-shell-stabilizers: that asks for finite presentation of singularity stabilizers, the input of the general finite germ extension theorem; this rules out the special corollary that would derive those stabilizers from the germ group.
artifacts:
  - research/artifacts/shell-envelope-local-tests-2026-09-13.md
---

Let `P` be infinite and finitely generated, let `nu` be any enumeration,
and let `E_nu` be the shell envelope with base point `p = 0^infinity`.
Its isotropy germ group is `Q = (E_nu)_p = <germs of rho(P), tau>`,
inside the near permutation group of `N`, and `(V)_p = <tau>`.
Then:

1. `<tau>` is not normal in `Q`.
2. If `P` is not virtually cyclic, then `|Q : <tau>| = infinity`.

Consequently, for `P` not virtually cyclic, hypothesis (3) of
Belk–Hyde–Matucci Corollary 2.10 (arXiv:2407.03149; Theorem 1.1 is its
`F_infinity` case) fails at `p`. That hypothesis reads: either
`|(G)_p : (B)_p| < infinity` for every singular `p`, or `(B)_p` is
normal in `(G)_p` with quotient of type `F_n`. So that corollary never
certifies finiteness properties of such a shell envelope. Any use of
that paper must go through its Theorem 2.1, which needs the groups
`SingFix(M,M') = S(M,M')` with `|M'| <= n` to have type `F_n`.

This says nothing about whether `E_nu` or the groups `S(M,M')` are
finitely presented.
