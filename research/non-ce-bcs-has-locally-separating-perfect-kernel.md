---
rg: 2
id: non-ce-bcs-has-locally-separating-perfect-kernel
kind: claim
title: A tracially satisfiable non-CE BCS has a perfect model whose group kernel separates every forbidden local character
distinct_from:
  mipstar-bcs-tracial-nonru-exists: that supplies a finite BCS with a perfect tracial model and no CE perfect model; this asks for the additional exact local structure of the chosen model's group kernel.
  perfect-completeness-constant-soundness-lcs-compiler: that seeks a machine-indexed binary linear-constraint compilation with a quantitative gap; this is a one-instance algebraic kernel-separation statement and requires no gap constant.
  character-rigid-signed-bcs-quotient: that promotes a quotient trace using uniqueness; this asks instead for exact annihilation of the forbidden local character idempotents by the perfect model's group kernel.
---

**OPEN.**  Choose the finite tracially satisfiable, non-CE Boolean
constraint system and a perfect tracial representation `theta` so that, for
every forbidden context character `chi_i`,

```text
chi_i|_(ker(theta) intersect H_i) is nontrivial.       (LSP1)
```

Equivalently, quotienting the contextual group skeleton by `ker(theta)`
annihilates every forbidden local character idempotent while preserving the
central sign.  By `forbidden-character-kernel-quotient-compiler`, `(LSP1)`
produces a nonhyperlinear quotient immediately.

For a fixed context, let `S_i` be the character support of `theta|H_i` and
put

```text
K_i=intersection_(psi in S_i) ker(psi).                (LSP2)
```

Then `(LSP1)` says that every forbidden `chi_i` is nontrivial on `K_i`.
Equivalently, every character `chi` satisfying

```text
chi|K_i=1,                    chi(J)=-1                (LSP3)
```

is allowed.  The characters in `(LSP3)` form an affine packet in
`widehat(H_i)`, and it is the smallest affine packet containing the local
support `S_i`.  Thus the exact local criterion is:

```text
affineHull(S_i) subseteq Allowed_i.                   (LSP4)
```

The unresolved issue is to preserve the global non-CE trace while arranging
these locally kernel-separable supports.
