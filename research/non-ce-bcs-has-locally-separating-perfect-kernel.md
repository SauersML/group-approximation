---
rg: 2
id: non-ce-bcs-has-locally-separating-perfect-kernel
kind: claim
title: A tracially satisfiable non-CE BCS has a perfect model whose group kernel separates every forbidden local character
distinct_from:
  mipstar-bcs-tracial-nonru-exists: that supplies a finite BCS with a perfect tracial model and no CE perfect model; this asks for the additional exact local structure of the chosen model's group kernel.
  perfect-completeness-constant-soundness-lcs-compiler: that seeks a machine-indexed binary linear-constraint compilation with a quantitative gap; this is a one-instance algebraic kernel-separation statement and requires no gap constant.
  character-rigid-signed-bcs-quotient: that promotes a quotient trace using uniqueness; this asks instead for exact annihilation of the forbidden local character idempotents by the perfect model's group kernel.
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that proves this condition is equivalent to the existence of a tracial non-CE LCS and hence to a nonhyperlinear group; this retains the condition as the concrete local-kernel formulation consumed by the quotient compiler.
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

`locally-affine-support-bcs-is-exactly-the-lcs-boundary` shows that this is
an exact reformulation of the binary LCS endpoint, not a weaker consequence
of the presently known non-CE BCS source.

## Trace-modification audit

`affine-ghosts-survive-recoverable-tracial-dilations` rules out the standard
ways of modifying the supplied witness.  Any enlarged local support which
affinely and surjectively decodes to the original support carries every
original affine ghost.  Matrix amplification, finite central/direct sums,
classical polarization, and tagged diagonal tensor products all have such a
decoder.  Direct sums are worse: the hull of their union contains the hull
of every summand.

Discarding the tensor tag removes the decoder, but also removes the expected
copy of the original contextual algebra, so non-CE of the output no longer
follows from the input.  Inside one fixed tracial model, a support-shrinking
compression remains tracial only on a central summand.  Hence the only live
model-selection operation is to find a non-CE central/factor component whose
supports already satisfy `(LSP4)`.  Otherwise one needs a genuinely global,
nonrecoverable compiler with a new proof of non-CE; neither is furnished by
amplification or polarization.

Slofstra's wagon-wheel picture method does not weaken `(LSP4)`.
`wagon-wheel-stops-before-bcs-groupification` proves that fixed wagon fillings
give excellent dimension-free defect transfer **after** an ordinary source
group has been constructed.  Before that step, scalar solutions of every
finite local wagon/LCS fragment project to an affine visible packet.  Hence
preserving the chosen trace support forces the packet to contain its affine
hull, and excluding forbidden scalar solutions is possible only under
`(LSP4)`.  Bounded local picture surgery therefore returns exactly to this
claim rather than bypassing it.
