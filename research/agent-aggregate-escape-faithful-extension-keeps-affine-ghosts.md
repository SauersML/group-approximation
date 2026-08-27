---
rg: 2
id: agent-aggregate-escape-faithful-extension-keeps-affine-ghosts
kind: claim
title: A faithful groupification with an extended perfect trace cannot improve local kernel separation
distinct_from:
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: That identifies local affine support with the existence of a non-CE LCS; this proves invariance of the local obstruction under arbitrary faithful group embeddings which extend the fixed perfect representation.
  non-ce-trace-does-not-promote-to-subgroup-character-gap: That computes the affine hull visible to the GNS projective kernel of one trace; this shows why Slofstra-style embeddings and ucp triangle sections cannot enlarge the relevant kernel intersections.
  finite-packet-central-sign-cannot-enforce-nonlinear-support: That uses induction to retain every character in finite packet irreducibles; this permits arbitrary infinite overgroups but fixes the original perfect representation on the embedded contextual group.
---

Let `Gamma` be a contextual group, let `H_c<=Gamma` be its finite abelian
context subgroups, and let

```text
theta:Gamma->U(M)                                      (FEG1)
```

be a fixed perfect tracial representation.  Suppose

```text
iota:Gamma->Omega
```

is injective and `theta` extends to a tracial representation
`Theta:Omega->U(N)` in the sense that `Theta o iota` is unitarily equivalent
to `theta` (amplification does not change the argument).  Then for every
context

```text
iota(H_c) intersect ker(Theta)
   =iota(H_c intersect ker(theta)).                    (FEG2)
```

The same identity holds for the projective kernel after recording the scalar
phase.  Thus no faithful enlargement which preserves the chosen perfect
model can add a local kernel separator for a forbidden character.

Write `S_c` for the character support of `theta|H_c`.  The characters which
satisfy every local kernel equation in `(FEG2)` are exactly

```text
Aff(S_c).                                              (FEG3)
```

Hence if a forbidden assignment belongs to
`Aff(S_c) minus S_c`, that affine ghost survives every such faithful
groupification.  If `N normal Omega` lies in `ker(Theta)`, then

```text
iota^(-1)(N) intersect H_c <=ker(theta) intersect H_c, (FEG4)
```

so quotienting the overgroup does not improve the conclusion while retaining
the perfect representation.

This closes the direct use of the Slofstra wagon-wheel embedding for the
kernel compiler.  The theorem embeds a finitely presented group and its
distinguished involutions in a solution group, but it does not assert that an
arbitrary prescribed finite-tracial representation extends.  There are only
two cases:

1. the chosen non-CE perfect representation does not extend, so the embedding
   does not provide perfect completeness for the intended construction;
2. it does extend, in which case `(FEG2)--(FEG3)` retain every original
   affine ghost.

Inducing a representation from `Gamma` to an infinite-index overgroup does
not repair this: the induced Hilbert representation generally has no finite
normalized trace.  The group embedding alone preserves nontriviality of a
word, not the designated tracial state.

The triangle ucp data does not alter `(FEG2)` either.  A ucp section of a
group-C-star quotient need not send canonical group unitaries to unitaries
or preserve products, so it supplies no group homomorphism `Theta` and no
normal subgroup inside `ker(Theta)`.  If it happens to be multiplicative on
an original context, its restriction is an honest representation and
`(FEG2)` applies.  The quantitative obstruction to simultaneously fixing
both triangle sides therefore confirms, rather than bypasses, the kernel
problem.

Pure finite Bass--Serre syntax is also exhausted.  An iterated finite graph
of finite groups is virtually free and residually finite.  A finite quotient
can be chosen injective on every fixed context subgroup, and its regular
representation gives every context character positive Plancherel mass.
This is the exact countermodel in
`residually-finite-models-refute-filtered-wandering-return` and the stationary
type calculation in
`finite-packet-graph-atlases-have-a-regular-stationary-flow`.  Hence no
unfilled finite graph of finite groups can annihilate a forbidden Reynolds
atom.  If extra filling relators are added, their normal closure—not the
Bass--Serre gluing—must supply the separator in `(FEG4)`, so the affine-kernel
test applies to those relators directly.

Consequently `forbidden-character-kernel-quotient-compiler` cannot be
completed for a fixed nonlinear-support perfect BCS trace by embedding it in
a larger group.  One must instead construct a **different** non-CE perfect
trace whose local supports already satisfy

```text
Aff(S_c) subseteq Allowed_c                            (FEG5)
```

for every context.  By
`locally-affine-support-bcs-is-exactly-the-lcs-boundary`, obtaining `(FEG5)`
is exactly the perfect-complete non-CE LCS/nonhyperlinear frontier, not a
remaining wagon-wheel bookkeeping step.

DERIVATION
agent-aggregate-escape-faithful-extension-kernel-proof
