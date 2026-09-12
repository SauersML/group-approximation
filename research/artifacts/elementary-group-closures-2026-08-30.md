# Elementary group closures — proof audit (2026-08-30)

This artifact records the independent checks used to turn five exact
arguments into Cairn routes.

## Dependency table

| Claim | External established input | Direct calculation |
|---|---|---|
| `extraspecial-spin-predicate-centralization-kills-phase` | none | nondegenerate commutator form and one quotient commutator |
| `passive-core-quotient-has-relative-rational-h2` | none | two Mayer--Vietoris sequences and the mapping-cone sequence |
| `titz-witzel-two-generator-gate-forces-macroscopic-noncommutation` | the established two-generator gate only fixes the words and mark | bi-invariant telescoping |
| `thompson-even-lamp-fp-finite-state-detector` | augmentation-lamp finite-presentation criterion; finite-dimensional invisibility of `V` | finite character-support calculation |
| `regular-dominating-quotients-preserve-amenable-subgroup-algebras` | none | induction, weak-containment kernels, and full equals reduced for amenable groups |

## Edge-case checks

1. The extraspecial argument needs `p` noncentral.  This is exactly what
   nondegeneracy detects; a central word is deliberately outside the
   firewall.  A private conjugator fixing `J` preserves the witness.  A
   balanced commutator is not incorrectly excluded: sending the private
   letter to the commutator witness gives an explicit finite quotient.
2. In the passive-core amalgam the edge generator maps to the sole rational
   `H_1` generator of `BS(1,4)` and to zero in `D_infinity`.  Hence the edge
   map is an isomorphism, not merely nonzero.  In the Bruhat--Tits amalgam
   both vertex `H_1` groups vanish rationally, so the edge's one-dimensional
   `H_1` becomes `H_2` of the total group.  The cone calculation never uses
   injectivity of the quotient map.
3. In the Titz--Witzel estimate `c=u^2au^2`, not a conjugate.  Comparing it
   with `u^4` is nevertheless exact after bi-invariant cancellation.  The
   limsup lower bounds follow pointwise from the upper bounds; no common
   maximizing subsequence is assumed.
4. An infinite commuting family of involutions on `C^d` still has at most
   `d` simultaneous characters.  Invariance of a character of the even lamp
   module means its representing function changes by a constant; those
   constants form a homomorphism `V->F_2`.  Killing that homomorphism before
   invoking transitivity is essential.
5. The weak-containment convention is `lambda_G prec pi`, hence
   `ker(pi)<=ker(lambda_G)`.  The restriction of `lambda_G` to `H` is a sum
   of regular `H`-representations, so its kernel on `C^*(H)` is precisely the
   full-to-reduced kernel, not merely a larger ideal.
