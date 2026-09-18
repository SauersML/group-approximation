---
rg: 2
id: abelianized-cover-twist-fox-section-proof
kind: route
title: Crossed homomorphisms from the free group are Fox-free, and the character degree retracts the regular joint spectrum
target: abelianized-cover-twist-vanishes-iff-equivariant-fox-section
requires:
  - free-abelianized-cover-is-torsion-free
---

The claim file contains the complete proof.  Here is its skeleton.

1. **(FS1).**  A splitting of the pushout `E'_phi` is the same as a crossed
   homomorphism `c : E -> C(X,T)` with `c|_M = phi`.  Pulled back to the
   free group, such a `c` is determined by its values `f_i` on the basis,
   through the fundamental formula of Fox calculus.  So it is the same as
   an equivariant extension of `phi` along the Lyndon inclusion
   `Fox : M -> ZG^n`.  Evaluating at points of `X` turns that extension into
   a continuous equivariant section of `pi : (T^n)^G -> M^` over the joint
   spectrum.  The converse is the same construction run backwards.  Only
   elementary group cohomology and Fox calculus are used.
2. **(FS3).**  Compose a section of the pushout with `b rho(e)`.  This gives
   a homomorphism from `G` into the corona, which is trivial by the full
   radical.
3. **(FS4).**
   - The regular representation has joint spectrum `M^ = T^J`.
   - Bruschlinsky's theorem, together with continuity of Cech cohomology,
     gives an equivariant degree retraction `C(M^,T) -> M` onto the
     characters.
   - A section would therefore give a crossed homomorphism `E -> M` that is
     the identity on `M`, hence a splitting `G -> E`.
   - That splitting is impossible when `G` has torsion, because the cover is
     torsion-free by the prerequisite.

Background imports used verbatim as standard facts:
- Lyndon's injectivity of the relation-module sequence;
- Bruschlinsky's `[Y,T] = H^1_Cech(Y;Z)` for compact Hausdorff `Y`;
- continuity of Cech cohomology under inverse limits.
