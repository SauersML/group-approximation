---
rg: 2
id: subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence
kind: claim
title: If EL_3(LC(X,F_2)⋊Z) ≅ EL_3(LC(Y,F_2)⋊Z) for infinite minimal subshifts X and Y, then X and Y are strongly orbit equivalent
distinct_from:
  subshift-elementary-group-isomorphism-forces-orbit-equivalence: that is the statement over every finite field F_q, modulo the centre; this is the binary case, which is exactly the rigidity question closing the note, where G_X has trivial centre and the known isomorphism theorems that need 1/2 do not apply.
  root-preserving-subshift-el3-isos-force-orbit-equivalence: that assumes the isomorphism carries root subgroups to root subgroups; this asks it for every abstract isomorphism.
---

**ESTABLISHED** through `subshift-el3-f2-iso-soe-via-standard-isomorphisms` (sk-rigidity-merge, 2026-09-14). Let `X`,
`Y` be infinite minimal subshifts and `G_X = EL_3(LC(X,F_2) ⋊ Z)`. If `G_X ≅ G_Y`, then `X` and `Y` are strongly orbit
equivalent.

Precisely, every isomorphism `α: G_X → G_Y` is `inn(k)∘M_3(φ)|_{G_X}`, possibly after the graph automorphism, for a
ring isomorphism `φ: R_X → R_Y` (`subshift-el3-isomorphisms-are-standard-over-f2`, Theorem D of sk-orthogonality-o;
PASS-WITH-FIXES by sk-verify-25a and by sk-verify-25b, independently), and
`cantor-crossed-product-matrix-ring-iso-forces-soe` turns `R_X ≅ R_Y` into strong orbit equivalence.

This is the weaker half of the rigidity question in the note's "Questions" section; conjugacy or flip conjugacy gives
an isomorphism. The stronger half, flip conjugacy, stays open (`subshift-el3-group-isomorphism-forces-flip-conjugacy`).

## Attempts
- Standardness plus matrix-ring rigidity (route below): open at `subshift-el3-isomorphisms-are-standard-over-f2` until
  2026-09-14, when Theorem D (Frobenius bicommutants and Singer identities) established it.
  Over `F_2` at `n = 3` the Golubchik--Mikhalev and Zel'manov isomorphism theorems do not apply, and Petechuk's
  characteristic-2 exceptions are live (sk-rigidity-ring, sk-rigidity-f2).
- Root subgroups: `root-preserving-subshift-el3-isos-force-orbit-equivalence` proves the conclusion for isomorphisms
  that preserve root subgroups; recognizing root subgroups intrinsically is open (`el3-root-subgroups-are-bicommutant-closed`
  is a partial characterization, and root subgroups are never maximal abelian).
- Diagonal: isomorphisms preserving `GL_3(LC(X,F_2))` force flip conjugacy
  (`subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`); the missing step is Cartan uniqueness,
  `subshift-crossed-product-algebraic-cartans-are-conjugate`.
- Firewall: K-theory of the rings alone cannot give it, since all Sturmian systems have the same K-groups
  (sk-open-4); the order on `K_0` is needed.
