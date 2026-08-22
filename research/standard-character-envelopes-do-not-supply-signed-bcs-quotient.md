---
rg: 2
id: standard-character-envelopes-do-not-supply-signed-bcs-quotient
kind: claim
title: CDI, ordinary wreath, and Thompson-simple envelopes do not supply the unique signed BCS quotient
distinct_from:
  cdi-character-cannot-be-promoted-by-regular-corners: that computes why regular restriction and finite-support corners do not recover the CDI character; this audits the stronger unique-trace quotient proposal and its compatibility with quotient presentations.
  central-character-rigid-sector-forbids-relator-quotients: that is the abstract faithful-sector kernel theorem; this applies it and elementary trace-simplex tests to the three standard envelope families.
---

None of the three standard representation-enveloping operations supplies
`character-rigid-signed-bcs-quotient`.

1. **CDI property-T envelope.**  The Chifan--Drimbe--Ioana construction
   gives a property-T group `H` and a factor-generating non-CE character
   `chi`.  The same group also has its regular and trivial characters.
   Therefore its full group algebra is not monotracial.  More importantly,
   the existence of `chi`, which is neither finite-dimensional nor regular,
   is itself incompatible with the regular-versus-finite-dimensional
   character dichotomy required by the signed-quotient route.  Property
   `(T)` is not a substitute for that dichotomy.  A direct-product finite
   central sign merely replaces the selected corner by `C*(H)` and preserves
   all these traces; a non-split finite central cut has twisted regular trace,
   not `chi`, by `cdi-character-cannot-be-promoted-by-regular-corners`.

2. **Ordinary wreath envelope.**  If

   ```text
   W=A^(X) rtimes H -> H                                (SCE1)
   ```

   is the usual lamp-killing quotient and `H` is nontrivial, the trivial
   and regular traces of `H` pull back to two distinct traces of `C*(W)`.
   For a direct-product finite central mark `C x W`, every faithful marked
   corner is isomorphic to `C*(W)`, so it is again multitracial.  Permuting
   finitely many copies or matrix-amplifying the corner retains these traces.
   Thus the ordinary wreath universality mechanism and trace uniqueness point
   in opposite directions.

3. **Thompson-simple envelope.**  Thompson `V` has the regular/trivial trace
   segment, and `thompson-v-central-extensions-split` says every central
   extension splits.  Hence a finite central marked corner is just a copy of
   `C*(V)` and is not monotracial.  Simplicity also means a representation
   obtained by imposing group relators has either trivial or faithful group
   kernel.  It cannot both add nontrivial BCS group relations and retain an
   infinite factor-generating image.  An analytic quotient which removes the
   trivial trace is a different operation; if it has the regular GNS trace,
   proving that its trace is non-CE already proves `L(V)` non-CE.

The useful positive residue is therefore very narrow.  The explicit Deligne
faithful central-character fibre already supplies the required unique source
trace.  But by `central-character-rigid-sector-forbids-relator-quotients`,
its BCS map cannot be installed by a quotient presentation.  One must build
an analytic quotient inside the full-to-reduced kernel, equivalently identify
the fixed non-CE BCS GNS factor with the Deligne twisted regular factor.  None
of CDI universality, ordinary wreath universality, or simple-group embedding
performs that identification.

The proof is `standard-character-envelope-audit-proof`.

