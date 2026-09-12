# Audit: Z-stable upper-semicontinuous fields and the first-factor firewall

Date: 2026-08-30

Claim: `stw81-z-stable-usc-fields-reduce-to-first-factor-map`.

## Globalization and bounds

1. Hirshberg--Rordam--Winter Theorem 4.6 requires a separable arbitrary
   `C_0(X)`-algebra, finite-dimensional locally compact metrizable base, and
   a K1-injective strongly self-absorbing algebra.  All hypotheses hold for
   `D=Z`; continuity and local triviality are not hidden assumptions.

2. The simple Z-stable nuclear-dimension-one theorem covers unital fibres;
   the Castillejos--Evington nonunital theorem covers the remaining simple
   fibres.  The explicit non-AF hypothesis excludes dimension zero.

3. Substitution of fibre dimension one into the proved USC product formula
   gives `2dim(X)+1`, hence three in base dimension one.  Evaluation
   quotient monotonicity gives the lower bound.

## First-factor reduction

4. The nuclear dimension of a star-homomorphism is at most that of its
   domain.  Strong self-absorption supplies isomorphisms back to `A` which
   converge on the first-factor embedding.  Nuclear dimension at most `d`
   is closed under point-norm limits of maps: for each finite set and
   tolerance, first choose a sufficiently close map and then its
   `d`-decomposable approximation.  These facts prove the exact equality
   with `dim_nuc(iota_A)`.

5. Fibrewise restrictions of `iota_A` have dimension at most one, but no
   theorem cited here turns that into global map dimension one.  Applying
   the ordinary USC gluing theorem merely recreates the independent base
   colour and the bound three.

## Constant-field checkpoint

6. `C([0,1]) tensor Z` is nuclear and globally Z-stable, and every fibre is
   the simple non-AF algebra `Z`.  It is therefore already an instance of
   the proposed fibrewise implication with no twisting or discontinuity.

7. Tikuisis--Winter prove decomposition rank at most two for
   `C(Y) tensor Z` for arbitrary compact Hausdorff `Y`.  Since nuclear
   dimension is bounded by decomposition rank, this improves the generic
   three-bound for the trivial interval field, but the cited theorem does
   not give one.

## Exact boundary

The package does not assert that the dimension of the constant interval
field equals two, nor that it is a counterexample.  It records the strongest
cited bound and the exact map whose one-dimensional estimate is missing.
Thus it is a firewall against the invalid inference

```text
fibrewise Z-stable => globally Z-stable => nuclear dimension at most one,
```

whose final implication is established for simple algebras and for
O-infinity-stable algebras, but not for arbitrary nonsimple Z-stable
algebras.

Outcome: **PASS**.
