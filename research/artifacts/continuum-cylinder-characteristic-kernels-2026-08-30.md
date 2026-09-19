# Characteristic-kernel proof of continuum multiplicity in the literal cylinder

## Input audited

The established claim `literal-witness-kernel-free` computes the kernel of the
canonical Clifford-witness epimorphism

```text
pi : E ->> W
```

as a free group `K` of countably infinite rank.  Its proof also records that
the common block centre injects into `W`: the literal word `w` maps to the
nontrivial Clifford sign.  Consequently

```text
K=ker(pi),           K normal E,           w notin K.             (1)
```

The external input is exactly the main cardinality conclusion of R. M.
Bryant, *Characteristic subgroups of free groups*, in M. F. Newman (ed.),
*Proceedings of the Second International Conference on the Theory of Groups*,
Lecture Notes in Mathematics 372, Springer (1974), 141--149,
[doi:10.1007/BFb0065165](https://doi.org/10.1007/BFb0065165): a free group of
countably infinite rank has continuum many characteristic subgroups (indeed,
continuum many which are not fully invariant).  The publisher's table of
contents confirms the author, title, volume and pages; the source abstract
states the countable-rank and continuum conclusions explicitly.

## Normality and survival of the mark

Let `C` be characteristic in `K`.  For `e in E`, normality of `K` says that
conjugation by `e` restricts to an automorphism of `K`.  Since `C` is fixed by
every automorphism of `K`, it is fixed by this conjugation.  Hence

```text
C char K and K normal E  ==>  C normal E.                         (2)
```

Also `C<=K`, so (1) gives `w notin C`.  Therefore `E/C`, with the images of
the eight literal generators as marking, is a marked quotient of `E` in which
the distinguished word survives.  By `clopen-non-mf-cylinder`, every such
marked quotient belongs to the literal clopen cylinder and is non-MF.

Applying this to Bryant's continuum family gives continuum many distinct
normal subgroups `(C_i)` of `E`, all contained in `K`, and hence continuum many
distinct marked quotients in the cylinder.  No claim about finite presentation
of these quotients is needed: they are quotients of the eight-generated group
`E`, so they are finitely generated and countable, exactly as the target asks.

## Removing the marking

Distinct marked quotients can have isomorphic underlying groups, so one final
countable-fibre argument is necessary.

Fix a countable abstract group `Q`.  If `E/C_i` is isomorphic to `Q`, compose
the quotient map with one such isomorphism.  This produces an epimorphism
`f_i:E->>Q` having kernel exactly `C_i`.  Since `E` has eight fixed generators,
every homomorphism `E->Q` is determined by a point of `Q^8`.  The latter is
countable.  Thus

```text
#{ C_i : E/C_i isomorphic to Q } <= aleph_0.                       (3)
```

The map from Bryant's continuum family to abstract isomorphism types therefore
has countable fibres.  If its image had cardinal `kappa<2^aleph_0`, then its
domain would have cardinal at most

```text
kappa * aleph_0 = max(kappa,aleph_0) < 2^aleph_0,
```

a contradiction.  Its image has cardinal continuum.  A transversal supplies
continuum many pairwise non-isomorphic finitely generated non-MF groups, all
inside the one literal cylinder.

## Firewall checks

- The argument varies quotients `E/C_i`; it does not use the external products
  `E x N_i` from `continuum-nonisomorphic-fg-non-mf`.
- The word `w` survives for the uniform reason `C_i<=ker(pi)` and
  `pi(w)!=1`; survival is not inferred from the mere fact that `C_i` is proper.
- Characteristicity is used only inside the already-normal subgroup `K`, so
  the elementary characteristic-in-normal implication supplies the required
  normality in `E`.
- Countability of each quotient is used in (3).  It follows from finite
  generation and is independent of any finite-presentation claim.
