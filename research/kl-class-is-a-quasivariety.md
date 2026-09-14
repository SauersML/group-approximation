---
rg: 2
id: kl-class-is-a-quasivariety
kind: claim
title: The groups satisfying nonsingular Kervaire--Laudenbach form a quasivariety closed under products and local embeddings
distinct_from:
  kervaire-laudenbach-nonsingular-conjecture: that asserts the class described here is every group; this describes the class's closure properties, which hold whether or not the conjecture is true.
  kl-failure-localizes-to-the-coefficient-subgroup: that transfers injectivity upward from the coefficient subgroup to the whole group by an amalgam normal form; this proves subgroup, product, ultraproduct, residual and local-embedding closure from the finiteness of a collapse certificate.
  nonsingular-adjunction-preserves-approximation-radicals: that bounds the coefficient kernel by the MF and hyperlinear radicals by extending homomorphisms into unitary product quotients; this bounds it by the radical of the Kervaire--Laudenbach class itself, using only the certificate.
  kl-counterexample-absorbs-any-countable-group: that enlarges a counterexample so it contains any countable group, the overgroup direction of failure; this is the closure of the positive class, the downward and product direction.
---

For a nonempty set `D` of nonzero integers, let `KL_D` be the class of groups
`G` such that `G -> G_w = (G * <t>)/<<w>>` is injective for every
`w in G * <t>` with `deg_t(w) in D`.  Write `KL` for `D = Z \ {0}`.

1. **Quasi-identities.**  `KL_D` is exactly the class of groups satisfying a
   recursively enumerable set of quasi-identities

       sigma_c :  forall x  ( r_1(x) = 1  and ... and  r_k(x) = 1 )  ->  alpha(x) = 1 ,

   one for each *template* `c = (P, w, alpha)`: a finite presentation
   `P = <x | r_1, ..., r_k>`, a word `w in P * <t>` with `deg_t(w) in D`, and
   a word `alpha` in `x` whose image lies in `<<w>>_(P * <t>)`.
2. **Closure.**  `KL_D` contains the trivial group and is closed under
   subgroups, arbitrary direct products, ultraproducts and directed unions.
   In particular:
   - `G in KL_D` if and only if every finitely generated subgroup of `G` is;
   - every residually-`KL_D` group lies in `KL_D`, and so does every
     subdirect product of members;
   - every group that is locally embeddable into members of `KL_D` lies in
     `KL_D`.
3. **Radical bound.**  For every group `G` and every `w` with
   `deg_t(w) in D`,

       ker(G -> G_w)  <=  Rad_D(G) = intersection of ker(phi) over all
                          homomorphisms phi : G -> Q with Q in KL_D .

4. **The conjecture.**  `KL_D` is every group if and only if, for every
   template, `alpha = 1` in `P`.  This is the finitely presented reduction
   `kl-counterexample-can-be-finitely-presented` read as a statement about
   quasi-identities.

The hyperlinear and MF classes lie in `KL`
(`kervaire-laudenbach-holds-for-hyperlinear`, `kervaire-laudenbach-holds-for-mf`).
By item 2, `KL` also contains every group that is residually, or locally
embeddable into, members of the union of those two classes, and every
subdirect product of hyperlinear and MF groups.  Item 3 refines the existing
bound `ker(q) <= Rad_MF(G) intersect Rad_hyp(G)`: any further class proved to
satisfy the conjecture shrinks the kernel bound at no extra cost.

## What it rules out about counterexamples

A counterexample is not residually `KL`, is not locally embeddable into `KL`,
and is not a subgroup of any product or ultraproduct of `KL` groups.  Every
overgroup of a counterexample is a counterexample.  The obstruction that a
counterexample must defeat is therefore global: no family of homomorphisms or
partial homomorphisms into good groups may separate its points.

## What it does not give

The class of `KL` groups is not claimed closed under quotients or
extensions.  Central extensions are exactly where `central-extension-kl-schur-criterion`
puts the difficulty, and main has no quotient permanence.

Proved in `kl-class-quasivariety-proof`.  No novelty is claimed: the closure
properties are the standard ones for a class defined by quasi-identities, and
the only input is that a collapse certificate is finite.
