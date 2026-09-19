---
rg: 2
id: cdi-character-cannot-be-promoted-by-regular-corners
kind: claim
title: Regular restriction and algebraic corners cannot promote the CDI non-CE character
distinct_from:
  cdi-property-t-envelope-has-nonabelian-base: that constructs the non-CE character and identifies the nonabelian cocycle base; this proves that the standard central-sector, subgroup-induction, algebraic-corner, and regular-wreath operations do not change its trace into a canonical one.
  unique-trace-signed-corner-quotient-forces-nonhyperlinear: that is a positive compiler assuming a unique canonical corner trace and a non-CE quotient; this shows why merely compressing the CDI lattice copy does not supply either hypothesis.
  diagonal-tensor-trace-powers-forget-full-gns-tensor: that rules out pointwise tensor polarization; this treats regular representations, finite central sectors, and finite-support group-ring corners.
---

Let `H` be a torsion-free cocompact lattice in `Sp(n,1)`, `n>=2`, and let
`chi` be the non-Connes-embeddable character supplied by the CDI envelope in
`cdi-property-t-envelope-has-nonabelian-base`.  Then `H` is ICC, residually
finite, and hyperlinear, and the following standard promotion attempts are
trace-blind.

1. **Finite central sectors.**  For every finite central extension
   `1 -> C -> H_tilde -> H -> 1`, every `beta in hat C`, and the central
   projection

   ```text
   q_beta=|C|^(-1) sum_(c in C) overline(beta(c)) c,
   ```

   the normalized canonical trace of `q_beta C[H_tilde]` is the twisted
   regular trace: `tau(q_beta h_tilde)/tau(q_beta)=0` whenever the image of
   `h_tilde` in `H` is nontrivial.  It therefore cannot equal `chi`.

2. **Subgroup restriction/regular induction.**  If `H<=Gamma`, then
   `lambda_Gamma|H` is an amplification of `lambda_H`, indexed by the left
   `H`-orbits of `Gamma`.  Hence restriction of the canonical trace, and every
   reducing multiplicity corner in this regular restriction, is still
   `delta_H`; it is not `chi`.  Replacing this regular block by
   `Ind_H^Gamma(pi_chi)` merely transports the noncanonical representation and
   does not identify it with `lambda_Gamma`.

3. **Finite-support marked corners.**  More generally, let `H<=Gamma` and let
   `0!=q in C[Gamma]` be a projection.  If every compression `qhq` is unitary
   in the corner `qL(Gamma)q`, then necessarily `hqh*=q` for every `h in H`;
   thus `q` commutes with `H`.  The natural corner representation `h |-> qh`
   has canonical corner character

   ```text
   chi_q(h)=tau_Gamma(qh)/tau_Gamma(q).
   ```

   This character equals `delta_H`.  Indeed its support inside `H` is
   contained in the finite support of `q`, while it is conjugation invariant;
   ICC makes every nonidentity conjugacy class infinite.

4. **Regular wreath/Clifford carriers.**  The ordinary finite-lamp wreath
   product over the regular `H`-set is sofic because `H` is residually finite;
   its canonical group factor is CE and cannot contain the CDI GNS factor.
   Passing to a finite central Clifford sector again supplies a twisted
   regular sector as in item 1, not `chi`.  To make such a sector non-CE one
   must build a new non-CE twisted regular algebra; the CDI character alone
   gives no map into that sector.

Thus none of the four formal operations promotes the existing character.
The honest escapes are exactly the graph's existing hard interfaces: a
unital algebraic map of a no-CE-trace algebra into a canonical group corner,
a unique-trace corner quotient, or a new group/action whose twisted regular
sector is independently proved non-CE.
