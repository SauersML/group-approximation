---
rg: 2
id: lamp-cartan-inclusion-is-not-rigid
kind: claim
title: The lamp Cartan inclusion of the summit wreath is not a rigid inclusion - relative property (T) fails via Bernoulli deformations
artifacts:
  - research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md
distinct_from:
  coset-wreath-algebra-has-a-lamp-cartan: that establishes the lamp algebra IS a Cartan masa of L(W_3); this records the opposite-polarity fence - the inclusion carries no relative property (T) - so Popa rigid-inclusion machinery cannot be applied to it.
---

Let `W_3 = A rtimes Gamma` be the summit coset wreath
(`A = direct_sum_{Gamma/Lambda} C_2`, `Gamma = SL_3(Z[1/3])`).  Claim
(THEOREM): the pair `(W_3, A)` does NOT have relative property (T);
equivalently (Popa's correspondence for crossed products by abelian
groups) the Cartan inclusion `L(A) subset L(W_3)` is not a rigid
inclusion.

*Proof.*  The dual of `A` is the compact Cantor group
`X = prod_{Gamma/Lambda} {+-1}` with `Gamma` permuting coordinates.
For `q in (0, 1/2]` let `nu_q` be the i.i.d. product measure giving
each coordinate the value `-1` with probability `q`.  Each `nu_q` is
`Gamma`-invariant (the action permutes coordinates), has no atom at the
trivial character (it is atomless), and `nu_q -> delta_1` weakly as
`q -> 0` (every cylinder neighbourhood of the trivial character gets
mass `(1-q)^{|window|} -> 1`).  The associated GNS representation of
`W_3` on `L^2(X, nu_q)` (lamps act by multiplication by characters,
`Gamma` by translation) has almost-invariant vectors as `q -> 0` (the
constant vector: `<pi(a)1, 1> = integral hat(a) d nu_q -> 1` for each
lamp `a`, and it is exactly `Gamma`-invariant) but no nonzero
`A`-invariant vector (an `A`-invariant vector is an `L^2`-function
supported on the `nu_q`-atoms of `X`, and `nu_q` is atomless).  A
sequence of such representations refutes relative property (T).  QED.

**Why record it.**  With `coset-wreath-algebra-has-a-lamp-cartan` on
the books, the natural next reflex is Popa deformation/rigidity against
the rigid-inclusion axis (as for `(Z^2 rtimes SL_2(Z), Z^2)`).  This
fence shows that axis is empty here: the rigidity of the situation
lives entirely ABOVE the lamps (property (T) of `Gamma`, Brown
discreteness of the base microstate classes), never on the lamp
inclusion itself, whose dual admits the full i.i.d. deformation family.
Note the contrast that makes the wreath enemy hard is visible in this
one computation: the dual deformations `nu_q` exist for EVERY base
group (they are the wall/Haagerup-flavored directions), while the
Kun-Thom-style counting rigidity needs compression the arithmetic pair
lacks (`arithmetic-integral-subgroup-is-incompressible`).  The
`Gamma`-invariant measures on `X` are moreover genuinely rich — the
coset action is not 2-transitive (building distance is invariant), so
de Finetti does not collapse them to i.i.d. mixtures; Markov-field
measures over the building geometry give further deformation
directions.
