---
rg: 2
id: integral-unit-conjecture-torsion-free
kind: claim
title: Integral group rings of torsion-free groups have only the units plus or minus g (Higman)
root: true
distinct_from:
  unit-conjecture-fails-over-complex-numbers: that refutes the field version over C, with coefficients in Z[zeta_8]; this has coefficients in Z and is open.
  rational-unit-conjecture-torsion-free: that has coefficients in the field Q and implies this; this has coefficients in Z.
  promislow-radius4-one-sided-and-integral-separation: that is a ball-limited integral lifting obstruction on one group; this is the conjecture for every torsion-free group.
  kaplansky-zero-divisor-conjecture: that asks for no zero divisors over every field; this asks for trivial units over Z.
  rational-units-rescale-to-integral-units: that transfers units between Q and Z on one group under a domain hypothesis; this is the conjecture for every torsion-free group.
---

For every torsion-free group `G`, every unit of `Z[G]` is `+-g` with
`g in G`.

*Marked `root`: Higman's unit conjecture (G. Higman, D.Phil. thesis, Oxford
1940).* It is open for the Promislow group `P`. Gardam
(arXiv:2312.05240v2, Section 2) reports "We have not succeeded in finding a
non-trivial unit in Z[P]", and Tabei (arXiv:2608.02982v1, abstract) says the
conjecture is open for `P`.

It follows from `rational-unit-conjecture-torsion-free` by
`integral-unit-conjecture-from-rational-proof`. On `P`, and on every
torsion-free elementary amenable group, the two are equivalent support by
support (`rational-units-rescale-to-integral-units`).

## Attempts

* **Balls of radius at most three.** Every unit of `Z[P]` supported in
  `B(3)` is trivial. This is Tabei's Corollary 4.1, deduced from the
  Craven--Pappas small-length theorems; it is not imported as a node here.
* **Nontrivial residues at radius four.** No unit of `Z[P]` with support in
  `B(4)` reduces mod 2 to a nontrivial unit
  (`promislow-radius4-one-sided-and-integral-separation`). The attack dies
  at Case A, units congruent mod 2 to a trivial unit. Bartholdi constructs
  approximate units modulo every `n` (Tabei, Remark 3.3), so no finite list
  of congruences closes Case A.
* **Untwisting Gardam's unit.** Every coefficient of Gardam's unit in
  `R[P]`, `R = Z[s,t]/(s^4+1, t^4+1)`, is a signed monomial `+-s^i t^j`
  (rechecked exactly in `research/artifacts/gardam-support-pair-gsp.py`).
  The monomial classes come from a homomorphism `rho: P -> R^x/{+-1}` with
  image `Z/4 + Z/4` (Gardam, Remark 2). A gauge automorphism would move the
  unit into `Z[P]` only if `rho` lifted to `P -> <s,t> = Z/8 + Z/4`. It
  cannot, because `P^ab = Z/4 + Z/4`. The attack dies at the abelianization.
* **Reduction alone.** `Z[zeta_8]` has residue rings of characteristic 2
  and 3 and embeds in `C`. So an argument whose only inputs are mod-2, mod-3
  and complex reductions proves a statement that is false for `Z[zeta_8]`
  (Tabei, Section 6.1). A proof has to use `Z^x = {+-1}`.
