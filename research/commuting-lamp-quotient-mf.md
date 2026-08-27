---
rg: 2
id: commuting-lamp-quotient-mf
kind: claim
title: MF property of the commuting-lamp witness quotient
refuted_by: commuting-lamp-quotient-not-mf
distinct_from:
  literal-mark-quotient-mf: This concerns the Clifford witness modulo its sign, whose lamp kernel is elementary abelian; the other concerns the literal presented group modulo its mark, whose lamp kernel is a free product of copies of `(Z/2)^8`.
  corona-hs-radical-is-finite-residual: That established claim says every corona representation of this group is trace-blind on the finite residual; this open claim asks for one that is nevertheless injective in operator norm.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

For the Clifford witness `W` and its central sign `zeta`, the quotient
`W/<zeta>` is MF in the norm-matrix-corona sense.

## Ideas

**What the group is.**  `commuting-lamp-quotient-structure`:
`W/<zeta> = F_2[X] semidirect V` is the permutational wreath product
`F_2 wr_{V/Gbar} V`, with site set `X = Z x (Z[1/2]/Z)^3`, the shift `tau`
translating the level coordinate, and the affine group acting `2^n` times
finer at level `n`.  The surviving defect is the two-lamp configuration
`ubar = e_{(1,0)} + e_{(1,e_1/2)}`, a single element of the lamp kernel.

**Routes that are closed.**

- *Residual finiteness and LEF.*  Dead, `marked-quotients-not-lef`: a local
  embedding into a finite group uncompresses the represented base and kills
  `ubar`.  This is the `Nat.card` instance of `invariant-size-collapse`, and
  it also closes local finiteness and every consequence of
  `isWeakMF_of_isLEF`.
- *Partial finite separation.*  Dead in the strongest form,
  `commuting-lamp-quotient-finite-residual`: the finite residual is exactly
  the level-even lamp subgroup `L_0`, so finite quotients see nothing of it.
  What they do see is everything else — `(W/<zeta>)/L_0` is residually finite
  — so the entire problem is the module `L_0`, and `Rad_MF(W/<zeta>)` is a
  `V`-submodule of it.
- *Amenability plus Tikuisis--White--Winter.*  Unavailable: `Gbar` has (T).
  This is exactly what separates the present claim from
  `cyclic-base-sharpness`, where the corresponding quotient is neither
  residually finite nor LEF and is MF anyway, by amenability.
- *Permanence for `Z`-extensions.*  Dead,
  `mf-not-closed-under-integer-extensions`: `W/<zeta>` and `W` are both
  `Z`-extensions of LEF groups (`lamp-telescope-base-is-lef`), and `W` is not
  MF.  So the operator-norm analogue of Elek--Szabo is false and no
  permanence theorem that cannot see the central sign can prove this claim.

**What a proof must produce.**  By `corona-hs-radical-is-finite-residual`,
every corona representation of `W/<zeta>` is Hilbert--Schmidt blind on all of
`L_0`.  So a faithful model must send each element of `L_0` to a symmetry
`1 - 2p` with `p` a nonzero projection of vanishing normalized rank, and must
represent the compression relations to operator-norm `o(1)` while *not*
normalizing the represented base.  Equivalently, `corona-commutant-no-growth`
must fail.

**Direction of belief.**  Undecided, and the note records no evidence strong
enough to guess.  The one structural hint on the positive side: the central
sign is exactly the obstruction to closing the expanding level tower, and it
is trivial here; the one hint on the negative side is that all three
categories where the question can currently be asked give collapse.

**The hinge is exact.**  `marked-quotient-mf-forces-commutant-growth`: an
injective corona representation of this group puts the lamp
`Theta(c_{tau o})` in `Theta(abar(Gbar))' cap Q` but not in
`Theta(Gbar)' cap Q`, so MF here *requires* operator-norm commutant growth at
the compressor, and `corona-commutant-no-growth` refutes it.  The two
directions together make that claim an exact hinge.  It also covers the
Kun--Thom commuting-lamp wreath (`kun-thom-wreath-weak-mf`), which is this
same question for a different Kazhdan pair.

**Best next unit.**  `corona-commutant-no-growth` — decide whether the
operator-norm relative commutant of a corona-represented Kazhdan group can
grow under a compression implemented inside the represented group.  A proof
refutes this claim, `literal-mark-quotient-mf` and `kun-thom-wreath-weak-mf`
at once; a counterexample is very close to proving this one.

**RESOLVED NEGATIVELY (2026-08-15).**  The negation is established:
`commuting-lamp-quotient-not-mf` — the tau-moved root lamp is an
involutive compression witness, so the involutive collapse applies
verbatim and `[v_1, c_{tau o}]` is a nontrivial radical element.  The
fork was a false dichotomy: `corona-commutant-no-growth` is refuted in
general (`corona-commutant-growth-witness`) AND this group is non-MF
anyway.  The "very close" sentence above did not survive: the general
counterexample needs residual finiteness, which this group lacks.  This
claim can never be established; retained as the record of the question.
