# Mehta--Slofstra--Zhao positivity paper: Cairn ingestion

Date: 2026-08-20

Source: Arthur Mehta, William Slofstra, and Yuming Zhao, *Positivity is
undecidable in tensor products of free algebras*, arXiv:2312.05617v2.  The
source supplied by the user was checked against the arXiv v2 structure and
theorem numbering.

## Imported interfaces

### 1. The original polynomial doubling compiler

Theorem 4.1 constructs, from any RE language, a fixed finite involutive
alphabet, computable finite relation sets `R_m`, hermitian-square contractions
`P_tilde_n`, and involutions `X_tilde_n` such that before the halting time

```text
P_tilde_n+X_tilde_n P_tilde_n X_tilde_n=P_tilde_(n+1).
```

The relation has an `R_m`-decomposition of size `C((n+1)m)^k`.  Proposition
5.3 turns this into a nonmembership collapse with contraction factor
`1/sqrt(2)`.  This is the original source underneath the later Fanizza et al.
finite-BCS packaging already used throughout Cairn.

### 2. A concrete polynomial-filling Clifford machine

The group stage is more useful than a generic appeal to Higman embedding.  It
builds central products of `D_4` cells, replacing one cell by `C_2^3` at the
terminal residue, and uses HNN letters `S,T,W` to address the cell and input.
The resulting six-generated group has deterministic polynomial-time word
problem (Proposition 4.7).  Proposition 4.8 embeds it in a finitely presented
involution-generated host with polynomially bounded fillings.

This gives Cairn an explicit computation-indexed Pauli commutator tape with a
quantitative filling ledger.  It does not give constant-soundness semantic
transport: the later gate that converts the terminal commutator into
projection doubling is an additive star-polynomial relation.

### 3. Synchrony is enough for the weighted ledger

Lemmas 3.6--3.9 prove that generator synchrony moves a word to the opposite
tensor factor at first-Sobolev cost and transfers relator decompositions to
the left marginal.  Proposition 6.3 then obtains the same `1/sqrt(2)`
contraction for a synchronous state whose marginal need not be tracial.

This is important for Cairn's quantum/contextual routes: the exponential
signal destruction survives without a classical rounding step.  It removes
an analytic state-transfer concern but not the groupification concern.

## Exact boundary for the nonhyperlinear-group program

The paper proves coRE-hardness of tracial positivity and of positivity in
tensor products of free algebras.  Those theorems do not imply a
nonhyperlinear group.  In particular:

1. the crucial recurrence is an equality of sums of projections, not a group
   word equality;
2. its defining gate multiplies that additive defect by a polynomial in a
   commutator phase;
3. the positive signal is a tracial projection mass, not a separated
   nonidentity word; and
4. the exact tracial representation on the membership side is deliberately
   compatible with the additive algebra.

Therefore the paper strongly validates Cairn's exponential-versus-polynomial
ladder and supplies its best explicit machine skeleton, while leaving exactly
the already isolated matrix-only groupification/trace-promotion boundary.

## Graph wiring

- `msz-polynomial-doubling-star-algebra-compiler`
- `msz-clifford-machine-skeleton-has-polynomial-fillings`
- `synchrony-replaces-tracial-cyclicity-at-sobolev-cost`
- `msz-polynomial-doubling-survives-synchronous-states`
- `fanizza-bcs-polynomial-doubling-tape-citation` now records the MSZ compiler
  as the imported predecessor used by the later BCS construction.
