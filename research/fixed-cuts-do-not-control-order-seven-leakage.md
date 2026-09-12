---
rg: 2
id: fixed-cuts-do-not-control-order-seven-leakage
kind: claim
title: Existing fixed finite-coordinate cuts do not control the order-seven Whitehead leakage tail
invalidates:
  - fixed-finite-coordinate-cuts-force-order-seven-leakage-tail
artifacts:
  - research/fixed-cut-order-seven-leakage-audit-proof.md
distinct_from:
  order-seven-anchor-stops-at-whitehead-compression-leakage: that isolates the positive leakage operator and proves the compression telescope; this audits every presently available fixed finite-coordinate selector against that operator.
  fixed-type-and-raw-rank-selectors-do-not-evade-hecke-firewall: that treats finite packet isotypic carriers and raw ambient ranks; this also treats the middle-index packet, the nine-pair regularizer, finite-actor minimal atoms, and spectral coarea.
  finite-coordinate-el20-active-cut-inherits-order-seven-anchor: that is the still-open arbitrary-profile estimate; this only excludes the fixed selector mechanisms currently present in Cairn and leaves a growing coefficient-sensitive cut open.
---

**ESTABLISHED FIXED-MECHANISM AUDIT.**  Use the notation of `(OCI5)` and put

```text
L_n=sum_(i=1)^2
 Q_n v_(i,n)^*J_(i,n)(1-Q_n)J_(i,n)v_(i,n)Q_n.        (FLC1)
```

None of the fixed finite-coordinate mechanisms already established in
Cairn forces

```text
tr_n(Q_n 1_((C delta_n^(2alpha)),infinity)(L_n))
 <=C delta_n^alpha.                                   (FLC2)
```

The obstructions are mechanism-specific.

1. The order-seven relation only turns a cut with small `(FLC1)` boundary
   into reservoir-gauge coercivity.  It gives no estimate on the spectral
   mass of `(FLC1)`.  Fixed packet-type and raw-rank cuts are already blocked
   by the regular and amplification firewalls.
2. The three-pair middle-index Heisenberg packet is normalized by the two
   prefix Whiteheads, but the actual center-chain/Hecke arms eject its dual
   roots into new root positions.  Its atoms therefore do not reduce the
   operators in `(FLC1)`.
3. The nine-pair packet has arbitrary-profile uniform atoms, but every
   operator in `(FLC1)` acts as `1 tensor T` on its active decomposition.
   Passing to one of its atoms preserves the complete spectral distribution
   of the reservoir leakage.
4. A minimal atom of a fixed finite actor packet is Morita-neutral in the
   exact finite dual-permutation model.  Following a genuine opposite-root
   or Leavitt-parabolic actor leaves every fixed invariant window and
   restores, rather than controls, the moving boundary.
5. Single-spike spectral coarea constructs a reducing cut after the relevant
   high spectral mass or first moment is supplied.  Applied here, retaining a
   positive near-full low cut is precisely the missing estimate `(FLC2)`;
   coarea controls the boundary of the chosen tail, not the size of that
   tail.  It is therefore not an independent proof of `(FLC2)`.

There is a quantitative regular firewall behind item 1.  In the exact
regular model let `L` be the fixed leakage operator and
`lambda=tau(L)>0`.  Since `0<=L<=2Q`, for every `t>=0`,

```text
tau(Q 1_((t,infinity))(L))
 >=(lambda-t tau(Q))/2.                               (FLC3)
```

Thus a fixed regular-safe selector cannot make the tail vanish with zero
word defect.  A genuinely finite-coordinate argument can escape `(FLC3)`
only by using structure that does not extend to that regular model; the
fixed type, packet, actor, and coarea operations above provide no such
structure.

This is deliberately not a refutation of `(OCI5)`.  The exact survivor is a
cut whose complexity grows with the matrix coordinate or an authenticated
coefficient-sensitive mixed/opposite-root occurrence that proves a
normalized tail bound.  No such mechanism is presently established.

DERIVATION
fixed-cut-order-seven-leakage-audit-proof
