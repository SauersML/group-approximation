---
rg: 2
id: binary-schur-toeplitz-one-branch-hs-payment
kind: claim
title: Charge one retained Schur child in the binary Toeplitz head by ordinary group-relator energy
distinct_from:
  binary-schur-child-toeplitz-self-embedding: that proves the exact coefficient endomorphism and its two-child module identity; this is the remaining normalized-HS estimate.
  toeplitz-schur-child-masa-recurrence: that asks for a complete Fanizza tape placement with inactive-sector bookkeeping; this isolates the single forbidden-ideal branch payment after the allowed ideal has been collapsed to the augmentation.
  branching-plus-first-hit-exits-forces-hs-floor: that is an abstract recurrence once one-copy exit control is available; this must construct that exit control for the explicit binary Toeplitz head.
---

Let `Rsharp`, `Sigma`, `I`, and `C` be as in
`binary-schur-child-toeplitz-self-embedding`, put

```text
Gsharp=EL_5(Rsharp),
Hsharp=<Gsharp,t | tgt^-1=Sigma(g) for g in Gsharp>,
w=x_12(P).                                                  (BHP1)
```

Attach a finite, explicitly presented Schur/Fanizza return cell to one of the
two corrected-child signs in `(BST3)`.  Prove that every canonical-delta
normalized-HS microstate with total relator energy `E` has a nonnegative
carrier mass `a` satisfying

```text
c ||U(w)-1||_2^2-C sqrt(E) <= a,
a <= 2 C_exit E+C sqrt(E),                                (BHP2)
```

with constants independent of matrix dimension.  Equivalently, after fixed
finite-table exactification, the two head branches have equal mass `a/2` and
one of them is bounded by `C_exit E`.

The exact algebraic prerequisites are now present.  The stable letter makes
the parent packet and its binary-head image conjugate, while `(BST3)` turns
the old full block into two corrected-child copies.  The allowed packet ideal
has been collapsed to the augmentation in `Bsharp`, so no inactive
Wedderburn direction remains.  The only possible escape is stationary flow
through both child signs.

The return cell must break that stationary flow without identifying the old
selector center globally.  A valid implementation may use the explicit
Fanizza density difference `P_f=2D(Z_C-Z_B)`, the corrected child-sign flip,
or the one-exit Pauli carrier.  It must fail on a merely classically
unsatisfiable CSP and hence cannot be a direct finite-group amalgam.

Once `(BHP2)` holds, `||U(w)-1||_2->0` in every canonical microstate.  Since
`w!=1` in `Hsharp` and every exact finite-dimensional coefficient
representation already kills it, the usual canonical-trace argument makes
`Hsharp` nonhyperlinear.  Thus this is a strictly smaller analytic target than
decoding the whole root-kernel quotient as a linear-sofic algebra.

## Attempts

- **Use both branches only.**  Iterating `(BST8)` gives `2^n` equal-scale
  descendants, but matrices may grow exponentially and realize stationary
  regular flow.  Binary branching without a paid exit is not a contradiction.
- **Conjugate a child directly back to the parent.**  This would identify
  unequal finite-packet type vectors and is blocked by
  `hnn-conjugacy-cannot-return-schur-morita-multiplicity`.  The return must
  compare the explicit density element or relative Pauli carrier instead.
- **Finite head alone.**  `finite-edge-attachments-residual-decouple` gives
  tensor-product exact models which erase any old-commutant density measured
  independently of the tail.  The paid branch must contain a nontrivial
  `Rsharp` coefficient word.
- **Modify the algebra embedding to kill one branch.**  This is impossible.
  `binary-schur-head-embeddings-are-relative-inner-holonomies` proves that
  every unital sector map has two faithful components and differs from the
  standard diagonal map only by a relative `PGL` holonomy.  The live route is
  therefore to charge that holonomy; `binary-schur-branch-payment-via-19243-holonomy`
  installs collision 19243 in exactly this slot.
- **Replace the binary head by a ternary head and call the third branch an
  exit.**  `arity-imbalanced-schur-heads-have-a-stationary-exit` proves that a
  unital full-block map still returns every branch.  Relabelling one branch
  gives the formal `2/3` rank split, but the finite packet's regular stationary
  representation carries the remaining `1/3` at zero relator defect.  A
  relation that genuinely discards that third is the missing one-sided
  payment, not a consequence of the larger arity.
- **Use complementary transverse Pauli returns.**  This gives the exact
  aggregate identity `D_T+D_S=1`, hence a dimension-independent total HS
  floor.  But demanding both exact returns destroys the marked model, while
  a commuting branch selector can take `W=i` on the T-good sector and `W=1`
  on the S-good sector and continue at zero selected defect.  Thus the
  transverse pair does not by itself provide the oriented exit in `(BHP2)`.
  It becomes useful only if collision 19243 or another external incidence
  pins the branch selector independently of the holonomy spectrum.
- **Collision 19243 in the current projective frame does not pin it.**  The
  Schur relative frame is `[W] in PGL`, so the entire Atlas packet/collision
  interface is invariant under `W->iW`.  That same phase rotation exchanges
  the T and S branch deficits.  Hence the current 19243 route can only charge
  symmetric projective holonomy, not orient a fixed exit.  A new
  phase-sensitive odd return word must be coupled to the payload without
  promoting the flip into the full Pauli algebra, which would cancel the
  surplus.
