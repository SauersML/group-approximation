---
rg: 2
id: balanced-schur-active-child-is-next-prefix-source
kind: claim
title: Identify the phase-retained Schur child with the next pulse-prefix source
distinct_from:
  finite-depth-prefix-preserving-hard-sign-hnn: That makes already selected exits first-hit orthogonal; this must return the complementary child as the next active source.
  proper-corner-charged-section: That selects one local retained return and one paid companion; this must concatenate the retained returns through the finite Toeplitz/Fanizza depth.
---

**OPEN ACTIVE INCIDENCE.**  For the fixed depth `N`, attach the balanced
payload-rooted Reynolds section to each binary Schur child cell so that:

1. the phase-retained child at level `n` is, up to `C sqrt(E)` drift, the
   source carrier at level `n+1` cut by the positive pulse prefix `C_(n+1)`;
2. the complementary relative-Pauli child is the projection `P_n` used in
   `finite-depth-prefix-preserving-hard-sign-hnn`;
3. inactive/allowed packet sectors return to the active carrier and do not
   enter a first-hit exit; and
4. the perfect infinite BCS representation extends with every forbidden
   source zero and the marked payload sign nontrivial.

The two-sign balance, raw square-root word, one-exit Pauli split, hard-sign
capture, and prefix orthogonality are established separately.  The only
new assertion is that the same finite subgroup charts realize all four
incidences simultaneously, rather than leaving an independent multiplicity
unitary between the retained child and the next source.

## Attempts

- Conjugating the complete child packet to the next full packet is impossible
  because their restriction multiplicity vectors differ by the Schur factor
  two.  The edge must identify only the retained child chart.
- Identifying only the central child sign leaves the external multiplicity
  unitary arbitrary.  The balanced raw-lift section must be reused as the
  actual chart edge, not attached as a tensor-independent local cell.

