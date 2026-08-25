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
- **The remaining gauge and the weakest sufficient identity are explicit.**
  `agent-free-compressor-chart-edge-has-multiplicity-gauge` shows that even
  conjugacy of the complete simple chart leaves an arbitrary `U(m)` on its
  multiplicity space, which can rotate the intended next prefix to zero
  overlap at zero relator defect. The same edge must additionally conjugate
  one non-scalar prefix involution. Its spectral projections then satisfy the
  required incidence with exactly one half of the conjugacy-word HS defect.
  The construction problem is now to impose that mixed conjugacy without
  constraining the inactive sectors or recreating the Schur `M_2` cancellation.
- **The one-source mixed edge is now exact.**
  `full-index-two-hnn-edge-creates-own-prefix-split` extends an index-two
  Reynolds edge over the full source pair and sends its source sign to the
  literal next pulse sign.  The retained Reynolds range is then exactly the
  positive-prefix fixed space and its unused companion is exactly the
  negative first-hit space, with a dimension-free HS estimate.  What remains
  in this node is the simultaneous source ledger: realize the complete
  retained Schur family by such full-pair sources sharing one target sign,
  while returning allowed/inactive sectors without losing a baseline copy.
- **Routing the whole baseline through those cells is impossible.**
  `full-pair-routing-of-complete-baseline-has-a-prefix-capacity-gap` proves
  that if the `T` retained baseline types are all full-pair sources sharing
  `B`, then every successor carrier under the positive `B` prefix loses at
  least `1/T` of the current baseline trace.  This contradicts the lossless
  return required in the perfect model, where the forbidden surplus is zero.
  Thus the remaining construction must be hybrid: return the complete
  allowed/inactive baseline without an index-two companion, and apply the
  full-pair split only to the forbidden surplus.
- **Exact companion-free chart return also has an exponential firewall.**
  `companion-free-prefix-return-has-exponential-regular-capacity` applies in
  the canonical group trace to the complete sum of returned baseline types.
  Typewise full-chart HNN transport, auxiliary central-sign changes, paired
  source halves with orthogonal target tags, and shared-variable amalgams all
  preserve that total trace.  If their returned sum lies under the `n`-bit
  positive pulse prefix, its trace is at most `2^(-n)`.  Therefore no such
  functorial hybrid can satisfy the finite first-hit threshold
  `N eta q_0>1`.  The companion-free seam must itself contain a genuinely
  matrix-only multiplicity selection (false in the regular factor), not just
  an exact finite-chart incidence.
- **Finite-depth concatenation of all established local cells is still
  regular-absorbed.**
  `balanced-schur-finite-depth-reuse-is-regular-absorbed` includes the
  payload square and Reynolds proper-corner dressing in finite semidirect
  vertex packets, then applies common negative regular multiples to every
  child-reuse and first-hit HNN edge.  For every fixed depth this gives an
  exact finite-dimensional model with payload sign `-I` and every
  forbidden/child/address type present.  Enlarging an associated subgroup so
  the same edge also carries the next prefix does not help.  The missing seam
  must constrain two edge intertwiners on their external multiplicity spaces;
  another independent finite-chart covariance row cannot establish the four
  simultaneous incidences.
