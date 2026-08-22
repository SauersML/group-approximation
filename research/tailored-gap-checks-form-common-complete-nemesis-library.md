---
rg: 2
id: tailored-gap-checks-form-common-complete-nemesis-library
kind: claim
title: The checks of one perfect-gap tailored game are a finite common-complete strategy nemesis library
distinct_from:
  perfect-zpc-irs-quantum-gap-game: that supplies the separated game; this interprets its individual verifier checks as approximation-specific nemeses and proves joint completeness.
  bespoke-extension-nemesis-library-defeats-diagonal-schedules: that compactifies ordinary group-extension profiles; this works first in the richer strategy language, where the common completion and finite cover are immediate from the game gap.
  coherent-word-oracles-cannot-branch-on-their-own-tracial-profile: that rules out internal tomography followed by branching; this pre-enumerates every verifier check and needs no branch selection inside the presentation.
---

Let `G` be the finite tailored game from
`perfect-zpc-irs-quantum-gap-game`, with checks `c in C`, positive sampling
weights `beta_c`, and losing projections `L_c`.  Then:

1. one perfect ZPC-IRS strategy `S_infinity` satisfies
   `L_c=0` for every `c` simultaneously;
2. every CE strategy `S` satisfies

   ```text
   sum_c beta_c tau_S(L_c)>=1/2,                       (TCN1)
   ```

   so at least one check has `tau_S(L_c)>=1/2`;
3. for each check, the set of CE strategy types satisfying `L_c=0` is
   closed.

Thus the finite family of exact conditions `L_c=0` is already a jointly
complete approximation-specific nemesis library.  The failed check may
depend arbitrarily on the strategy, but all checks were fixed in advance and
the same infinite strategy satisfies all of them.

## Proof

Perfectness makes the weighted sum of the nonnegative numbers
`tau(L_c)` zero, hence every summand vanishes; in the faithful GNS quotient
this is `L_c=0`.  The quantum-value bound below one half gives `(TCN1)` for
every CE strategy.  Evaluation of the fixed polynomial projection `L_c` is
continuous on the compact tracial strategy-type space, proving closedness.

No recursion theorem, tomography, dimension sensor, or infinite challenge
enumeration is used.  The unresolved operation is solely translation of
these common projective checks into ordinary marked group extensions.
