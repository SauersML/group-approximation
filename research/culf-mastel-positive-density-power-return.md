---
rg: 2
id: culf-mastel-positive-density-power-return
kind: claim
title: Return enough powers of the Culf--Mastel acceptance contraction on one canonical positive-density carrier
distinct_from:
  oracular-2csp-mark-relative-canonical-groupifier: that asks for an arbitrary mark-relative decoder of the full projection atlas; this is a narrower analytic compiler using only the already established cyclic acceptance contraction.
  fanizza-heat-filter-one-sided-return: that returns a polynomial heat-filter sequence tied to the native Fanizza signal; this returns powers of one fixed finite-game acceptance contraction and uses orbit-capacity rather than signal collapse.
  dimension-reported-julia-amplitude-return: that activates one dimension-selected Julia amplitude; this asks for every fixed depth on a canonical carrier and never reads the matrix dimension.
---

From the finite Culf--Mastel game `B_m`, construct computably a recursively
presented group `Gamma_m`, a nonzero rational finite-packet idempotent
`q_m in Q[Gamma_m]`, an ordinary unitary word `u_m`, and the block-encoded
cyclic acceptance contraction `T_m` on the selected packet carrier, such
that:

1. the canonical packet trace has `tau(q_m)=alpha_m>0`;
2. for computable integers `N_m,L_m`, canonical-profile matrix microstates
   satisfy, after packet exactification,

   ```text
   q_m u_m^n q_m=T_m^n+o(1),       0<=n<=N_m L_m;       (CPR1)
   ```

3. on a NONHALT instance the Culf--Mastel gap gives
   `||T_m||<=rho_m<1+o(1)` on `q_m`;
4. on a HALT instance one exact, possibly properly infinite,
   representation extends with `q_m!=0` and with the perfect acceptance
   carrier fixed.

Choose the fixed integers so that

```text
N_m>alpha_m^(-1)-1,
2 rho_m^L_m/(1-rho_m^L_m)<1.                            (CPR2)
```

The finitely many equalities in `(CPR1)` may have constants depending
arbitrarily on `m,N_m,L_m`.  They must all refer to the same `q_m`; separate
depth heads with trace `O(1/N_m)` are insufficient.

By `positive-density-power-dilation-forces-finite-depth`, clauses 1--3 rule
out canonical microstates on every NONHALT instance using the one finite
choice `(CPR2)`.  Clause 4 supplies the
algebraic survival input for reverse Kleene.  Hence this claim, together with
the Culf--Mastel source and `canonical-profile-kleene-higman`, yields a
finitely presented nonhyperlinear group.

## Attempts

- **One finite dilation register of the required depth.**  This realizes
  `(CPR1)` but `fixed-depth-strict-contractions-have-dilution-escape` makes
  the head trace `O(1/N_m)`, exactly cancelling the orbit-capacity
  contradiction unless the independent packet authentication retains
  `alpha_m>1/(N_m+1)`.
- **One Julia/Halmos block.**  It gives only `q u q=T`; later compressed
  powers contain returns through the complementary block and are not `T^n`.
- **Unilateral shift register.**  It gives coherent powers in the exact
  infinite model, but finite cyclic truncations dilute the head as in
  `geometric-infinite-counter-is-hs-trace-diluting`.
- **Live target.**  Couple the finite packet carrying `q_m` to one finite
  no-return colligation of length `N_mL_m` without dividing its Plancherel
  mass by the clock length.  No infinite tail or runtime-uniform construction
  is needed.  The coupling must still be matrix-only: a literal collection
  of too many orthogonal equal-trace conjugates would already contradict the
  canonical regular trace.
