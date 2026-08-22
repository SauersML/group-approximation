---
rg: 2
id: culf-mastel-positive-density-power-return
kind: claim
title: Return the Culf--Mastel acceptance contraction through all powers on one canonical positive-density carrier
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
2. for every fixed `N`, canonical-profile matrix microstates satisfy, after
   packet exactification,

   ```text
   q_m u_m^n q_m=T_m^n+o(1),       0<=n<=N;             (CPR1)
   ```

3. on a NONHALT instance the Culf--Mastel gap gives
   `||T_m||<=rho_m<1+o(1)` on `q_m`;
4. on a HALT instance one exact, possibly properly infinite,
   representation extends with `q_m!=0` and with the perfect acceptance
   carrier fixed.

The equalities in `(CPR1)` may have constants depending arbitrarily on `m`
and `N`.  They must all refer to the same `q_m`; separate depth heads with
trace `O(1/N)` are insufficient.

The operator equalities in `(CPR1)` are sufficient but stronger than the
capacity argument needs.  By
`positive-density-hs-power-overlaps-force-finite-depth`, it is enough to
construct the same `q_m,u_m` with

```text
||q_m u_m^(kL_m) q_m||_2^2
 <=(alpha_m+o(1))rho_m^(2kL_m)+o(1),    1<=k<=N_m,     (CPR1-HS)
```

and to choose the fixed integers with

```text
(N_m+1)alpha_m
 >1+2rho_m^(2L_m)/(1-rho_m^(2L_m)).                   (CPR2-HS)
```

This scalar-overlap formulation is invariant under arbitrary common
multiplicity gauges.  It does not by itself solve the remaining selected
corner return, but it removes coherent operator identification from the
minimal interface.

By `positive-density-power-dilation-forces-finite-depth`, clauses 1--3 rule
out canonical microstates on every NONHALT instance: fix
`N>alpha_m^(-1)-1`, then take the microstate limit.  Clause 4 supplies the
algebraic survival input for reverse Kleene.  Hence this claim, together with
the Culf--Mastel source and `canonical-profile-kleene-higman`, yields a
finitely presented nonhyperlinear group.

## Attempts

- **Fresh dilation register at every depth.**  This realizes `(CPR1)` but
  `fixed-depth-strict-contractions-have-dilution-escape` makes the head trace
  `O(1/N)`, exactly cancelling the orbit-capacity contradiction.
- **One Julia/Halmos block.**  It gives only `q u q=T`; later compressed
  powers contain returns through the complementary block and are not `T^n`.
- **Unilateral shift register.**  It gives coherent powers in the exact
  infinite model, but finite cyclic truncations dilute the head as in
  `geometric-infinite-counter-is-hs-trace-diluting`.
- **Live target.**  Couple the finite packet carrying `q_m` to a self-similar
  dilation tail so that canonical Plancherel mass replicates the head rather
  than normalizing it over the depth.  The coupling must be matrix-only:
  exact orthogonality of infinitely many conjugates of a nonzero
  group-algebra projection is impossible in the canonical finite trace.
