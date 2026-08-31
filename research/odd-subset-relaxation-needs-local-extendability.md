---
rg: 2
id: odd-subset-relaxation-needs-local-extendability
kind: claim
title: The unrestricted odd-subset relaxation theorem fails without local extendability
invalidates:
  - linear-encoding-lcs-admits-odd-subset-cheats-proof
distinct_from:
  linear-encoding-lcs-admits-odd-subset-cheats: that asserts, for EVERY linear encoding of every constraint system, that consistent odd-subset assignments solve the encoded LCS; this exhibits a three-context system with a non-extendable local assignment on which a consistent odd-subset assignment violates an honestly satisfied constraint, so the assertion needs the extendability hypothesis its proof silently used.
  central-pinning-forbids-nonlinear-predicates: that is finite-group character theory about one pinned sector; this is a combinatorial counterexample to a global relaxation statement about encoded constraint systems.
---

Let `B` be a Boolean constraint system with contexts `C`, satisfying sets
`S_C`, and shared variables, encoded linearly as in
`linear-encoding-lcs-admits-odd-subset-cheats`: variables
`a_(C,phi)`, `phi : S_C -> {+1,-1}`, honest encoding `a_(C,phi) = phi(x)`
for `x in S_C`.  The claim that every constraint of an encoded LCS `L`
satisfied by all honest encodings of all consistent tuples is also
satisfied by every odd-subset assignment with consistent mod-2 marginals
is FALSE without a further hypothesis.

**Counterexample.**  Variables `u, v, w`; contexts `C_1 = {u, v}` with
`S_(C_1)` = all four assignments, `C_2 = {u, w}` with `S_(C_2) = {00, 11}`
(`u = w`), `C_3 = {v, w}` with `S_(C_3) = {00, 11}` (`v = w`).  The
consistent tuples (equivalently the solutions of `B`) are exactly `000`
and `111`.  Let `L` consist of the single constraint

```text
a_(C_1, phi_1) a_(C_2, +1) a_(C_3, +1) = J^0,
```

with `phi_1 = +1` except `phi_1(0,1) = -1`.  Every honest encoding of a
solution evaluates `phi_1` at `(0,0)` or `(1,1)`, so the constraint holds
honestly.  Take the odd subsets `T_(C_1) = {(0,0), (0,1), (1,0)}`,
`T_(C_2) = T_(C_3) = {(1,1)}`.  Their mod-2 marginals on the shared
variables agree (on `u`: `psi(0) psi(0) psi(1) = psi(1)` from `T_(C_1)`
and `psi(1)` from `T_(C_2)`; on `v` and `w` likewise), yet the odd-subset
assignment gives `a_(C_1,phi_1) = (+1)(-1)(+1) = -1` and the other two
factors `+1`, so the constraint reads `-1 = +1`: VIOLATED.

**Where the proof breaks.**  The route's several-context case asserts
that honest satisfaction for all consistent tuples "forces each `A_C` to
factor through the shared variables up to a constant".  That uses that
every `s in S_C` occurs in some consistent tuple; here `(0,1) in S_(C_1)`
occurs in none (`C_2` forces `w = 0`, `C_3` forces `w = 1`), so
`A_(C_1) = phi_1` is unconstrained at `(0,1)` and need not factor.  A
second unstated requirement is that the factorization be a PRODUCT over
the pairwise overlaps: the consistent-marginal hypothesis is pairwise, and
`T_(C_1)` above matches a point's pairwise `u`- and `v`-marginals while its
joint profile differs.

**What survives, and what it costs.**  The within-context classification
(solutions of the long-code relations `a_phi a_psi = a_(phi psi)`,
`a_(-1) = J` are exactly the odd-support characters) is correct.  A
plausible repaired theorem would assume LOCAL EXTENDABILITY -- every
`s in S_C` extends to a locally consistent tuple over the contexts of each
constraint -- together with a product-over-overlaps factorization.  The
stronger hypothesis "extends to a global solution of `B`" would make the
statement vacuous exactly for unsatisfiable `B`, which is the soundness side
the programme needs.  No repaired universal theorem is asserted here.
The route is invalid as written, and the unrestricted claim
`linear-encoding-lcs-admits-odd-subset-cheats` is refuted.
