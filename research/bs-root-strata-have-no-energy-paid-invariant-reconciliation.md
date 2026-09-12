---
rg: 2
id: bs-root-strata-have-no-energy-paid-invariant-reconciliation
kind: claim
title: BS root strata have no energy-paid invariant type reconciliation
distinct_from:
  long-bs14-packets-defeat-invariant-op-thresholding: that refutes operator-threshold deletion by tracking the high coordinate lines and their invariant hull; this extracts the exact obstruction to reconciling torsion strata before applying a within-stratum UGO estimate.
  exact-bs-core-strata-have-conjugation-commutant-normal-form: that gives a global chart after the root multiplicity vector is fixed; this proves that crossing to such a chart cannot first be paid by invariant padding proportional to squared core displacement.
  uniform-gauge-optimized-induced-energy: that permits direct movement between arbitrary exact comparator cores and may therefore survive this counterfamily; this refutes only the proposed invariant type-equalization reduction.
---

There is no constant `C` with the following property: any two exact
level-`N` BS cores can first be made unitarily equivalent by adjoining exact
BS summands of relative rank at most `C` times their squared normalized-HS
generator distance.

Explicitly, for every `m>=2`, let `N_m=4^m-1` and use the two `m`-dimensional
cores from `long-bs14-packets-defeat-invariant-op-thresholding`:

```text
b_m=(R_m,S_m),                 c_m=(R_m,T_m),
T_m=S_m^2.                                             (BSR1)
```

They are exact level-`N_m` cores in distinct irreducible root-multiplicity
strata and satisfy

```text
dist_core(b_m,c_m)^2=||S_m-T_m||_2^2
 <=64 pi^2/(135m).                                    (BSR2)
```

Nevertheless, if exact BS representations `pi,tau` have dimensions less
than `m`, then

```text
b_m direct_sum pi  is not unitarily equivalent to
c_m direct_sum tau.                                   (BSR3)
```

Since equivalent enlargements have equal total dimension, exact invariant
type reconciliation must add at least `m` dimensions to each `m`-dimensional
side.  Its relative padding density is therefore at least `1/2`, while the
right side of the proposed energy payment tends to zero by `(BSR2)`.

Consequently the within-stratum constant-two identity cannot be globalized
by first cutting or padding exact invariant BS packet types at a cost
proportional to core HS energy.  A surviving stratum-crossing theorem must
move/reconnect the exact comparator core non-invariantly and jointly with
the Iwahori endpoint rows.  This does not refute `(UGO1)`: `G_N` is allowed
to move directly from `b_m` to `c_m` at the actual `O(1/m)` squared
generator cost and does not require the two core types to become equivalent.

There is also a firewall against misreading this family as a direct UGO
counterexample.  On every even `m`, both isolated packets in `(BSR1)` fail
the exact determinant condition of `iwahori-cycle-packet-determinant-fence`:
`det(S_m)=exp(2 pi i/3)`, `det(T_m)=det(S_m)^2`, and
`det(R_m)=-1`, so `[det(R_m)/det(S_m)]^3` and
`[det(R_m)/det(T_m)]^3` both equal `-1`.  Hence neither core has an exact
Iwahori extension on its own space.  A genuine endpoint counterfamily must
embed such stratum motion in a larger coupled congruence restriction atom;
the isolated long clocks only refute the invariant reconciliation step.
