---
rg: 2
id: cuspidal-redistribution-refutes-regular-core-orbit-basin
kind: claim
title: Cuspidal multiplicity redistribution refutes capture by the regular endpoint orbit
distinct_from:
  congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits: that classifies endpoints having the same regular finite-quotient character; this changes the global character while preserving the core restriction exactly, and the changed characters are nevertheless asymptotically regular.
  p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment: that is a fixed exceptional field and disappears after minimizing over the whole regular-character endpoint orbit; this gives a positive-density obstruction along unbounded prime levels even after that minimization.
  selberg-orbit-retraction-does-not-cross-square-free-basin: that is a logical firewall against using Selberg before congruence authentication; this constructs exact congruence endpoints and uses the Selberg gap to prove that they stay uniformly outside the regular endpoint orbit.
  bs14-two-cubic-strict-repair-constants-diverge: that uses compressed endpoints with small nonzero residual; this has zero residual, an exactly regular authenticated BS core, and an asymptotically canonical global character.
---

Let

```text
A=PSL_2(Z[1/2]),             Q_p=PSL_2(F_p),
B=<r,t | rtr^(-1)=t^4> <= A,
```

and take primes `p=1 mod 4` for which the standard reduction maps `A` onto
`Q_p`.  There are same-dimensional exact representations

```text
rho_p,eta_p:A -> U(|Q_p|)                                  (CRB1)
```

with all of the following properties.

1. `rho_p` is the left regular representation of `Q_p`.
2. After one exact unitary alignment,

   ```text
   eta_p|B=rho_p|B.                                        (CRB2)
   ```

3. The normalized characters of **both** sequences converge pointwise to
   the regular character of `A`.
4. If `x` is the square-free extending involution and

   ```text
   O_p={U rho_p(x) U^*: U in rho_p(B)'},                   (CRB3)
   ```

   then one constant `c>0`, independent of `p`, satisfies

   ```text
   dist_2(eta_p(x),O_p)>=c.                                (CRB4)
   ```

In particular, over the exactly authenticated regular congruence core
`rho_p|B`, the raw involution `eta_p(x)` has **zero** error in the
involution, inversion, both cubic rows and every core row, but it does not
approach the regular-character core-commutant endpoint orbit.  This remains
true even though the whole tuple has asymptotically canonical trace.

The construction redistributes the regular multiplicities among the
`m_p=(p-1)/4` cuspidal irreducibles of degree `p-1`.  These irreducibles all
have the same restriction to the standard Borel, hence to the image of
`B`.  Keep every noncuspidal regular multiplicity, put all
`m_p(p-1)` cuspidal copies on one cuspidal irreducible, and put zero copies
on the other `m_p-1`.  Restriction to `B` is unchanged exactly.  The
redistributed sector has asymptotic dimension one half of `|Q_p|`, while
only one of its `m_p` regular summands remains common with `rho_p`.

Property `(tau)` turns this representation-type mismatch into `(CRB4)`.
For a core intertwiner `U`, view `U` in
`Hom(H_(rho_p),H_(eta_p))`.  Its displacement under the fixed generators
of `B` is zero and its displacement under `x` is precisely the distance in
`(CRB3)`.  The uniform congruence spectral gap bounds that displacement
below by `kappa` times the distance to the space of genuine `A`-intertwiners.
The latter distance is at least

```text
sqrt(((m_p-1)(p-1)^2)/|Q_p|) -> 1/sqrt(2).              (CRB5)
```

This refutes only capture by the preselected **regular-`Q_p` endpoint
orbit**.  It does not refute flexible repair: `eta_p` is already an exact
endpoint and may repair itself at zero cost.  The corrected target must
select the input's endpoint representation type adaptively, or reconcile
the full moving congruence restriction semigroup.  Core authentication
alone cannot select the regular global multiplicities.

