---
rg: 2
id: x-central-root-alignment-fails-inside-one-exact-stratum
kind: claim
title: Exact congruence endpoints in one root stratum need not admit an involution-central root alignment
distinct_from:
  fixed-root-exact-core-fiber-has-pairwise-row-coercivity: that controls the implementer after an involution-central alignment of the roots has been supplied; this proves that such a root alignment cannot be selected from small row energy, even when both row energies vanish.
  cuspidal-redistribution-refutes-regular-core-orbit-basin: that fixes the represented core and separates two global endpoint types through their extending involutions; this globally conjugates one endpoint to fix the involution instead, and obtains a uniform separation between the two represented roots modulo the involution commutant.
  exact-bs-core-strata-have-conjugation-commutant-normal-form: that aligns two equal-multiplicity roots by an unrestricted unitary; this proves that the aligning unitary cannot in general be chosen in the commutant of the common extending involution.
---

There are a constant `c>0`, primes `p->infinity` with `p=1 mod 4`,
dyadic one-power levels

```text
K_p=ord_p(4),                  N_p=4^(K_p)-1,
```

and, on dimension `d_p=|PSL_2(F_p)|`, an involution `X_p` and two exact
level-`N_p` BS cores

```text
b_(i,p)=(R_(i,p),T_(i,p)),             i=0,1,          (XCA1)
```

such that all of the following hold.

1. The two roots have exactly the same multiplicity at every `N_p`th root
   of unity.
2. Both triples `(X_p,R_(i,p),T_(i,p))` are exact square-free Iwahori
   endpoints.  In particular, their inversion and two cubic row energies
   are identically zero.
3. Nevertheless

   ```text
   inf_([z,X_p]=0) ||T_(1,p)-zT_(0,p)z^*||_2 >= c.     (XCA2)
   ```

Thus the hypothesis `(FRC5)` in
`fixed-root-exact-core-fiber-has-pairwise-row-coercivity` does not follow,
even qualitatively, from equality of the root-multiplicity stratum and
small Iwahori row energy.  The same-stratum part of the global optimized
problem cannot first force an `X`-central root alignment and then invoke
fixed-root coercivity.  It must instead select the full exact endpoint type
adaptively (or use a comparison which simultaneously moves `X` and the
root).

This is not a counterexample to
`uniform-gauge-optimized-induced-energy`: each of the two triples is already
an exact endpoint and repairs itself with zero cost.  It is a counterexample
only to the proposed intermediate selector of one root orbit under `{X}'`.
