---
rg: 2
id: kt-a2-heisenberg-flat-wall-survives-one-more-compressor
kind: claim
title: The nested Kun--Thom flat wall survives the first rank-two Steinberg packet
distinct_from:
  kt-nested-compressor-flat-tower-has-uniform-wall: That constructs the wall for the one-compressor ascending-HNN packet; this adds a second external elementary generator, its commutator direction, and every rank-two Heisenberg relation without losing the wall.
  amenable-multi-compressors-have-a-joint-hs-telescope: That copies arbitrary fixed coefficient tables over a Folner compression monoid but does not build a nested relative-commutant wall; this synchronizes a depth-dependent commutant gauge across the two transverse directions and proves a uniform marked-return gap.
  kt-two-positive-compressors-generate-full-obstruction: That uses the nonamenable pair A=CB,B which generates the full external SL_3(Z) actor and proves a canonical permutation obstruction; this treats the smallest amenable A2 unipotent packet and proves it remains flexible in normalized Hilbert--Schmidt norm.
  kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath: That identifies the unrestricted A,B lamp orbit as a regular wreath and does not retain the polynomial stabilizer wall; this retains the nested Gamma-commutant gauge but only for the Heisenberg unipotent pair.
  bare-relative-wall-exists: That demands a wall for the whole Kun--Thom actor G; this proves that adjoining one transverse elementary generator and all of its rank-two Steinberg relations still does not provide that extension.
---

**ESTABLISHED SCOPED FLEXIBILITY THEOREM.**  In the `d>=3` Kun--Thom
polynomial actor take the external elementary matrices

```text
t=u_12=I+E_12,       s=u_23=I+E_23,       r=u_13=I+E_13. (KAH1)
```

They satisfy the rank-two Steinberg/Heisenberg packet

```text
t s=r s t,           [t,r]=[s,r]=1.                     (KAH2)
```

Let `alpha_u(delta)=u delta u^(-1)` on `Gamma`, let
`gamma=e_(ab)(x_2)`, and put `h=t^(-1) gamma t`.  There are, for every
`L`, one exact finite-dimensional representation `Pi_L` of `Gamma` and two
sets of actor unitaries

```text
(T_(0,t),T_s,T_r),          (T_(1,t),T_s,T_r)            (KAH3)
```

on the same space such that:

1. the two maps agree exactly on `Gamma`, on `s`, and on `r`;
2. every covariance row

   ```text
   T_u Pi_L(delta)T_u^*=Pi_L(alpha_u(delta)),
                  u in {t,s,r},                          (KAH4)
   ```

   has normalized-Hilbert--Schmidt defect `O(L^(-1/2))` for both maps;
3. every relation in `(KAH2)` has defect `O(L^(-1/2))` for both maps; and
4. the returned `t`-fold remains uniformly separated:

   ```text
   ||T_(0,t)^*Pi_L(gamma)T_(0,t)
       -T_(1,t)^*Pi_L(gamma)T_(1,t)||_2^2
       >=2(1-1/L).                                        (KAH5)
   ```

Thus one additional external elementary generator, its commutator root,
and the complete smallest A2 Steinberg packet do **not** obstruct the flat
wall.  The first possible obstruction must use either a nonamenable family
of compressor directions (such as the full-actor pair `A=CB,B`) or mixed
`Gamma`-incidence data not contained in this Heisenberg packet.  This does
not construct approximate representations of the full Kun--Thom actor.

Proof: `kt-a2-heisenberg-flat-wall-proof`.
