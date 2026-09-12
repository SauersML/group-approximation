---
rg: 2
id: kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath
kind: claim
title: The A=CB and B lamp orbit alone is an ordinary sofic regular wreath
distinct_from:
  kt-two-positive-compressors-generate-full-obstruction: That proves Gamma together with A and B generates the full nonsofic Kun--Thom action; this removes Gamma and identifies the entire A,B lamp sector as a standard sofic wreath.
  amenable-multi-compressors-have-a-joint-hs-telescope: That gives only local HS covariance for an amenable Heisenberg compressor pair; this gives canonical permutation microstates for every lamp cylinder and every joint actor word of the nonamenable pair A,B.
  canonical-a5-window-leaves-a-partial-commutant-cocycle: That computes the unitary multiplicity algebra left by an arbitrary fixed lamp window; this identifies a structural reason the proposed A,B-only Cartan transfer cannot reach the Kun--Thom permutation defect even if it succeeds perfectly.
---

**ESTABLISHED.**  In the `d=3` Kun--Thom pair, retain

```text
B=I+E_12,             A=C B,             H=<A,B>.
```

Then `H=SL_3(Z)`.  Its orbit of the base coset is

```text
O=H Gamma subset G/Gamma,
```

and the map `h |-> h Gamma` identifies the `H`-set `O` with the left regular
`H`-set.  Consequently

```text
(direct_sum_O C_2) rtimes H  ~=  C_2 wr H               (KAL1)
```

is residually finite, hence sofic.  It has canonical permutation microstates
which simultaneously realize:

1. every finite Bernoulli cylinder PVM on the `A,B` orbit;
2. exact lamp covariance under both `A` and `B` on every retained interior
   arrow;
3. all joint actor multiplication relations in `<A,B>`; and
4. all canonical mixed lamp--actor traces.

Thus no finite family of cylinder PVMs using only the `A,B` orbit and its
`A,B` covariance can imply the full Kun--Thom permutation defect.  Even a
perfect common `A,B`-normalized masa is compatible with these data.  Any
successful two-compressor unitary-HS transfer must also recover the action of
`Gamma` on the transported cylinders, equivalently a mixed stabilizer table
containing words of the form

```text
gamma w Gamma,          gamma in Gamma, w in <A,B>.     (KAL2)
```

The obstruction is not an `A,B` normalizer problem by itself; it is the
compatibility of that normalizer with the nonnormal Kazhdan stabilizer.

## Proof

`kt-two-positive-compressors-generate-full-obstruction` proves
`H=SL_3(Z)`.  In the semidirect product defining `G`, the external
`SL_3(Z)` factor intersects the Laurent elementary factor, hence `Gamma`,
trivially.  Therefore

```text
h_1 Gamma=h_2 Gamma  iff  h_2^(-1)h_1 in H intersect Gamma
                         iff h_1=h_2,
```

which proves that `O` is regular.

The group `H` is residually finite.  For completeness, the restricted wreath
by a finite base is residually finite directly.  Given a nonidentity
`(f,h) in C_2 wr H`, if `h!=1`, choose a finite quotient of `H` detecting
`h`.  If `h=1`, choose a finite quotient injective on the finite support of
`f` and on all pairwise support differences.  Push `f` to the quotient by
summing along quotient fibers; injectivity on the support prevents
cancellation.  In either case a finite wreath quotient detects `(f,h)`.
This proves `(KAL1)` is residually finite.

Its regular finite quotients provide the stated canonical permutation
microstates.  Fourier transformation of each finite binary lamp base gives
one common cylinder PVM normalized by the actor permutations, so even the
strongest desired `A,B`-only masa conclusion holds in this counterpacket.
The full defect from
`kt-two-positive-compressors-generate-full-obstruction` can therefore enter
only through the omitted `Gamma` action in `(KAL2)`.

DERIVATION
kt-two-compressor-lamp-orbit-sofic-proof
