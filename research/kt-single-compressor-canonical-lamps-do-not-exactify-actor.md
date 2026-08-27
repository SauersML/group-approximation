---
rg: 2
id: kt-single-compressor-canonical-lamps-do-not-exactify-actor
kind: claim
title: Canonical lamps for one Kun--Thom compressor do not exactify its actor
distinct_from:
  kun-thom-single-compressor-sofic-joint-nonsofic: that proves the restricted coset action is sofic; this converts its canonical permutation models into a normalized-HS obstruction to actor exactification
  kt-wreath-relative-canonical-actor-exactification: that asks for exactification after all actor and multi-compressor relations are imposed; this proves the corresponding one-compressor statement is false even with every canonical lamp mixed trace
  canonical-a5-window-leaves-a-partial-commutant-cocycle: that gives a fixed-window tensor-gauge normal form; this gives a global canonical microstate sequence of an actual sofic one-compressor wreath and proves it stays away from every exact actor representation
  kun-thom-compression-survives-amenable-near-model: that constructs a genuine amenable actor representation whose compression fixed space has zero charge; this constructs canonical lamp-rich finite microstates whose actor leg cannot be exactified
---

**ESTABLISHED.**  Fix one positive strict compressor `t` from the explicit
Kun--Thom pair, put

```text
V=<Gamma,t>,
W_t=(direct_sum_(V/Gamma) C_2) rtimes V.                (KSC1)
```

Then `W_t` is sofic and has a canonical permutation, hence normalized-HS,
microstate sequence `phi_n`.  Nevertheless the actor restrictions
`phi_n|V` do not admit `o_2(1)` correction, even after `o(d_n)` padding, to
genuine finite-dimensional representations of `V`.

More quantitatively, after passing to a subsequence there are a fixed finite
generating set `S_V` and `epsilon>0` such that for every genuine
finite-dimensional representation `pi_n:V->U(D_n)` with
`D_n/d_n->1`,

```text
max_(s in S_V)||phi_n(s) direct_sum 1_(D_n-d_n)-pi_n(s)||_2
 >= epsilon.                                            (KSC2)
```

Thus all canonical Bernoulli cylinder traces, including the mixed
lamp--actor coefficients, are compatible with a uniformly nonexactifiable
actor cocycle.  Any proof of
`kt-wreath-relative-canonical-actor-exactification` must use relations
involving at least two incompatible compressors.  One compressed edge,
property `(T)`, residual finite quotients, finite lamp-packet
exactification, and cylinder-resolved traces are jointly insufficient.

## Proof

`kun-thom-single-compressor-sofic-joint-nonsofic` proves that
`V action V/Gamma` is sofic.  Since `V` is a subgroup of the residually finite
actor `G`, it is sofic; GKP wreath permanence therefore makes `W_t` sofic.
Choose any canonical permutation microstate sequence.

Suppose a subsequence of its actor restrictions admitted the correction in
`(KSC2)` with error tending to zero.  Let `a_Gamma` be the root lamp.  Its
microstate involution almost commutes with `phi_n(Gamma)`.  Property `(T)` of
`Gamma`, applied to conjugation on Hilbert--Schmidt matrices, moves it by
`o_2(1)` to an involution

```text
X_n in pi_n(Gamma)'.                                    (KSC3)
```

The transported involution `pi_n(t)X_n pi_n(t)^*` lies in
`pi_n(t Gamma t^(-1))'`.  Since
`t Gamma t^(-1)<Gamma` and these two finite-dimensional algebras are unitarily
conjugate with one included in the other, finite-dimensional commutant
no-growth gives

```text
pi_n(t Gamma t^(-1))'=pi_n(Gamma)'.                    (KSC4)
```

Choose `gamma in Gamma\t Gamma t^(-1)`.  Equation `(KSC4)` says the rounded
lamp at `tGamma` is fixed by `pi_n(gamma)`.  Returning through the `o_2(1)`
correction says the microstate lamps at `tGamma` and `gamma tGamma` have
distance `o(1)`.  They are distinct group elements of the lamp base, so the
canonical microstate trace makes their normalized `2`-distance tend to
`sqrt(2)`, a contradiction.

If no uniform `epsilon` in `(KSC2)` existed, a diagonal choice of corrections
would give an `o_2(1)`-correctable subsequence, already contradicted.  This
proves the quantitative form.

