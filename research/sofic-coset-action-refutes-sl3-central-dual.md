---
rg: 2
id: sofic-coset-action-refutes-sl3-central-dual
kind: claim
title: Soficity of the large-prime SL3 coset action forces a canonical central-dual counterexample
distinct_from:
  sl3-regular-double-collapse-forces-nonsofic-vertex-action: that treats the dyadic adjacent double and its one fold word; this treats every prime at least eleven and the complete central-dual matrix-range inequality for the centralizer HNN group.
  sl3-dyadic-building-vertex-action-is-sofic: that is the open positive action claim at p=2; this is a proved implication from action soficity at any fixed large prime to failure of the proposed central-dual collapse.
  finite-lamp-frame-is-matrix-range-neutral: that forgets coherent arithmetic actor covariance and gives unconditional finite lamp countermodels; this retains the full actor covariance conditionally on a genuine sofic action atlas.
---

**ESTABLISHED DYNAMICAL FORK.**  Fix a prime `p>=11` and put

```text
Lambda=SL_3(Z),       Gamma=SL_3(Z[1/p]),
G_p=<Gamma,t | [t,Lambda]=1>,       X=Gamma/Lambda.             (SCD1)
```

If the transitive action `Gamma curvearrowright X` is sofic, then `G_p` is
sofic.  In particular there is a canonical matrix approximation of `G_p`
for which `(LCG3)` in `sl3-hnn-central-dual-gap-vanishes` fails: along a
subsequence there are uniformly operator-bounded, normalized separator
tuples asymptotically commuting with the stable letter and having a fixed
positive matrix-range gap.

Indeed `centralizer-hnn-is-free-generalized-wreath` identifies

```text
G_p ~= Z wr^*_(Gamma curvearrowright X) Gamma.                   (SCD2)
```

The actor `Gamma` is residually finite, hence sofic, and `Z` is amenable.
`gkp-free-wreath-permanence` makes `(SCD2)` sofic.  If `(LCG3)` held for
every canonical approximation, then
`sl3-hnn-central-dual-gap-implies-matrix-range-capture`, the established
large-prime exact-face reduction, and
`non-hyperlinear-from-sl3-large-prime-collapse` would make this same group
nonhyperlinear, a contradiction.  Hahn--Banach plus central-letter averaging
then supplies the stated bounded separator on a canonical sofic sequence.

Thus the actor-covariant survivor is an exact action-soficity fork, not an
unspecified collection of additional moments.  A proof of the central-dual
claim necessarily proves that the type-zero vertex action
`Gamma curvearrowright Gamma/Lambda` is nonsofic.  Conversely, a sofic atlas
for that action produces the full finite-coordinate enemy, including the
same actor matrices permuting the lamp frame and transporting the lattice
tuple.

DERIVATION
sofic-action-free-wreath-counterexample-proof
