---
rg: 2
id: signed-hecke-detectors-are-uniformly-mark-saturated-but-untyped
kind: claim
title: Every nontrivial signed-Hecke detector uniformly saturates the mark, but saturation loses source typing
artifacts:
  - research/signed-hecke-detector-saturation-and-source-fence-proof.md
  - experiments/signed_hecke_detector_normal_closure_audit.py
  - experiments/signed-hecke-detector-normal-closure.json
distinct_from:
  middle-pauli-probes-leave-three-signed-hecke-detector-classes-untyped: that tests the literal paid 48-word dual menu and the full 48-word primal return menu on the 31 externally probed classes; three endpoint classes still admit no elementary extraction, and the only source-preserving paid-menu words centralize the detector group.
  paid-t00-carrier-has-signed-hecke-reynolds-dichotomy: that makes one of 8192 ordinary detector words pay on the paid carrier, or retains the native discrepancy on the signed source; this audits every detector algebraically and determines exactly why normal saturation does not turn its payment into source incidence.
  binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale: that uniformly compares two elementary roots by Leavitt sandwiches; most detectors here are products of roots, and the first step is to extract one nonzero root from such a product.
  native-actor-normal-closure-does-not-localize-paid-t00-support: that fences conjugation of the paid discrepancy by the native Whitehead actor menu on its three-bit constant atom; this fences detector saturation while preserving the actual signed source group.
---

**ESTABLISHED SATURATION WITH SOURCE-TYPING FENCE.**  Work in

```text
Delta=St_20(L_(F_2)(1,2)),       z=x_13(q),
Q=e_(L_0,lambda_0),              |L_0|=8192,
r_g=z^((1-lambda_0(g))/2)g.                         (DSF1)
```

The character has two fibers of size `4096`.  Exactly one detector is the
identity, namely `r_1`.  Every other detector is nontrivial.  More strongly,
for every `g!=1` with `lambda_0(g)=+1`, a two-spare-index Steinberg
commutator extracts a nonzero elementary root as a product of at most four
conjugates of `r_g` or its inverse.  For `lambda_0(g)=-1`, one common
spare-index probe commutes with `g` and extracts a nonzero root from the
`z` factor as a product of two conjugates.  The uniform Leavitt sandwich then
gives

```text
z = product of at most 16 conjugates of r_g^(+/-1)    (DSF2)
```

for all `8191` nonidentity detectors; the bound improves to `8` on the
negative-character half.

Conversely, the ten displayed generators of `L_0` are nonzero elementary
roots, hence each is a product of at most four conjugates of `z`.  A shortest
word for an element of the `8192`-vertex Cayley graph has length at most
`8191`.  Therefore

```text
r_g = product of at most 32765 conjugates of z^(+/-1). (DSF3)
```

Thus every nontrivial detector and the mark normally generate one another
with bounds uniform over the complete menu.  In particular, a detector
operator-norm spike can be rewritten as a spike of some conjugate of a named
marked root with a fixed quantitative loss.

This does **not** close the detector branch of `(PSD5)`.  Normal saturation
turns largeness of `(r_g-1)C` only into largeness of a conjugated root on a
unitarily moved or untyped carrier.  It proves neither smallness of `r_g`,
incidence with `Q`, nor an occurrence identity with either native selector
row.  The extracting probes use indices outside the seven-coordinate actor
and need not normalize `(L_0,lambda_0)`.

That loss of typing is necessary, not an artifact of the proof.  The exact
normal-closure audit of the faithful `8192`-element actor table finds `511`
nonidentity positive-character conjugacy classes.  Of these, `480` normally
contain an internal root in at most two conjugate occurrences, but the
remaining `31` contain none of the `13` internal root transvections.  Hence a saturation
argument which stays inside the source normalizer cannot handle all positive
detectors; at least those classes require an external probe, precisely where
the signed-source projection ceases to be controlled.

Accordingly full Steinberg/Leavitt relations make every nontrivial detector
uniformly **mark-saturated**, but do not make any detector a relator and do
not supply the missing native occurrence.  A successful continuation still
needs an independently typed relation controlling the external probe on
`Q`, or a direct upper bound for the finite detector menu.  No Property T,
Kazhdan input, canonical trace, stability theorem, or literature input is
used.

DERIVATION
signed-hecke-detector-saturation-and-source-fence-proof
