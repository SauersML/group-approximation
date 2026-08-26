---
rg: 2
id: sofic-central-covers-need-nontorsion-classes
kind: claim
title: A sofic central cover of a nonsofic group has infinite center and a class that stays non-torsion on every finite-index subgroup, so finite central extensions and torsion classes can never feed Thom's central-quotient descent
distinct_from:
  thom-central-corner-criterion: that is the positive descent statement (central quotients of hyperlinear groups are hyperlinear), which is what makes a sofic central cover of a nonsofic group a Pestov 3.4 witness; this is the elementary constraint on which covers could possibly be sofic.
  leavitt-all-countable-central-covers-are-nonsofic: that kills every central cover of the binary Leavitt unit group by lifting the compression configuration through universal central extensions; this is the general elementary part, valid for any nonsofic quotient, and it is what shows the remaining candidates must have non-torsion classes.
  gohla-thom-stable-base-nonsofic-extension: that produces nonsofic central extensions from a sofic base under stability and cosystolic hypotheses; this goes the other way, asking when a central extension of a NONSOFIC group can be sofic.
---

**The route.**  By `thom-central-corner-criterion` (Thom, Remark 3.4 of
arXiv:0810.2180) a central quotient of a hyperlinear group is hyperlinear.
Hence if some nonsofic group `Q` (the Kun--Thom wreath or double, or the
Leavitt group) had a **sofic** central cover `1 -> Z -> S -> Q -> 1`, then
`Q` would be hyperlinear (sofic implies hyperlinear, then descend) and
nonsofic: the Pestov 3.4 separation.  Soficity is not known to pass to
central quotients, so this is a genuine, if narrow, route.

**Theorem** (elementary constraints).  Let `1 -> Z -> S -> Q -> 1` be a
central extension with `S` sofic and `Q` nonsofic.  Then:
1. `Z` is infinite; more precisely `Z` has no finite subgroup `F` with
   `S/F`'s quotient map to `Q` -- equivalently, one may divide out the
   torsion of `Z` and the statement persists.  (Quotients of sofic groups by
   finite normal subgroups are sofic.)
2. The class `c in H^2(Q; Z)` of the extension (for `Z = Z^k`, in each
   coordinate) is not torsion: if `n c = 0` then `S` embeds with index `n`
   in `Z x Q`, which would make `Q` sofic.
3. The same holds after restriction to every finite-index subgroup
   `Q_0 <= Q`: the restricted class is non-torsion in `H^2(Q_0; Z)`.  In
   particular `H^2(Q_0; Q) != 0` for every finite-index `Q_0`, and if some
   finite-index subgroup of `Q` has vanishing rational second cohomology
   then `Q` has no sofic central cover at all.

**Where this leaves the Kun--Thom objects.**  For the Leavitt group the
route is closed outright by `leavitt-all-countable-central-covers-are-nonsofic`
(the compression configuration lifts through universal central extensions
because the Kazhdan groups involved are perfect).  For the Kun--Thom wreath
`W` and double `D` no analogous node exists; the same mechanism is expected
to apply -- the (T)-part of the preimage of `Gamma` survives any central
extension, the lamp lift still centralizes it because the commutator map
into the center is a homomorphism vanishing on Kazhdan groups, and
Kun--Thom's Theorem 4.1 then reproduces the contradiction -- but it is not
recorded as established here.  Independently of that, (3) makes the route
hostage to rational `H^2` of finite-index subgroups of `W` and `D`; for `W`,
Hochschild--Serre with torsion lamps gives `H^2(W; Q) = H^2(G; Q)`, and the
corresponding computation for `G = EL_r(F_q[x^(+-1)]) x| SL_d(Z)` is open.
