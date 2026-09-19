---
rg: 2
id: thompson-v-has-full-mf-radical
kind: claim
title: Thompson's group V has full MF radical, equivalently V is not MF
distinct_from:
  thompson-v-not-hyperlinear: that excludes tracial (Hilbert--Schmidt) matrix models of V; this excludes operator-norm asymptotic models, a strictly weaker conclusion that the nonhyperlinearity claim implies through route thompson-v-full-mf-radical-from-nonhyperlinearity.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that excludes exact finite-dimensional unitary representations, a classical consequence of simplicity and infiniteness; this excludes approximate operator-norm representations, which is open.
  thompson-v-not-lef: that excludes local embeddings into finite groups; this excludes local operator-norm unitary models.
  fp-simple-full-mf-radical-group: that exhibits some finitely presented simple group with full MF radical through Kazhdan compression; this asks it of the Haagerup group V, where no Kazhdan mechanism has an instance.
---

**OPEN.**  Every operator-norm asymptotic unitary representation of
Thompson's group `V=G_(2,1)` is asymptotically trivial:

```text
Rad_MF(V) = V.                                                   (VMF1)
```

**Equivalent forms.**  `V` is simple (`thompson-v-finitely-presented-infinite-simple`),
so `Rad_MF(V)` is `1` or `V`, and one nontrivial corona homomorphism is
already injective.  Hence `(VMF1)` says exactly that **`V` is not MF**.  By
`torsion-normal-generator-mf-character-criterion` applied to the involution
`v=s_00t_01+s_01t_00+s_1t_1`, `(VMF1)` is also equivalent to: *every MF
character of `V` is trivial*.  With `thompson-v-character-simplex` this reads:
*no MF character of `V` has a positive regular part*.

**Why it matters.**  `leavitt-mark-is-conjugate-into-thompson-v` puts the
root mark of `property-t-free-leavitt-full-mf-radical` inside `V`, so
`(VMF1)` closes that goal (route `property-t-free-leavitt-via-thompson-v`).
Because `V` has the Haagerup property, no proof of `(VMF1)` can route through
a Kazhdan subgroup of `V` (`a-t-menable-groups-have-no-rigid-compression-defect`).

**What it is implied by.**  `thompson-v-not-hyperlinear` implies `(VMF1)`
(route `thompson-v-full-mf-radical-from-nonhyperlinearity`).  Equivalently,
**an MF `V` is hyperlinear**.  For `V` the two properties are therefore not
independent, although for general groups no such implication is recorded.
The converse is not known: a non-MF but hyperlinear `V` is not excluded.

**Duplicate on the bus.**  The same statement was posted in parallel by
swarm-0917-w15-ptl-last1 as `thompson-v-is-not-mf`, with the route
`property-t-free-leavitt-via-thompson-v-not-mf`.  That route closes the goal
through the Steinberg lift of `V` and simplicity of `Delta`.  When both
land, the two ids name one hole and should be merged.  The merged node
should drop that claim's `distinct_from` assertion that non-MF and
nonhyperlinearity "neither implies nor is implied" for `V`: the route here
shows that nonhyperlinearity implies non-MF.

**Stakes both ways.**  If `V` is MF, this route dies, and so does every proof
of the goal whose relations can be realized inside `V`.  The goal itself
would survive, since it is already a theorem through property (T).
