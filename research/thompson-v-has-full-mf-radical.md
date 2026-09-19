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

## Attempts

- **swarm-0917-w17-w17-ptm-pull (2026-09-19), entropy-measure and
  Cuntz/Tarski transplants, both dead; target stays OPEN.**
  (a) Any measure/entropy/trace invariant read off a limit of an MF model is
  a character of `V`, and by `thompson-v-character-simplex` every such
  character is realized by trivial and regular representations
  (`lambda` is not an obstruction). So trace-level arguments die a priori.
  (b) Rank counting. Transplant the `O_2` paradox `[1]=2[1]` by assigning to
  a clopen set `A` the rank of the nontrivial part of finite subgroups
  supported in `A`. This needs support additivity for disjoint free
  involutions. `thompson-v-mf-models-overlap-disjoint-involutions` (ESTABLISHED,
  lane proof) shows that in every operator-norm model, all free proper
  involutions have the same `-1` rank `M_n`. Disjoint pairs overlap in
  exactly `M_n/2`, so `rank(1-e_{<a,b>})=(3/2)M_n`. Additivity is then
  equivalent to `M_n=0`, i.e. to the goal itself, at every scale. All
  finite-subgroup rank data are realized by `trivial^a + b regular` of the
  dyadic permutation groups `W_N`. **Survivors:** arguments using
  infinite-order elements of `V`, or the relative position of the
  eigenspaces of non-commuting finite subgroups.

- **swarm-0917-w19-w19-ptl-pull (2026-09-19), symbolic-dynamics transplant, dead; target stays OPEN.**
  Every construction that reads an MF model of `V` off the Cantor dynamics is dead at a named step:
  - covariant or cylinder-indexed projections in the model: `c = 2c`
    (`thompson-v-cantor-system-has-no-covariant-rank-model`, and its operator-norm form, since
    projections within distance `< 1` have equal rank);
  - compressions of covariant representations: Bekka non-amenability
    (`thompson-v-covariant-cantor-representations-are-not-amenable`);
  - models whose norm profile is dominated by a spatial representation (strong convergence to Koopman,
    orbit `l^2`, or Cuntz/Jones representations): new, `thompson-v-germ-local-representations-contain-unital-o2`.
    `V_B` has spectral gap on `rho(1_B)H`, because there is no invariant measure. So `rho(1_A)` lies in `C*_pi(V)`, and
    `v_i = pi(g_i)rho(1_[0]) + pi(h_i)rho(1_[1])` is a Cuntz pair inside `C*_pi(V)`. The model's quotient would put a
    proper isometry in the finite algebra `Q`.

  **Invariant:** proper infiniteness of `C*(V)` in its germ-local completions.
  **Death step:** `q(v_0)` is an isometry in `Q`.
  **Survivors:** witnesses `psi` with `lambda ≺ psi` whose norm profile is not dominated by any `O_2`-representation
  of `V` (non-spatial, non-covariant). This is consistent with the dense-projective-image regime of bus need
  9a535093 and with `thompson-v-gap-witnesses-need-unbounded-lie-closure`.
