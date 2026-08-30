---
rg: 2
id: remote-bernoulli-profile-orbit-obstruction-proof
kind: route
title: A periodic projection below one Bernoulli cylinder lies below a null infinite intersection
target: remote-bernoulli-padding-destroys-profile-pure-finite-orbits
requires: []
---

Let

```text
Y={0,1}^Z
```

with Bernoulli product measure, and add the free central sign coordinate used
by the ZPC model. Let a new readable involution `b` act as `J^(y_0)`. Let
new unreadable involutions `r,s` act on `Y` by the coordinate reflections

```text
(r y)_k=y_(-k),
(s y)_k=y_(1-k).
```

Their product `w=rs` is a bilateral shift. Place `b,r,s` at remote dummy
vertices so that no original verifier row sees them and all new checks are
identically accepting. The original strategy tensored with this action is
therefore perfect and ZPC.

Mix the old verifier into `G^B` with any fixed positive probability `eta` and
use the dummy checks otherwise. Every quantum strategy then has loss at
least `eta(1-omega*(G))`, proving

```text
omega*(G^B)<=1-eta(1-omega*(G))<1.
```

If the source value is `v<1/2`, choosing
`eta>1/(2(1-v))` also retains `omega*(G^B)<1/2`.

Now let `E_a` be a full readable profile projection whose Bernoulli
coordinate has value `y_0=a`. Suppose

```text
0!=p<=E_a
```

has finite orbit under the unreadable structural group. Its orbit under the
single word `w` is finite, so for some `n>=1`,

```text
pi(w^n)p pi(w^n)^*=p.                                  (RBP2)
```

Since `p<=q_-1_(y_0=a)`, conjugating by every power of `w^n` and using
`(RBP2)` gives

```text
p<=q_-1_(y_(kn)=a)       for every k in Z.              (RBP3)
```

The commuting multiplication projections on the right have meet zero:
the Bernoulli event `y_(kn)=a` for all `k` has measure zero. Hence `(RBP3)`
forces `p=0`, a contradiction. No diagonality of `p` was assumed; a
projection subordinate to every member of a commuting family is subordinate
to their meet.

The Bernoulli shift is weakly mixing, so its product with an ergodic original
component is ergodic. For the standalone always-accept padding factor,
replacing `Y` by an `N`-cycle gives a finite signed-permutation perfect
model whose readable translate algebra is finite. These cyclic padding
actions converge on every fixed cylinder to the Bernoulli padding action,
which has no nonzero finite-orbit projection below a readable profile. Thus
finite-orbit structure is not weak-star closed even in the elementary
always-accept ZPC class. This observation does not assert that tensoring a
cyclic padding factor with an arbitrary original witness gives the total
product a finite orbit; it shows exactly why fixed-cylinder compactness
cannot preserve such structure without a separate uniform bound.

This padding does not refute
`perfect-gap-zpc-has-profile-pure-finite-projection-orbit`: that claim may
select a different, source-specific unpadded maximizing witness. It proves
that any positive argument must use such a selection theorem and cannot rely
only on the formal ZPC axioms, ergodic decomposition, or pseudo-IRS
compactness.
