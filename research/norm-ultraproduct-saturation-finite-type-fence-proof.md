---
rg: 2
id: norm-ultraproduct-saturation-finite-type-fence-proof
kind: route
title: Isolate the unsatisfied bounded Leavitt fragment before invoking saturation
target: norm-ultraproduct-saturation-does-not-decode-corona-root-germs
requires:
  - finite-root-heisenberg-multiplicity-germs
  - finite-root-windows-share-one-reducing-corona-carrier
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

Choose projection lifts `P_n` of `P`.  Since `P!=0` in the Fréchet norm
corona, the set

```text
I={n: P_n!=0}
```

is infinite.  A free ultrafilter containing `I` sends `P` to a nonzero
projection `p` in `A_U`.  The root-group relations and eventual rank-germ
identities survive this quotient.  This step does not create any new
coefficient operators.

Fix a variable bound `K>=1`.  Suppose that lifts in the square corner
`P_n M_(d_n)(C) P_n` satisfy

```text
||T_0S_0-P_n|| <= epsilon,
||T_1S_1-P_n|| <= epsilon,
||S_i||,||T_i|| <= K,
```

with `epsilon<1`.  On the range of `P_n`, the first two products have least
singular value at least `1-epsilon`.  Therefore

```text
s_min(T_0) >= (1-epsilon)/K,
s_min(S_1) >= (1-epsilon)/K.
```

Multiplicativity of the least singular value gives

```text
||T_0S_1|| >= s_min(T_0S_1)
             >= (1-epsilon)^2/K^2.                    (SFP1)
```

This coordinate inequality passes to the norm ultraproduct.  If the
off-diagonal residual is also at most `epsilon`, then `(SFP1)` is impossible
for `epsilon<min(1/2,1/(4K^2))`.  Hence the three formulas `(NSF1)` form a
finite subset of the full ring-action type which is not approximately
satisfiable on the nonzero corner.

There is also a bound-free fence.  The normalized trace on each nonzero
coordinate corner gives

```text
1 <= ||T_0S_0-P_n||+||T_1S_1-P_n||
     +||S_0T_0+S_1T_1-P_n||,
```

so the three residuals in `(NSF4)` cannot all be below `1/3`.  This is the
Atomic Leavitt Gap.

Now compare the logical languages.  A finite Heisenberg window gives an
actual representation of one finite root group.  For a finite chain of
windows, a largest window can realize all smaller Fourier and isotypic
decompositions coherently.  These are facts about the already given root
unitaries and their multiplicity projections.  The rank germs themselves
are external projective-dimension data; they are not existential witnesses
for bounded `S_i,T_i` in the C-star language.  Saturation of `p A_U p` does
not automatically extend to a new sort containing those germs.

Countable saturation also requires each variable to lie in one fixed norm
ball.  Allowing a separately exactified intertwiner to have norms which grow
with the window does not define a finitely satisfiable bounded type.  No
uniform bounds are presently supplied because no coefficient intertwiners
are presently supplied at all.

For the intended ring `L_(F_2)(1,2)`, every finite coefficient set is
contained in a finite additive subgroup, so finite root windows do exhaust
the root-group coefficient equations.  The generic formulation of
`corona-coefficient-module-decoder` for an arbitrary countable ring has an
additional hypothesis gap: `finite-root-heisenberg-multiplicity-germs`
only treats finite additive subgroups, which need not exhaust a ring whose
additive group is not locally finite.

Finally, if the desired type is read literally as a unital ring homomorphism
from the characteristic-two algebra `L_(F_2)(1,2)` into the complex corner,
it contains the still smaller impossible scalar equation `p+p=0`.  The
characteristic-free terminal content intended by the decoder is therefore
the four Leavitt operators, and the finite fragments above show that even
that weaker type has not been shown finitely satisfiable.

