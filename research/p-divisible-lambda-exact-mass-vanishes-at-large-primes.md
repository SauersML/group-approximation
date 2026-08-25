---
rg: 2
id: p-divisible-lambda-exact-mass-vanishes-at-large-primes
kind: claim
title: At large primes the p-divisible weight of a near-genuine microstate of the SL3 pair vanishes with the defect, independently of depth
distinct_from:
  lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible: that bounds the p-divisible weight by depth times defect and leaves ultra-deep towers alive; this bounds it by the defect alone, with no depth, once the deep-level Clifford constant exceeds 3/4.
  odd-congruence-lambda-exact-sector-collapses: that closes the coprime-level sector using the exact slot for h; this shows that at large primes every near-genuine microstate is asymptotically of coprime level.
  homogeneous-quotient-near-genuine-microstates-are-deep: that forces homogeneous-quotient microstates to be p-adically deep; combined with this theorem it shows that algebra has no near-genuine microstates at p >= 11.
---

**THEOREM (established here; proof in
`p-divisible-mass-vanishes-depth-free-proof`).**  Use the notation of
`lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible`: `C=SL_3(Z)`,
`h=diag(p,1,1/p)`, `C_0=C cap h^-1 C h` with Kazhdan constant `kappa_0`,
`rho'` a genuine representation of `C` of level `p^D m'`, `nu_0` the weight
of its trivial-`p` part, and `H` a unitary with `h`-twist defect at most
`epsilon` on the generators of `C_0`.  Put

```text
c_p = 1 - (p^2+p-2)/(p^3-1) - 1/(p+1),
a_p = min(4 c_p-3,1/3).
```

For every `p>=11` and every depth `D`, if `w_1` is the isotypic weight
measure of `rho'|_(C_0)` and `w_2` that of its `Ad(Jh)`-twist, then

```text
a_p(1-nu_0) <= TV(w_1,w_2) <= 12 epsilon/kappa_0.                         (PV1)
```

With the Kazhdan-constant normalization in `(UD1)`, orthogonality of the
Kazhdan projection sharpens the upper bound to

```text
TV(w_1,w_2) <= epsilon^2/kappa_0^2.                                      (PV1-square)
```

Since `c_p>3/4` exactly for `p>=11`, `a_p>0`.  Hence the `p`-divisible
weight tends to zero with the defect, independently of depth.

**Mechanism.**  Give each irreducible constituent of `rho'|_(C_0)` its
upper and lower simple-root depths `(beta,gamma)`.  The twist by `g=Jh`
acts by

```text
(beta,gamma) |-> (gamma-1,beta+1),                                      (PV2)
```

so `(a,a)` maps to `(a-1,a+1)`.  For levels `a>=2`, Clifford theory on the
last congruence layer puts at least `2c_p-1` of the restricted mass on
`(a,a)` and at most `2(1-c_p)` on all off-diagonal types.

Level one is not a Lie layer.  The three conjugate transvection subgroups
`U_12,U_23,U_31` generate `SL_3(F_p)`.  Their common fixed space in a
nontrivial irreducible is zero, so subadditivity of codimension puts at
least `1/3` of level-one mass on `(1,1)`.  For

```text
S = {(a-1,a+1) : a>=1},
```

level zero and level one give no mass to `w_1(S)`, while every contribution
from levels at least two is off diagonal.  Therefore

```text
TV(w_1,w_2) >= (4c_p-3) sum_(a>=2) nu_a + (1/3)nu_1
             >= a_p(1-nu_0),
```

proving the depth-free lower bound.  A single Kazhdan projection gives the
two upper bounds.

**Consequences.**

- At `p>=11` ultra-deep towers are excluded along with all shallower
  `p`-divisible towers.  Together with
  `coprime-sector-collapse-is-robust-to-small-p-admixture`, this closes the
  entire `Lambda`-exact face.  Only uniformly non-correctable lattice
  microstates remain.
- The homogeneous-quotient crossed product at `p>=11` has no microstates
  whose `SL_3(Z)` part is near a genuine representation: its cell structure
  forces `nu_0->0`, while `(PV1)` forces `nu_0->1`.
- Nothing is claimed at `p<=7`.  The separate level-one argument is
  essential because `Gamma(1)/Gamma(p)=SL_3(F_p)`, whereas the additive Lie
  layer description begins only at level two.
