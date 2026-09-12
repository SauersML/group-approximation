---
rg: 2
id: linear-cocycle-phase-countersequence-proof
kind: route
title: Count low-error interval phases in a backward-neighbor ordering
target: linear-cocycle-dimension-forces-phase-countersequence
requires:
  - link-thresholds-need-macroscopic-phase-frustration
---

We prove a sampling-order lemma first. Fix

```text
alpha=1/4,       sigma=1/16.                            (LCP1)
```

At every vertex, label its `m` incident edges bijectively by `Z/mZ` using
one of the link coordinates. Given `epsilon>0`, put

```text
D=ceil(2 epsilon m/sigma)+1.                            (LCP2)
```

For all sufficiently large `m`, there is an ordering of the vertices with
the following property: if `v` is not among the first `alpha V` vertices,
then for every cyclic interval `J` of at least `D` incident-edge labels,

```text
|{e in J: the other endpoint of e precedes v}|
 >=sigma |J|.                                           (LCP3)
```

To see this, choose a uniform random vertex ordering. Conditional on the
position of a late vertex, the number of earlier endpoints in a fixed
`J` is hypergeometric with mean at least `(alpha/2)|J|` for all large
`V`. The lower-tail Chernoff bound makes failure of (LCP3) at most

```text
exp(-c alpha |J|)
```

for a universal `c>0`. There are at most `V m^2` pairs `(v,J)`. Also
`V<=m^2`, because `|SL_2(Z/mZ)|<=m^3` and `|P|>=m`. Since
`D` is a positive multiple of `m`, a union bound proves the lemma.

Fix such an ordering and a cocycle `z`. Process the interval shifts
`q_v in Z/mZ` in vertex order. When the phases at earlier vertices are
known, every backward edge at `v` prescribes one target bit for the
translated interval indicator at `v`.

Suppose two phases `q` and `q'` each disagree with their target on at most
`epsilon m` backward edges. The symmetric difference of two cyclic
intervals of length `(m-1)/2` is the disjoint union of two cyclic
intervals, each of length equal to the cyclic distance

```text
d_cyc(q,q')<= (m-1)/2.                                  (LCP4)
```

If `d_cyc(q,q')>=D`, the sampler property (LCP3) finds at least
`2 sigma D>2 epsilon m` backward labels in this symmetric difference.
That contradicts the triangle inequality for the two error sets. Hence
all admissible phases have pairwise cyclic distance less than `D`.
They lie in a cyclic arc of length at most `2D`, so, for all sufficiently
large `m`, their number is at most

```text
rho m,       rho=5 epsilon/sigma=80 epsilon.            (LCP5)
```

Now suppose `c_eta` differs from the fixed `z` on at most `delta E`
edges. Assign every edge discrepancy to its later endpoint. A late vertex
is called bad if it receives more than `epsilon m` discrepancies. Since
`E=mV/2`, there are at most

```text
delta E/(epsilon m)=delta V/(2epsilon)                  (LCP6)
```

bad late vertices. The first `alpha V` vertices and these bad vertices
may choose arbitrary phases. Every other vertex has at most `rho m`
choices by (LCP5).

Union over the possible bad-vertex sets. Ignoring harmless integer
rounding, the number of phase assignments within `delta E` of this one
cocycle is at most

```text
2^V m^(beta V) (rho m)^((1-beta)V)
 =2^V rho^((1-beta)V)m^V,                              (LCP7)

beta=alpha+delta/(2epsilon).
```

Choose `delta=epsilon^2`. Then `beta=1/4+epsilon/2`.
Under (LCD2), unioning (LCP7) over every cocycle gives at most

```text
[2^(C+1) rho^(1-beta)]^V m^V.                           (LCP8)
```

As `epsilon` tends to zero, `rho=80epsilon` tends to zero while
`1-beta` tends to `3/4`. We may therefore choose `epsilon=epsilon(C)>0`
so small that the bracket in (LCP8) is strictly below one. Put

```text
delta_C=epsilon(C)^2.                                   (LCP9)
```

For every sufficiently large level, (LCP8) is then smaller than the total
number `m^V` of phase assignments. Some assignment is farther than
`delta_C E` from every cocycle, proving (LCD5).

Finally, the threshold-globalization theorem applies to every phase
assignment, including the one just selected. With the corrected
central-sign multiplicity, each link interval has `4(m-1)` bad face rows,
`|P|=2mn`, and hence its all-vertex union has syndrome

```text
4V(m-1)/|G|=2(m-1)/(mn)<2/n.
```

This proves (LCD4) and completes the conditional theorem.
