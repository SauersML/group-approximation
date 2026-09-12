---
rg: 2
id: lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible
kind: claim
title: The p-divisible Lambda-exact sector of the SL3 pair is negligible unless its p-adic depth exceeds the inverse defect
distinct_from:
  odd-congruence-lambda-exact-sector-collapses: that closes the Lambda-exact sector whose congruence levels are coprime to p, by the exact slot for h and the Weyl relations; this bounds the weight of the complementary p-divisible levels, for which no exact slot exists, in terms of depth times squared defect.
  homogeneous-quotient-near-genuine-microstates-are-deep: that constrains microstates of the homogeneous-quotient crossed product using its cell structure; this needs no cells and applies to any near-genuine microstate of the pair, giving a weight bound rather than a depth bound.
  fixed-shift-invariance-does-not-force-flat-profile: that refutes an inference from shift invariance to a flat profile on the p-divisible sector; this is a positive theorem on the same sector, with an explicit inequality, and is compatible with that refutation (triangular profiles of ultra-deep towers are not excluded).
---

**THEOREM (established here; proof in
`lambda-exact-p-divisible-ultra-deep-proof`, sharpened by
`orthogonal-kazhdan-powers-have-quadratic-depth-loss`).**  Let `p` be any prime,
`C = SL_3(Z)`, `h = diag(p, 1, 1/p)`, `C_0 = C cap h^-1 C h`, `S_0` a finite
generating set of `C_0` with Kazhdan constant `kappa_0`, and

```text
c_p := 1 - (p^2 + p - 2)/(p^3 - 1) - 1/(p + 1),
b_p := min(c_p,1/3)                                  (b_p > 0 for every prime).
```

Let `rho' : C -> U(d)` be a genuine representation, factoring through
`SL_3(Z/N)` with `N = p^D m'`, `p` not dividing `m'`, and let `nu_0` be the
normalized dimension of the subspace on which the `p`-part of `rho'` is
trivial (the constituents `pi'_p (x) pi'_(m')` with `pi'_p` trivial, i.e.
the fixed space of `rho'(Gamma(m'))`).  Let `H in U(d)` satisfy

```text
|| H rho'(c) - rho'(h c h^-1) H ||_2  <=  epsilon        (c in S_0).      (UD1)
```

Then

```text
b_p . (1 - nu_0)  <=  12 D epsilon / kappa_0.                            (UD2)
```

The orthogonality sharpening gives the stronger estimate, under the
Kazhdan-constant normalization of the proof route,

```text
b_p . (1 - nu_0)  <=  D epsilon^2 / kappa_0^2.                           (UD2-square)
```

**Reading.**  A near-genuine microstate of `SL_3(Z[1/p])` whose
`SL_3(Z)`-part has congruence level `p^D m'` carries weight at most
`D epsilon^2/(b_p kappa_0^2)` on constituents of positive `p`-level.  So
either the microstate is asymptotically of level coprime to `p` -- the sector
closed by `odd-congruence-lambda-exact-sector-collapses` -- or its `p`-adic
depth is at least `b_p kappa_0^2 (1 - nu_0) / epsilon^2`: an **ultra-deep
tower**, deeper than the inverse-square defect.  Thus the `p`-divisible
mass of a near-genuine microstate can survive only at depths beyond
`1/epsilon^2`.  No
contradiction is claimed: ultra-deep towers with such a profile are not
excluded, in line with `fixed-shift-invariance-does-not-force-flat-profile`.
For the pair `(SL_3(Z),
SL_3(Z[1/p]))` the surviving Lambda-exact enemy is therefore confined to
ultra-deep towers; everything shallower is either prime-to-`p` (closed) or of
negligible weight.  Nothing here touches the outlier sector
(`SL_3(Z)`-parts far from every genuine representation).

**Mechanism.**  The Atkin--Lehner-type element `g_k = J h^k` (`J` the
signed Weyl permutation `(1 3)`, `J h J^-1 = h^-1`) normalizes
`C^((k)) = cap_(i<=k) h^-i C h^i` and maps the upper root subgroup
`e_12(x)` to `e_32(+-p^k x)`.  Property (T) of `C_0` turns `H` into an exact
intertwiner `T`.  Because this is the orthogonal Hilbert--Schmidt projection
of `H`, Pythagoras and the contraction-defect identity bound the overlap
deficit for `rho'(J)T^k` by `k epsilon^2/kappa_0^2`.  A constituent of exact
`p`-level `a>=2` has, by Clifford theory over
`Gamma(p^(a-1))/Gamma(p^a) = sl_3(F_p)`, at least `c_p` of its mass
nontrivial on `e_12(p^(a-1)m')`.  At level one, three conjugate
transvection subgroups generating `SL_3(F_p)` give the lower bound `1/3`.
Thus every positive level has at least `b_p` such mass; the twist by `g_D` of such a
constituent is nontrivial on `e_32(+-p^(a-1+D) m') in Gamma(N)`, on which the
whole of `rho'` is trivial, so that twisted mass is absent and counts fully
toward the overlap deficit.  The factor `k` is sharp for powers of one
projected intertwiner, so this does not exclude inverse-square-depth towers.
