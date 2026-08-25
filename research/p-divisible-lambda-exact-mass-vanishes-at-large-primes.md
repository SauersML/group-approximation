---
rg: 2
id: p-divisible-lambda-exact-mass-vanishes-at-large-primes
kind: claim
title: At large primes the p-divisible weight of a near-genuine microstate of the SL3 pair vanishes with the defect, independently of depth
distinct_from:
  lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible: that bounds the p-divisible weight by depth times defect and leaves ultra-deep towers alive; this bounds it by the defect alone, with no depth, once the Clifford constant exceeds 3/4, and so empties the whole p-divisible sector at primes p >= 11.
  odd-congruence-lambda-exact-sector-collapses: that closes the coprime-level sector using the exact slot for h; this shows that at large primes every near-genuine microstate is asymptotically of coprime level, so that sector is the whole Lambda-exact face.
  homogeneous-quotient-near-genuine-microstates-are-deep: that forces microstates of the homogeneous-quotient crossed product to be p-adically deep; combined with this theorem it shows that algebra has no near-genuine microstates at all for p >= 11.
---

**THEOREM (established here; proof in
`p-divisible-mass-vanishes-depth-free-proof`).**  Notation of
`lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible`: `C = SL_3(Z)`,
`h = diag(p,1,1/p)`, `C_0 = C cap h^-1 C h` with Kazhdan constant `kappa_0`,
`rho'` a genuine representation of `C` of level `p^D m'`, `nu_0` the weight
of its trivial-`p`-part, `H` a unitary with `h`-twist defect at most
`epsilon` on the generators of `C_0`, and

```text
c_p = 1 - (p^2 + p - 2)/(p^3 - 1) - 1/(p + 1).
```

Then, for every prime `p` and every depth `D`,

```text
(4 c_p - 3) (1 - nu_0)  <=  12 epsilon / kappa_0.                        (PV1)
```

Since `c_p > 3/4` for `p >= 11` (`c_11 ~ 0.819`, `c_13 ~ 0.842`,
`c_p -> 1`), at those primes the `p`-divisible weight of any near-genuine
microstate is at most `12 epsilon/((4 c_p - 3) kappa_0)`, **whatever its
depth**.

**Mechanism.**  Give every irreducible constituent `sigma` of `rho'|_(C_0)` an
upper depth `beta(sigma)` (least `b >= 0` with `sigma` trivial on
`e_12(p^b m')` and `e_23(p^b m')`) and a lower depth `gamma(sigma)` (least
`g >= 1` with `sigma` trivial on `e_21(p^g m')` and `e_32(p^g m')`; these lie
in `C_0` for `g >= 1`).  The twist `sigma |-> sigma o Ad(g)^-1`, `g = J h`,
acts on types by

```text
(beta, gamma)  |->  (gamma - 1, beta + 1),                               (PV2)
```

because `Ad(g)` carries `e_12(x), e_23(x)` to `e_32(+-px), e_21(+-px)` and
`e_21(x), e_32(x)` to `e_23(+-x/p), e_12(+-x/p)`.  So the twist sends every
diagonal type `(a, a)` to the off-diagonal type `(a-1, a+1)`.  On the other
hand a level-`a` irreducible of `C` has at least `c_p` of its restricted mass
at upper depth exactly `a` and, by Weyl symmetry, at least `c_p` at lower
depth exactly `a`, hence at least `2 c_p - 1` on the diagonal and at most
`2(1 - c_p)` off it.  The level-`0` part is twist-invariant.  Comparing the
off-diagonal masses of the weight measure and its twist gives
`TV >= (4 c_p - 3)(1 - nu_0)`, while one Kazhdan projection gives
`TV <= 12 epsilon/kappa_0`.

**Consequences.**
- For `p >= 11` the `p`-divisible `Lambda`-exact sector of the collapse for
  the pair `(SL_3(Z), SL_3(Z[1/p]))` is empty in the limit: ultra-deep towers
  are excluded along with everything shallower.  Together with the closure
  of the coprime sector (`odd-congruence-lambda-exact-sector-collapses`),
  the entire `Lambda`-exact face of the collapse at `p >= 11` reduces to
  microstates that are prime-to-`p` up to weight `O(epsilon)`; what remains
  to close the face is a robust form of the coprime theorem tolerating that
  admixture (`coprime-sector-collapse-is-robust-to-small-p-admixture`), and
  what remains beyond the face is the outlier sector
  (`sl3-z-weakly-ucp-stable`).  See
  `sl3-large-prime-pair-relative-commutant-collapse`.
- For `p >= 11` the homogeneous-quotient crossed product
  `L^infinity(SL_3(Q_p)/Lambda') rtimes SL_3(Z[1/p])` has **no** microstates
  whose `SL_3(Z)`-part is near a genuine representation: its cell structure
  forces `nu_0 -> 0` (`homogeneous-quotient-near-genuine-microstates-are-deep`,
  `(DT2)` at `j = 0`), while `(PV1)` forces `nu_0 -> 1`.  Any Connes
  embedding of that algebra at such primes must be built from outliers.
- Nothing is claimed at `p <= 7`, where `c_p <= 3/4`; there the ultra-deep
  bound is the only one.  Sharper Clifford constants (the true maximal fixed
  fraction of a level-`(a-1)` root subgroup in a level-`a` irreducible of
  `SL_3(Z/p^a)`, about `2/p`) would lower the threshold to `p >= 11` again,
  so the prime `11` is where the crude and the sharp counts agree.
