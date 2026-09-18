---
rg: 2
id: fpbs-rotation-boundary-class-refutes-shadow-summability
kind: claim
title: Every nonelementary hyperbolic group, torsion-free or not, has an ergodic nonatomic quasi-invariant boundary class (an irrational-rotation code in a Schottky subgroup) in which no measure is shadow-summable and the sharp Borel--Cantelli return sum diverges; so the torsion-free shadow-summability conjecture is false, yet for F_2 the class still has totally dissipative diagonal by a pointwise match-rigidity argument
distinct_from:
  fpbs-dini-singular-boundary-classes-exist-but-one-way-die: that constructs Dini-singular classes and kills the one-way and paperfolding ones by proving them shadow-summable, and conjectures every class of a torsion-free hyperbolic group is shadow-summable; this refutes that conjecture with a class whose language is closed under inversion, and replaces the first-moment (Borel--Cantelli) kill by a pointwise one.
  fpbs-dini-boundary-class-diagonal-dissipative: that proves Theorem A (shadow-summable implies crossing diagonal dissipative) and names the sharp Maharam sum as the next test; this shows both first-moment sums diverge on an explicit class, so no argument through them can exclude every boundary class.
---

**ESTABLISHED (written proof; see `research/fpbs-rotation-boundary-class-refutes-shadow-summability-proof.md`,
script `experiments/rotation-boundary-class-2026-09-17/rotation_class.py` with output `rotation_class.out`). Theorems 1
and 2 are self-contained for `F_2`; for general `Gamma` they import only the standard Schottky/Morse facts already used
in `fpbs-dini-singular-boundary-classes-exist-but-one-way-die`. Theorem 3 is proved for `F_2`; its extension to a
general hyperbolic group is conditional on two imported facts named below.**

**Why this matters for the flagship.** The Bevilacqua--Bowen (BB) route to fixed price one for a cocompact `Sp(n,1)`
lattice needs an amenable ergodic PDR imp action. Its Zimmer boundary class must be "small": by Theorem A of
`fpbs-dini-boundary-class-diagonal-dissipative`, no measure in the class may be shadow-summable. The previous claim
conjectured that in a torsion-free hyperbolic group *every* quasi-invariant class contains a shadow-summable measure.
That would have excluded BB certificates for every hyperbolic group. **The conjecture is false** (Theorem 1). The sharp
first-moment sum of Remark 3 of that proof also diverges on the same class (Theorem 2). So no Borel--Cantelli
argument can close the route. The class is nevertheless killed for `F_2`, by a pointwise argument (Theorem 3). This
points at the method that has to replace the first moment.

**Setting.** Notation is as in `fpbs-dini-boundary-class-diagonal-dissipative`: thin shadows `O_s(g)` and the shadow
sum `S_s(lambda) = sum_g lambda(O_s(g)) lambda(O_s(g^{-1}))`. In `F_2 = <a,b>` with its tree, `O_0(g)` is the cylinder
`[g]`.

**The rotation code.** Fix an irrational `alpha`. Put `s(x) = +1` on `[0,1/2)` and `s(x) = -1` on `[1/2,1)`. Let
`t_n = a` for odd `n` and `t_n = b` for even `n`. For `(theta, j)` in `Omega = T x Z/2`, the bi-infinite word
`zeta_n(theta, j) = t_{n+j}^{s(theta + n alpha)}` is reduced, since `a`-letters and `b`-letters alternate. Let
`zeta^+(theta, j)` be the ray `zeta_1 zeta_2 ...`, and let `mu` be the law of `zeta^+` under Lebesgue measure times
uniform measure.
- **Inversion identity.** `s(-x) = -s(x)` gives
  `(zeta_1 ... zeta_m(theta, j))^{-1} = zeta_1 ... zeta_m(-theta - (m+1) alpha, j + m + 1)`.
- So the language is closed under `w -> w^{-1}`, and `mu[w^{-1}] = mu[w]` for every word `w`.
- The factor complexity is at most `4m`, and the itinerary map is injective. The measure is nonatomic, with no
  eventually periodic rays.

For a nonelementary hyperbolic `Gamma`, fix a Schottky free subgroup `F = <a,b>` (quasiconvex, via ping-pong). Put
`iota : dF -> dGamma` and `nu = sum_g c_g g_* iota_* mu` (`c_g > 0`, summing to 1). The **rotation class** is the
class of `nu`.

**Theorem 1 (the conjecture is false).** Let `Gamma` be nonelementary hyperbolic. The rotation class is ergodic,
`Gamma`-quasi-invariant and nonatomic. There is `s_0` such that `S_s(lambda) = infinity` for every `s >= s_0` and
every finite measure `lambda` with `lambda >= c iota_*(mu|_A)`, for some `c > 0` and some `A` with `mu(A) > 0`. In
particular:
- no measure in the rotation class is shadow-summable;
- for `F_2` this holds with `s_0 = 0`.

*Mechanism.* Let `C` run over the at most `4m` level-`m` cells. The level-`m` term of `S_0(mu|_A)` is
`sum_C |A ∩ C| |tau_m A ∩ C|`, where `tau_m` is the measure-preserving involution of the inversion identity. By
Cauchy--Schwarz this term is at least `|A ∩ tau_m A|^2 / (4m)`. The quantity `|A ∩ tau_m A|` is a value
`f(-(m+1) alpha)` of a continuous autocorrelation `f` with `int f = |A|^2 > 0`. Weyl equidistribution then puts a
positive density of `m` where `f(-(m+1) alpha) > delta`, and the harmonic sum diverges.

**Theorem 2 (the sharp sum diverges too).** In `F_2` the rotation class contains an `F_2`-invariant sigma-finite
measure `m_infinity`, with `m_infinity|_B = mu` on the set `B` of rotation rays. Take `U = [a] ∪ [a^{-1}]` and
`V = [b] ∪ [b^{-1}]`. For the ergodic, conservative, amenable imp action `(dF_2, m_infinity)`, the sharp
Borel--Cantelli sum `sum_g a_U(g) a_V(g)` diverges, where `a_W(g) = m_infinity(B_W ∩ g^{-1} B_W)`. The expected
number of returns of a pair in `B_U x B_V` is at least `(1/4) sum_{k even} 1/(2k) = infinity`.

**Theorem 3 (but the class is killed pointwise).**
1. For `m_infinity x m_infinity`-a.e. pair of rays, and every finite union `B'` of translates of `B`, the pair returns
   to `B' x B'` only finitely often.
2. The reason is rigidity. Infinitely many reversal (or shift) matches between `zeta^+(theta)` and `zeta^+(theta')`
   at bounded offsets force `theta'` into `theta + Z alpha` or `-theta + Z alpha`. That is a null set.
3. Consequently, for **every** imp `F_2`-action `Z` whose boundary map satisfies `xi_*(mu_Z|_E) << nu` for all `E` of
   finite measure, the diagonal action on `Z x Z` is totally dissipative. So `Z` is not PDR. No BB certificate, even
   hypothetically, has the rotation class as its boundary class.

For a general hyperbolic `Gamma`, the same conclusion holds under two inputs:
- **(M)** `F` can be chosen malnormal. This is imported: Kapovich, *A non-quasiconvexity embedding theorem for hyperbolic
  groups*, 1999, and not verified here.
- **(LI)** The limit-set intersection property `Lambda(H) ∩ Lambda(K) = Lambda(H ∩ K)` holds for quasiconvex `H`, `K`.

**Calibration.**
- *`F_2` has cost > 1*, so no certificate may exist. Theorem 3 agrees. Theorems 1--2 show that the previous criteria
  were not what excluded it for this class.
- *Theorem B of the Dini claim* (Dini implies shadow-summable) forces the rotation class to be Dini-singular. It is:
  cylinder masses are about `1/m`, and the script gives `4m L_m >= 1` for all `m <= 1500`.
- *Periodic calibration.* If `alpha` were rational, the rays would be periodic. The rigidity step of Theorem 3 would then
  fail, and correctly so: periodic rays are fixed points of elements, and the pair set is not null.
- *Script.* `rotation_class.py` checks:
  - the inversion identity (0 failures in 2000 random trials);
  - `4m L_m >= 1` for `m <= 1500`;
  - `sum_{k<=m} L_k` growing like `0.32 log m`;
  - the restricted sum `S_0(mu|_A)` for `A = [0, 0.05) x {0}` growing like `1.5 * 10^{-4} log m`;
  - for 20000 random pairs, match counts that are finite with `count * ||x - y|| <= 1.03`, but with tail
    `P(count >= k)` about `0.55/k`. So each pair has finitely many matches while the expected number diverges. This is
    Theorems 2 and 3 side by side.

**What dies (exact step).** Take the attack "two reversal matches at nearby scales force periodicity, and torsion-free
groups have no periodic reversible axes, so matches are lacunary". It dies at *lacunary*.
- Two matches at lengths `m < m' < 2m` force only a *local* period `m' - m` of the prefix of length `m'`.
- Rotation words have local periods (continuants of `alpha`) at every scale.
- Matches occur at every scale `k` with probability about `1/k`, which is not summable.
The same class kills every first-moment criterion: the shadow sum under any reweighting, and the sharp Maharam/return
sum.

**Named open statement left (pointwise match rigidity).** Let `Z` be an ergodic imp action of a torsion-free
hyperbolic group with boundary map `xi`. Must `mu x mu`-a.e. crossing pair `(z, z')` have only finitely many `g` with
`g(z, z')` in a fixed product set `B_U x B_V`?

The route is not to bound the expectation. It is to show that infinitely many joint returns force an algebraic
relation between `xi(z)` and `xi(z')`, as `theta' in -theta + Z alpha` does here. The first test objects are classes
with no invariant sigma-finite measure (type III). Examples are rotation codes whose cylinder weights follow a
nontrivial cocycle (Anzai/Denjoy-type skew weights), and their Maharam extensions. There, returns can use the
Radon--Nikodym direction and Theorem 3's rigidity argument has to be redone.
