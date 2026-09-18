---
rg: 2
id: fpbs-dini-singular-boundary-classes-exist-but-one-way-die
kind: claim
title: Every nonelementary hyperbolic group has nonatomic ergodic quasi-invariant boundary classes singular to every Dini measure, so size alone cannot exclude Bevilacqua--Bowen certificates; but every class carried by the orbit of a one-way compact set is shadow-summable, which kills the Schottky-coded Dini-singular classes
distinct_from:
  fpbs-dini-boundary-class-diagonal-dissipative: that proves shadow-summable (in particular Dini) classes are not PDR and leaves open whether Dini-singular classes exist; this constructs Dini-singular classes for every nonelementary hyperbolic group (so the size dichotomy cannot finish the job), and proves a second, size-free shadow-summability criterion (one-way support) that kills them.
  fpbs-hyperbolic-bb-criterion-obstruction: that uses cocycle geometry and pair maps; this uses only the combinatorics of the support of the boundary class under the reversal g -> g^{-1}.
---

**ESTABLISHED (written proof; see `research/fpbs-dini-singular-boundary-classes-exist-but-one-way-die-proof.md`,
calibration scripts `experiments/dini-singular-one-way-2026-09-17/one_way_f2.py` and `paperfold_f2.py`). The free-group case is
self-contained. For a general hyperbolic group, Proposition 3 imports one standard existence fact about loxodromic
elements (Ol'shanskii 1993, Lemma 3.8).**

**Why this matters for the flagship.** For a cocompact `Sp(n,1)` lattice, a Bevilacqua--Bowen (BB) certificate is an
amenable ergodic PDR imp action with infinite nonatomic components. Such an action has a Zimmer boundary map
`xi : Z -> dGamma` (`fpbs-hyperbolic-bb-criterion-obstruction`, item 4). `fpbs-dini-boundary-class-diagonal-dissipative`
proved that the class of `xi_* mu` must be singular to every Dini measure, and asked whether such classes exist. It
also offered a clean way to finish: if every nonatomic ergodic quasi-invariant class dominated a Dini measure, no
hyperbolic group would have a BB certificate.

**That way to finish is dead.** Theorem 1 answers the question: Dini-singular classes exist for every nonelementary
hyperbolic group, including cocompact `Sp(n,1)` lattices, surface groups and `F_2`. So size cannot rule out
certificates.

**The heretical point.** The shadow sum `S(lambda) = sum_g lambda(O_s(g)) lambda(O_s(g^{-1}))` is not a size invariant.
It measures how much the class correlates with its own *reversal* `g -> g^{-1}`. Theorem 2 shows that a class supported
on the orbit of a "one-way" compact set has a convergent shadow sum, however slowly its balls shrink. The Dini-singular
classes of Theorem 1 are one-way (Proposition 3). They are therefore killed by Theorem A of the previous claim, not by
their size.

**Setting.** Notation is as in `fpbs-dini-boundary-class-diagonal-dissipative`. `Gamma` is nonelementary hyperbolic,
`O_s(g)` is the thin shadow, and `d_eps` is a visual metric. `Gamma_s(K) = {g : O_s(g) meets K}` for `K` contained in
`dGamma`.

**Theorem 1 (Dini-singular classes exist).** Let `Gamma` be a nonelementary hyperbolic group. There is a Borel
probability measure `nu` on `dGamma` such that:
- `nu` is `Gamma`-quasi-invariant, ergodic and nonatomic;
- `nu` is singular to every finite Dini measure;
- `nu` is carried by `Gamma K`, where `K = f(2^N)` is a Cantor set coded by positive words in a Schottky pair.

The construction is a Glimm--Effros-type block code:
- `f(x)` is the endpoint of `A_1(x_1) A_2(x_2) ...`, where `A_n(0) = a^{L_n}`, `A_n(1) = b^{L_n}`, `L_n = 4^{n+n_0}`
  and `a`, `b` generate a Schottky free subgroup;
- `nu = sum_g c_g g_* f_*m`, with `m` the fair-coin measure.

Ergodicity uses only the easy direction: tail-equivalent codes give points in one orbit, and the Kolmogorov 0-1 law
applies. Dini-singularity holds because `nu` gives mass at least about `2^{-n}` to the ball of radius
`exp(-kappa (L_1 + ... + L_n))`, and `sum_n 2^{-n} L_n` diverges.

**Theorem 2 (one-way supports are shadow-summable).** Call a compact `K` in `dGamma` **one-way** if, for every
`s >= 0`,

`rho_K(s) = sup{|h| : h in Gamma_s(K), and y h^{-1} in Gamma_s(K) for some |y| <= s} < infinity.`

Let `C` be a quasi-invariant class carried by `Gamma K` for a one-way compact `K`. Then `C` contains a finite measure
`nu` with `S_s(nu) < infinity` for every `s`. Consequently no imp action with boundary map `xi` and
`xi_*(mu|_B) << nu` for all `B` of finite measure is PDR. In particular no BB certificate has its boundary class in `C`.

**Proposition 3 (the coded sets are one-way).**
1. **Free group.** In `F_2 = <a,b>` with its free generators, every compact subset of the set `Lambda_+` of positive
   rays is one-way, with `rho(s) <= 4s + 1`. The script finds `rho(s) = 2s` for `s <= 3`.
2. **General hyperbolic group.** Choose `a`, `b` loxodromic with `E(a) = <a> x E(Gamma)` and
   `E(b) = <b> x E(Gamma)`, and with no nonzero powers conjugate. Such a pair exists by Ol'shanskii 1993, Lemma 3.8.
   Then for suitable Schottky powers and a suitable `n_0`, the set `K = f(2^N)` of Theorem 1 is one-way, with
   `rho_K(s) <= A s + A'`.

**Proposition 4 (the reversal-symmetric candidate dies too; one-wayness is not the invariant).** In `F_2`, consider the
inverse-paperfolding code `U_0 = a`, `U_n = U_{n-1} t_n U_{n-1}^{-1}`, where the `t_n` in `{b, b^{-1}}` are fair coins,
so that `U_n^{-1}` is `U_n` with `t_n` flipped. It gives a nonatomic quasi-invariant class `nu` with these properties:
- `nu` is singular to every Dini measure, since cylinder mass is about `1/length`;
- `nu` is carried by `Gamma K` for a set `K` that is **not** one-way;
- `nu` is nevertheless shadow-summable.

The key is a reversal-match estimate (Lemma 3 of the proof). A match of length `ell` against the reversal, centred at
`m = 2^k o` with `o` odd, has probability at most `(4/ell) min(1, 16/o)`. The two factors come from bits of the partner
ray that the match forces, and from ties the match forces inside the ray itself. Summed over levels, this gives
`sum_m (1/m)(1/o(m)) < infinity`. The script finds that the actual collision levels are `ell + 1 in {4,5,6} * 2^k`.

**Corollary.** For every nonelementary hyperbolic group, the Schottky-coded Dini-singular classes of Theorem 1 cannot
be the boundary class of a BB certificate. In `F_2` the same holds for the paperfolding class of Proposition 4. A BB
certificate needs a nonatomic ergodic quasi-invariant class that is **small**: no finite measure dominating it is
shadow-summable. In particular such a class is singular to every Dini measure, and by Theorem 2 it is not carried by
`Gamma K` for any one-way `K`. By Proposition 4, being two-way is necessary but not sufficient for smallness.

**Calibration.**
- *The nonelementary hypothesis is load-bearing.* For `Gamma = Z`, `K = {+infinity}` is one-way and `delta_{+infinity}`
  is shadow-summable. Theorem A then says only that the (empty) crossing part is dissipative. The PDR conclusion fails
  because `Z` fixes `+infinity`, as it must.
- *Atomic loxodromic classes agree with the previous claim.* For loxodromic `a`, `K = {a^+}` is one-way exactly when no
  `u` in `Gamma` sends `a^+` to `a^-`. If some `u` does, then `y = u^{-1}` gives `y a^{-n} in Gamma_s(K)` for all `n`
  once `s >= |u| + c`, so `rho_K = infinity`. This matches the previous claim: the shadow sum of an atomic class
  diverges exactly when the class charges both fixed points. In a torsion-free hyperbolic group no such `u` exists: `u`
  would normalise the cyclic group `E(a)` by inversion.
- *Free and surface groups.* Their cost exceeds 1, so no class may yield a certificate. Theorems 1--2 and
  Proposition 4 are consistent with this: Theorem 1 creates classes, and Theorem 2 and Proposition 4 remove them.
- *Scripts.*
  - `one_way_f2.py` enumerates all reduced words of length at most 11 in `F_2`. For `s <= 3` it finds `rho(s) = 2s`,
    within the proved bound `4s + 1`. It also prints the divergent Dini lower sums of Theorem 1.
  - `paperfold_f2.py` computes the exact reversal-collision sums `S_s(lambda)` of the paperfolding code for `s <= 3`.
    They stabilise; for example `S_0 = 1.3076...` at depth 1023.

**Named open statement left (collision density).** Is there a cocompact `Sp(n,1)` lattice, or already `F_2` as a test
case, with a nonatomic ergodic quasi-invariant class `nu` such that `S_s(phi nu) = infinity` for every density `phi`
and every large `s`?

Equivalently, the reversal matches `M(i,j,ell)` of pairs of `nu`-typical rays would need non-summable total mass at a
set of levels that no reweighting can thin. Lemma 3 shows why self-similar palindromic codes fail: each match costs
about `1/ell` in forced partner bits, and a further `1/o` in internal ties. A small class must make reversal matches
cheap at a non-summable set of scales.

**Conjecture (heretic's bet).** In a torsion-free hyperbolic group every quasi-invariant class contains a
shadow-summable measure. If so, then by Theorem A of the previous claim no hyperbolic group has a BB certificate. For a
lattice with torsion this would be applied to a torsion-free subgroup of finite index. If some class is small, the sharp
Maharam sum `sum_g a_U(g) a_V(g)` (Remark 3 of the previous proof) is the next test.
