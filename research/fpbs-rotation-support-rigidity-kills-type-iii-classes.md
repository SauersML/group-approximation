---
rg: 2
id: fpbs-rotation-support-rigidity-kills-type-iii-classes
kind: claim
title: Pointwise match rigidity for rotation codes is a property of the Borel support, not of the measure, so every nonatomic class carried by the rotation rays is killed, including classes of every Krieger type III_lambda and all their Maharam extensions; for torsion-free hyperbolic groups the limit-set-intersection import is removed and malnormality is weakened to cyclic conjugate intersections
distinct_from:
  fpbs-rotation-boundary-class-refutes-shadow-summability: that proves pointwise match rigidity (Theorem 3) for one type II_infinity class, the Lebesgue-weighted rotation class, and extends it to hyperbolic groups under the imports (M) Kapovich malnormality and (LI) limit-set intersection; this shows the same rigidity holds for every nonatomic measure on the rotation-ray support, realizes every Krieger type III_lambda there, removes (LI) by a pigeonhole argument, and replaces (M) by the weaker (M') that conjugate intersections are cyclic.
  fpbs-dini-boundary-class-diagonal-dissipative: that kills imp actions over classes dominating a Dini measure by a first-moment count, which uses the size of the measure; this kills imp actions over a class of measures that need not be quasi-invariant under anything in particular, using only where the measure lives.
---

**ESTABLISHED (written proof; see `research/fpbs-rotation-support-rigidity-kills-type-iii-classes-proof.md`).
Theorem A is self-contained given the previous rotation claim. Theorem B imports the Dougherty--Jackson--Kechris
classification of hyperfinite Borel relations and the Araki--Woods/Krieger type computations for product measures.
Theorem C is proved for every nonelementary hyperbolic group containing a quasiconvex free subgroup with property
(M'); for torsion-free groups (M') follows from Kapovich's malnormal-subgroup theorem, which is still imported.**

**Why this matters for the flagship.** The previous lane killed the Lebesgue-weighted rotation class as a boundary
class for Bevilacqua--Bowen (BB) certificates, by pointwise match rigidity. It named type III classes as the next
test: rotation codes with cocycle (Anzai/Denjoy) cylinder weights and their Maharam extensions. There a joint return
must also match the Radon--Nikodym coordinate, and it was unclear whether rigidity survives. It does, for a
structural reason: **the rigidity is a property of the Borel set of rotation rays, not of the measure on it.** So the
entire family of classes carried by rotation rays dies at once, whatever the cocycle does.

**Setting.** Notation is as in `fpbs-rotation-boundary-class-refutes-shadow-summability`: irrational `alpha`, the
rotation code `zeta^+ : Omega_0 -> dF`, `F = <a,b>`, the shift `sigma`, the set `B = zeta^+(Omega_0)` of rotation rays.
For a finite Borel measure `rho` on `Omega_0` put `nu_rho = sum_g c_g g_* zeta^+_* rho` (`c_g > 0`, sum 1).

**Theorem A (support rigidity, `Gamma = F_2`).** Let `(Z, mu_Z)` be any imp `F_2`-space with a measurable equivariant
`xi : Z -> dF_2` such that, for every `E` of finite measure, `xi_*(mu_Z|_E)` is nonatomic and carried by `F B`. Then
`F_2` acts totally dissipatively on all of `(Z x Z, mu_Z x mu_Z)` (not only on the crossing part). In particular this
holds whenever `xi_*(mu_Z|_E) << nu_rho` for one nonatomic `rho`. No quasi-invariance, ergodicity or invariance of
`rho` is needed.

**Theorem B (every Krieger type is present and killed).** For every `lambda in [0,1]` there is a nonatomic,
`sigma`-quasi-invariant, ergodic `rho_lambda` on `Omega_0` such that `nu_{rho_lambda}` is an ergodic, nonatomic,
`F_2`-quasi-invariant class of Krieger type `III_lambda`, carried by `F B`. Every Anzai/Denjoy skew-weighted rotation
measure is also a nonatomic measure on `B`. By Theorem A, the Maharam extension of each such class (amenable, by Adams)
and each of its ergodic components, and every imp action over it, has totally dissipative diagonal. None is PDR, so
none is the boundary class of a BB certificate.

**Theorem C (hyperbolic groups, fewer imports).** Let `Gamma` be nonelementary hyperbolic and let `F = <a,b>` be a
quasiconvex free subgroup with
- **(M')** `F ∩ beta F beta^{-1}` is cyclic for every `beta in Gamma \ F`.

Build the rotation code in `F` and let `iota : dF -> Lambda_F` be the boundary embedding. Then Theorem A holds for
`Gamma`, with `F B` replaced by `Gamma iota(B)`. The limit-set intersection property (LI) is no longer used. It is
replaced by a pigeonhole lemma: if `zeta` is not eventually periodic and `gamma iota(zeta) in Lambda_F`, then
`gamma in F`. Malnormal subgroups satisfy (M'). Kapovich's theorem supplies one in every torsion-free nonelementary
hyperbolic group, so the conclusion holds for all of them.

**Calibration.**
- *`F_2` has cost 2.* No certificate may exist, and Theorems A and B remove only candidates.
- *Rational `alpha`.* Rotation rays become periodic, `Bad` acquires positive measure, and the proof fails exactly at the
  Fubini step. It must fail: periodic rays are fixed points.
- *Atomic classes.* Theorem A requires nonatomic pushforwards. An orbit of a loxodromic fixed point is carried by a
  countable set, and there the non-crossing diagonal is conservative. This is correct.

**What dies (exact step), and why the general statement needs the fibre.** The support-only method cannot prove the
general pointwise match rigidity statement. Take a closed surface group with the Lebesgue class on `S^1`. By
Hopf--Tsuji--Sullivan, the diagonal action on `(S^1 x S^1, Leb x Leb)` is conservative. So for every Borel `S` of full
measure, a.e. pair of `S x S` has infinitely many joint returns to `S x S`, and no support-level relation can be
countable-to-one. The Maharam extension of Lebesgue is still dissipative (Dini claim), but only because returns must
match the Radon--Nikodym coordinate. So Theorem A's mechanism is exactly the complement of Theorem B of the Dini claim:
- *support-rigid classes* (rotation type) die with no fibre information;
- *Dini classes* die by the fibre (a first-moment count);
- the general statement needs a mechanism combining the two.

**Named open statement left.** Call an ergodic class `C` on `dGamma` **support-rigid** if some Borel `S` with
`Gamma S` conull for `C` has the property that, for all finite `H` in `Gamma`, the relation
`{(eta, eta') : infinitely many g with g eta, g eta' in H S}` has countable sections on `S x S`. Theorem A shows that
every nonatomic class carried by `Gamma S` is then killed. Open: is every Dini-singular ergodic class of a torsion-free
hyperbolic group either support-rigid or killed through its Radon--Nikodym fibre? A second, more concrete open step is
to remove Kapovich's theorem by proving (M') directly for `F = <a^N, b^N>`, `N` large.
