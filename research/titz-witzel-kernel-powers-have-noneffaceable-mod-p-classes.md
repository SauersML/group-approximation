---
rg: 2
id: titz-witzel-kernel-powers-have-noneffaceable-mod-p-classes
kind: claim
title: Powers of the simple Titz Mite–Witzel kernel are torsion-free CAT(0) Kazhdan groups of type F with non-effaceable mod-p classes in every even degree, so no profinite-blind rigidity input proves effacement
distinct_from:
  every-hyperbolic-group-is-good: that is the open goodness assertion for hyperbolic groups; this is a proved calibration showing which inputs any proof of it must use, on explicit non-hyperbolic, non-residually-finite groups
  kazhdan-degree-two-goodness-iff-profinite-measurable-lifts: that is an exact degree-two dictionary for residually finite Kazhdan groups via measurable lifts; this is a finite-dimensional-representation dictionary for any finitely generated group, plus explicit groups on which every non-profinite input holds and effacement fails
  good-cocompact-proper-groups-are-virtually-torsion-free: that derives virtual torsion-freeness from goodness; this exhibits torsion-free groups with every classical rigidity property that are not good
  sp21-finite-congruence-kernel-forbids-p-goodness: that shows failure of p-goodness for a residually finite arithmetic group via its congruence kernel; these groups have trivial profinite completion and fail in every even degree
---

**ESTABLISHED** (route `titz-witzel-kernel-powers-noneffaceable-proof`; the only
import is `titz-witzel-simple-kazhdan-cat0-lattices-exist`).

A class `x in H^q(G;A)` is *effaceable* if it restricts to zero on some subgroup of
finite index. This is the notion used by `every-hyperbolic-group-good-via-rf-and-high-degrees`.

**Setting.** `Γ = π_1(Y_1^2)` is the Titz Mite–Witzel lattice of thickness 3,
acting freely and cocompactly on the exotic `C~_2` building `X = X_1^2`.
`K <= Γ` is its finite residual, of finite index `d` and simple.

**Statement.**

1. **(Cohomology.)** `H_1(K;Z) = 0`, and `H_2(K;Z) ≅ Z^b` with
   `b = d·|Y^(0)| - 1 >= 1`. Hence `H^2(K;F_p) ≅ F_p^b ≠ 0` for every prime `p`.
   For the recorded complex with 7 vertices, `b = 7d - 1`.
2. **(Powers.)** For every `m >= 1`, `K^m` has these properties:
   - it is finitely presented, torsion-free and of type `F`;
   - it acts freely and cocompactly on the CAT(0) complex `X^m`;
   - it has property (T);
   - it has no proper subgroup of finite index, so its profinite completion is trivial;
   - `H^q(K^m;F_p)` vanishes for odd `q`, while `H^(2m)(K^m;F_p) ≅ F_p^(b^m) ≠ 0`.

   Consequently no nonzero class of `H^(2j)(K^m;F_p)`, for `1 <= j <= m`, is
   effaceable, and `K^m` is not good.
3. **(Degree-two dictionary, any finitely generated `G`.)** Let `x in H^2(G;F_p)`
   have trivial action and classify `1 -> Z/p -> E -> G -> 1`. Let `c` be a
   normalised cocycle for `x`, and `χ: Z/p -> T` a faithful character. Then the
   following are equivalent:
   - (i) `x` is effaceable;
   - (ii) some finite quotient of `E` is injective on `Z/p`;
   - (iii) the twisted group C*-algebra `C*(G, χ∘c)` has a nonzero
     finite-dimensional representation.

   In particular, for every nonzero `x in H^2(K;F_p)`, the algebra `C*(K, χ∘c)`
   has no finite-dimensional representation.
4. **(Calibration.)** Let `P` be any property of groups that holds for `K^m`.
   Then "`P(G)` implies that every class of `H^(2m)(G;F_p)` is effaceable" is
   false. This covers property (T) together with a free cocompact CAT(0) action
   and type `F`, and every consequence of these. Examples of such consequences:
   - Kazhdan projections;
   - vanishing of `H^1(G;π)` for unitary `π`;
   - `w`-rigidity of Bernoulli actions;
   - vanishing of `b_1^(2)`.

## What this kills, and what survives

* **Killed.** Every argument for `every-hyperbolic-group-is-good` in which the
  only inputs are rigidity or finiteness properties shared by `K^m`. Such an
  argument dies at the step "conclude that the class restricts to zero on a
  finite-index subgroup". In degree two, by item 3, that step must produce a
  finite-dimensional projective representation with the given multiplier. The
  step is killed in every even degree.
* **Not killed.**
  - Odd degrees. The odd cohomology of `K^m` vanishes.
  - Arguments that use residual finiteness, as Lemma B of the route does, or
    hyperbolicity. `K` is not residually finite. `K` is not hyperbolic, because
    `X` contains flat planes and `K` acts on it cocompactly.
* **The operator-algebraic avatar of hyperbolicity** is bi-exactness (Ozawa's
  class S). It is the one gate this calibration does not decide. For `m >= 2`,
  `K^m ⊇ K × K` is not bi-exact, since it contains the product of an infinite
  group with a non-amenable one. So only `K` itself could decide the gate.
  **Open test:** is `K` bi-exact? If it is, then (T) together with
  bi-exactness, CAT(0) and type `F` does not imply degree-two effacement.
