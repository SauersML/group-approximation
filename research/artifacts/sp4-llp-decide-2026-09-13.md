# Deciding LLP for `C^*(Sp_4(Z))`: calibration and obstruction audit (2026-09-13)

Target: `sp2g-z-full-c-star-algebra-has-llp` at `g = 2`.

Sources read locally from PDFs fetched on MSI this date (page numbers are
the printed page numbers, checked against the form-feed count):

- [ISW] A. Ioana, P. Spaas, M. Wiersma, *Cohomological obstructions to
  lifting properties for full C*-algebras of property (T) groups*,
  arXiv:2006.01874.
- [FFW] F. Fournier-Facio, R. Willett, arXiv:2603.18456v2.

## 0. Calibration: `F_2 x F_2 <= Sp_4(Z)`

**Embedding.**  Write `Z^4` with symplectic basis `e_1, f_1, e_2, f_2`.
The hyperbolic planes `<e_1,f_1>` and `<e_2,f_2>` are orthogonal for the
form, and on each plane `Sp_2(Z) = SL_2(Z)`.  Block-diagonal matrices give

```text
SL_2(Z) x SL_2(Z) <= Sp_4(Z).                               (CAL1)
```

The Sanov matrices `[[1,2],[0,1]]` and `[[1,0],[2,1]]` generate a free
subgroup of rank two (of finite index) in `SL_2(Z)`, so

```text
F_2 x F_2 <= Sp_4(Z).                                       (CAL2)
```

**Permanence.**  [ISW] Remark 1.2 (p. 4): for countable `Sigma < Gamma`,
"if `C*(Gamma)` has the LP (respectively, the LLP), then so does
`C*(Sigma)`".  The same statement is [FFW] Corollary 3.17 (p. 17): "The LP
and LLP both pass to subgroups."  Hence

```text
C*(Sp_4(Z)) has LLP  ==>  C*(F_2 x F_2) has LLP.            (CAL3)
```

**Status of `F_2 x F_2`.**  [FFW] p. 6: "In another direction, the
following seems to be a particularly challenging group for which the (L)LP
is open.  Question 1.6.  Does `F_2 x F_2` have the (L)LP?"  And p. 18: "It
seems to be open whether the (L)LP is preserved under direct products.  For
example, it is open whether `F_2 x F_2` has the (L)LP (Question 1.6); this
problem is generally considered difficult, see for example the discussion
at the end of [155, Section 3]."  (I did not read [155] itself.)

**A second open question sits on the same side.**  `Sp_4(Z)` has property
(T): it is a lattice in `Sp_4(R)`, which [ISW] Example 1.3(i) (p. 4) lists
among the simple Lie groups with property (T).  [FFW] p. 6: "Question 1.9.
Is there an example of an infinite property (T) group (or just a group with
property (T) relative to an infinite subgroup) with the (L)LP?"  [FFW]
Remark 3.8 (p. 15): "We do not know an example of a group with the LLP that
has property (T), or even property (T) with respect to an infinite subgroup
(Question 1.9)."

**CALIBRATION OUTCOME.**

1. `C*(F_2 x F_2)` is NOT known to fail LLP.  The calibration does not
   refute the target.
2. A positive answer for `Sp_4(Z)` would answer three questions at once:
   - the LLP half of [FFW] Question 1.6, positively, by (CAL3).  [FFW] call
     this "generally considered difficult".
   - the LLP half of [FFW] Question 1.9, positively.
   - and it would produce a finitely presented nonhyperlinear group, by the
     established dichotomy `sp4-llp-failure-or-maslov-nonhyperlinear-extension`.
   The target node already records a fourth consequence: LLP without LP.
3. So the positive side is at least as hard as an open problem that [FFW]
   single out as difficult.  This lane works on the refutation side
   (sections 1-2); section 4 only records what the positive side would
   need.

**Other subgroups with known LLP failure.**

- [ISW] Corollary B (p. 2): "Let `Gamma = Z^2 rtimes Sigma`, where
  `Sigma < SL_2(Z)` is a non-amenable subgroup.  Then `C*(Gamma)` does not
  have the LLP.  Thus, `C*(Z^2 rtimes SL_2(Z))` and `C*(SL_n(Z))` do not
  have the LLP, for any `n >= 3`."
  - Every non-amenable `Sigma < SL_2(Z)` contains a free group `F`.  The
    established `sp4-contains-no-isw-affine-subgroup` excludes
    `Z^2 rtimes F` from every subgroup of `Sp_4(Z)`, not only the
    parabolics.
  - The Corollary B family, in the form quoted above, is therefore absent.
    Its ring generalisation (same page, "More generally, if R is ...")
    contains `Z^2 rtimes SL_2(Z)` whenever the ring contains `Z`.  Positive
    characteristic rings give infinite torsion abelian subgroups, which
    `GL_4(Z)` cannot contain.
  - `SL_3(Z)` does not embed in `Sp_4(Z)` (the superrigidity bullet on the
    target node).
- [ISW] Theorem A (p. 2), scalar cocycles realized by finite-dimensional
  projective representations: no data on `Sp_4(Z)` or on any finite-index
  subgroup (`isw-theorem-a-has-no-data-on-sp4-finite-index-subgroups`).  On
  the maximal parabolics the scalar obstruction dies on the radicals
  (`isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals`).
- [ISW] Corollaries D and E (p. 4) and Theorem G (p. 5) conclude only
  "does not have the LP".
- [FFW] Remark 3.8 (p. 15) also cites the Buss--Echterhoff--Willett examples
  built from Osajda's groups whose Cayley graphs contain expanders.  For
  Osajda's non-exact a-T-menable groups, failure of the (L)LP is only
  "plausible", not known.
  - Groups containing expanders in this way are not exact.  Every subgroup
    of the linear group `Sp_4(Z)` is exact (Guentner--Higson--Weinberger;
    not source-read here, no locator claimed).  So neither family occurs.
  - [FFW] Remark 3.8 also cites Ozawa [156, Corollary 5] and Thom
    [183, p. 198].  I did not read those sources and record no subgroup
    check for them.

Conclusion of section 0: no subgroup of `Sp_4(Z)` is currently known to
fail LLP.  The refutation side needs a mechanism at `Sp_4(Z)` itself or at a
subgroup with no recorded fence.

## 1. ISW Theorem C at the trivial coefficient algebra `A = C1`

[ISW] Theorem 4.3 (pp. 17-18): "Let `Gamma` be a countable group and
`Lambda` a subgroup such that `(Gamma, Lambda)` has relative property (T).
Assume that there is a trace preserving action `Gamma ~>_sigma (A, tau)` on
an abelian tracial von Neumann algebra `(A, tau)` such that `sigma|Lambda`
is ergodic, and 2-cocycles `c_n in Z^2(Gamma, U(A))` such that the
restriction of `c_n` to `Lambda` is not a 2-coboundary, for every `n`, and
`lim ||c_n(g,h) - 1||_{2,tau} = 0`, for every `g, h`.  Then `C*(Gamma)` does
not have the LP.  Moreover, if the twisted crossed product von Neumann
algebra `A x|_{sigma,c_n} Gamma` embeds into `R^omega`, for every `n`, then
`C*(Gamma)` does not have the LLP."  Theorem C (p. 3) is the case
`A = L^infty(X)`.

Take `A = C1`, `Lambda = Gamma = Sp_4(Z)`, trivial action.

| hypothesis | status at `A = C1` |
|---|---|
| relative (T) for `(Gamma, Gamma)` | holds: this is property (T) ([ISW] p. 2), and `Sp_4(Z)` has it (section 0) |
| `sigma|Lambda` ergodic | holds: the fixed-point algebra of `C1` is `C1` |
| `c_n in Z^2(Gamma, T)` with `c_n` not a coboundary and `c_n -> 1` pointwise | holds, see (TCA1) below |
| moreover clause: `C x|_{c_n} Gamma = L_{c_n}(Gamma)` embeds in `R^omega` | exactly `sp4-small-maslov-twisted-group-factors-are-ce` (SMT1) |

**(TCA1).**
- [ISW] Lemma 6.4 (p. 21): "Let `G` be a simple Lie group with an infinite
  cyclic fundamental group and with property (T).  If `Gamma` is a lattice
  in `G`, then `H^2(Gamma, R) != {0}`."  Its proof produces an integral
  cocycle `c` that is not in `B^2(Gamma, R)`.
- [ISW] Corollary 6.2 (p. 20): with `c_r = exp(irc)`, "Assume that
  `c_r in B^2(Gamma, T)`, for every `r in R`.  Then `c in B^2(Gamma, R)`."
- So `{r : c_r in B^2(Gamma,T)}` is a proper subgroup of `R` and contains
  no interval `(-eps, eps)`.  This gives `r_n -> 0` with `c_{r_n}` not a
  coboundary.  And `c_{r_n}(g,h) -> 1` for every `g, h`.

**No other scalar null family.**
- `H^2(Gamma, T) = Hom(H_2(Gamma), T)`: the Ext term vanishes, [FFW]
  p. 25 display.
- `H_2(Sp_4(Z))` has rank one (`sp4-fd-projective-multiplier-is-finite`).
  So the identity component of `H^2(Gamma,T)` is the Maslov circle.
- Pointwise convergence of cocycles gives convergence of classes (evaluate
  on 2-cycles).  So any admissible `c_n` is eventually cohomologous to a
  nontrivial `c_{theta_n}` with `theta_n -> 0`.  Connes embeddability
  depends only on the class.
- Together with `maslov-ce-parameter-set-is-a-closed-subgroup` (MCS1), the
  scalar instance applies iff `E_CE = R/Z`, iff SMT1.

**The CE toll cannot be dropped inside this proof.**  [ISW] p. 18, proof of
Theorem 4.3: "Assuming by contradiction that the conclusion fails,
Corollary 1.7 implies the existence of u.c.p. maps `psi_n : C*(Gamma) ->
M_n`".  [ISW] Corollary 1.7 (p. 6) needs "`C*(Gamma)` has the LLP and `M_n`
embeds into `R^omega`, for every `n`, or `C*(Gamma)` has the LP".

**New reduction.**  Theorem 4.3 allows any abelian tracial `A`, including
`A = C1`.  So SMT1 alone supplies a Theorem 4.3 packet refuting LLP, with no
Bernoulli injection and no twisted Bernoulli CE equivalence.  No separate
route is landed for this: `sp4-theorem-c-reduces-to-small-maslov-twisted-group-factors`
already makes TC1 follow from SMT1 through two established nodes.

## 2. Other obstructions

- **[ISW] Theorem G (p. 5).**  "If `Gamma` is a non-finitely presented
  countable group with property (T), then `C*(Gamma)` does not have the LP."
  `Sp_4(Z)` is finitely presented, and the conclusion is LP only; LP failure
  is already known.  Corollary D (p. 4) is also LP only, and its
  `ZGamma`-feed is at most bounded torsion at `Sp_4(Z)` (TC1 Attempts,
  duality).
- **[FFW] Corollary 3.36 (p. 24) and Example 3.37 (p. 25).**  Both move LLP
  UPWARD, from the twisted algebras `C*(Lambda; sigma_omega)` to a central
  extension `Gamma` of `Lambda`.
  - Read contrapositively at a Deligne cover `Gamma`, they yield failure of
    some TWISTED `C*(Sp_4(Z); c_theta)`, never of `C*(Sp_4(Z))`.
  - Example 3.37 needs the extension to be "pointwise trivial": "for each
    `omega in K^`, ... `[sigma_omega] = 0` in `H^2(Lambda, S^1)`".  For the
    integral Deligne extension the `sigma_omega` are the Maslov classes,
    which are nontrivial off a finite subgroup.  Its special case
    "`H^2(Lambda; S^1) = 0 <=> H_2(Lambda) = 0`" fails because `H_2` has
    rank one.
  - [FFW] p. 24 on deducing the twisted hypothesis from the untwisted one:
    "we were unable to do that (Question 1.12)".
  - Blocked in both directions.
- **Relative versions with ambient `Gamma = Sp_4(Z)`.**  Shrinking `Lambda`
  only strengthens the non-coboundary and ergodicity requirements.
  Relative (T) is automatic because `Gamma` is Kazhdan.  The CE toll is
  about `A x| Gamma` and does not depend on `Lambda`.  So `Lambda = Gamma` is
  optimal, and section 1 covers every Siegel or Klingen choice of `Lambda`.
- **Relative versions with ambient `Gamma = P_S` or `P_K`.**  If a parabolic
  fails LLP, so does `Sp_4(Z)`.
  - Scalar data on the radical pairs is dead by
    `isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals` (ISC1):
    the restricted classes lie in a finite set, so a null sequence is
    eventually trivial there.
  - Operator-valued data (non-constant measurable cocycles, ergodic on the
    radical) is uncharted: no candidate is recorded, and none was found
    here.

## 3. Finite-index scalar data is a hyperlinearity statement

Landed as the claim `sp4-finite-index-scalar-data-iff-hyperlinear-covers`
with proof route `sp4-finite-index-scalar-data-hyperlinear-covers-proof`,
which also adds (FLA1) below.

Let `Gamma' <= Sp_4(Z)` have finite index.  Scalar Theorem 4.3 data on
`(Gamma', Gamma')` refutes the target, because LLP passes to subgroups.

For `x in H^2(Gamma', Z)`, let `E_x` be the central extension by `Z` and
`E_x^(n) = E_x / nZ`.  Write `E_CE(Gamma')` for the set of classes
`omega in H^2(Gamma', T)` with `L_omega(Gamma')` Connes embeddable.

**THEOREM (FIC1).**  The following are equivalent.

1. There are `c_n in Z^2(Gamma', T)`, not coboundaries, with `c_n -> 1`
   pointwise and every `L_{c_n}(Gamma')` Connes embeddable.
2. `E_CE(Gamma')` is a closed subgroup of positive dimension.
3. Some infinite-order `x in H^2(Gamma', Z)` has `E_x^(n)` hyperlinear for
   every `n >= 1`.

Moreover, for every infinite-order `x`:
- (FIC2) only finitely many `E_x^(n)` are residually amenable;
- 3 implies that `E_x` is hyperlinear.

If `b_2(Gamma') = 1`, then 1-3 at `Gamma'` are equivalent to SMT1 (FIC3).

**Proof.**

- **Topology.**  `H^2(Gamma',T) = Z^2/B^2` is compact and metrizable.
  `B^2 = d(T^Gamma')` is closed by Tychonoff.  The continuous bijection
  onto `Hom(H_2(Gamma'), T)` is a homeomorphism.  `H_2(Gamma')` is finitely
  generated, so this is a compact abelian Lie group whose identity component
  is a torus of dimension `b_2(Gamma')`.
- **`E_CE(Gamma')` is a closed subgroup.**
  - Products: `u_g -> u_g (x) v_g` embeds `L_{omega eta}` trace-preservingly
    in `L_omega (x) L_eta`.
  - Inverses: `L_{omega-bar}` is the complex conjugate algebra.
  - Unit: `L(Gamma')` is CE because `Gamma'` is residually finite.
  - Closedness: the quotient map is open between metrizable spaces, so
    `omega_k -> omega` lifts to cocycles `c_k -> c` pointwise.  Then
    `u_g -> (u_g^(k))_k` embeds `L_c(Gamma')` in the ultraproduct of the
    `L_{c_k}(Gamma')`.
- **1 => 2.**  The classes are nontrivial and tend to `0` (evaluate on
  2-cycles).  A closed subgroup with non-isolated identity has positive
  dimension.
- **2 => 3.**  The identity component of `E_CE(Gamma')` is a nontrivial
  torus, so it contains a circle `t -> t.v` with
  `0 != v in Hom(H_2(Gamma'), Z)`.  Lift `v` to `x in H^2(Gamma', Z)`
  (universal coefficients); `x` has infinite order.  The central Fourier
  decomposition gives
  `L(E_x^(n)) = direct_sum_(j<n) L_{e(jx/n)}(Gamma')`, as in `(FDC2)`.  So
  every `E_x^(n)` is hyperlinear.
- **3 => 1.**
  - `t -> [e(tx)]` has finite kernel `(1/d)Z/Z`, where `dZ` is the image of
    the pairing `<x, H_2(Gamma')>`.
  - For large primes `p`, `c_p = e(x/p)` is not a coboundary, `c_p -> 1`
    pointwise, and `L_{c_p}(Gamma')` is a summand of `L(E_x^(p))`.
- **`E_x` hyperlinear.**  Along primes, the traces of `E_x -> E_x^(p)`
  converge to the regular trace.
- **(FIC2).**
  - `E_x^(n)` has (T), so residual amenability forces residual finiteness.
  - If `E_x^(n)` is residually finite, some finite quotient is injective on
    the centre.  An irreducible summand of its regular representation with a
    generating central character `chi_j` (`gcd(j,n) = 1`) makes `[e(jx/n)]`
    realizable in finite dimensions.
  - The realizable set `R(Gamma')` is finite
    (`sp4-finite-index-fd-projective-multiplier-is-finite`), while
    `[e(jx/n)]` has order `n/gcd(n,d)`, which is unbounded in `n`.
- **(FIC3).**  Restriction is injective on real classes, so it maps the
  Maslov circle onto the one-dimensional identity component.  Finite-index
  induction gives a trace-preserving embedding
  `L_c(Gamma) <= M_m(L_{c|Gamma'}(Gamma'))`.  So `L_{c_theta}(Gamma)` is CE
  iff its restriction is.  With MCS1 this is SMT1.  QED.

**Reading.**
- At level one, and at every `Gamma'` with `b_2 = 1`, this is SMT1 again.
- A genuinely new scalar mouth needs `b_2(Gamma') >= 2`, with a new circle
  all of whose finite covers are hyperlinear.  I did not compute `b_2` of
  congruence subgroups.
- Every such cover family is far from residually amenable (FIC2).  So even
  the refutation side at finite index asks for hyperlinearity of infinitely
  many finitely presented Kazhdan groups that are not residually amenable.

## 3a. Finite transitive actions add nothing (FLA1)

Let `Gamma' <= Gamma = Sp_4(Z)` have index `m` and `A = l^infty(Gamma/Gamma')`
with translation action and uniform trace; it is ergodic because the action
is transitive.

- Suppose `c_n in Z^2(Gamma, U(A))` are non-coboundaries with
  `||c_n(g,h) - 1||_2 -> 0`, and every `A x|_(c_n) Gamma` is CE.  Evaluating
  at the base coset gives `c_n' in Z^2(Gamma',T)` with `c_n' -> 1` pointwise.
- `U(A)` is the coinduced module, and the Eckmann--Shapiro isomorphism
  `H^2(Gamma,U(A)) = H^2(Gamma',T)` is exactly `[c] -> [c']`.  So `c_n'` is not a
  coboundary.
- The corner at `p = 1_(Gamma')` is `L_(c_n')(Gamma')`, trace-preservingly, so
  it is CE.

So condition 1 of (FIC1) holds at `Gamma'`.  Theorem 4.3 over finite atomic
ergodic actions reduces to scalar data on finite-index subgroups; only
non-atomic actions (profinite, Bernoulli, Gaussian) with non-constant
cocycles remain outside (FIC1).  Full proof: step 8 of
`sp4-finite-index-scalar-data-hyperlinear-covers-proof`.

## 4. What LLP for `C*(Sp_4(Z))` would need

1. Positive answers to the LLP halves of [FFW] Questions 1.6 and 1.9
   (section 0).
2. `E_CE` finite (section 1 plus MCS1).  So `E_q` is nonhyperlinear for every
   prime `q` not dividing `|E_CE|`: a finitely presented nonhyperlinear
   group (`sp4-llp-failure-or-maslov-nonhyperlinear-extension`).
3. For every finite-index `Gamma'` and infinite-order `x`, some `E_x^(n)`
   nonhyperlinear (FIC1).
4. For every ergodic abelian `(A, tau)` and every null non-coboundary
   `c_n in Z^2(Sp_4(Z), U(A))`, some `A x|_{c_n} Sp_4(Z)` not CE: the
   negation of TC1.  The same holds on every subgroup carrying
   relative-(T) data, including the parabolic radical pairs.
5. Weak ucp-stability of `Sp_4(Z)`, already recorded on the target
   (`llp-implies-weak-ucp-stability`).

Outcome: neither side is decided.  Every known obstruction reduces to a
Connes-embeddability or hyperlinearity toll (SMT1, FIC1, TC1).  Every
positive route passes through [FFW] Question 1.6 and a nonhyperlinear
group.
