# Near-minimal defects are independent of the cylinder commutant, and conjugation data cannot force a deficit

Lane `w4-sub-weyl`, 2026-09-12, family SUB (lead `w3-strategist-gate`, verifier `w4-vf-gate`).
Target: `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`. Supports
`near-minimal-defects-are-rank-independent-of-cylinder-commutants` and the Attempts entries on the
target. Notation and Facts 1.1–1.3, Lemma 3.0 and the constant `c_*` are those of
`research/artifacts/two-root-defect-descent-gap-2026-09-12.md`.

## 0. Summary

* **Section 2 (established): commutant independence.** Let `sigma` be a nontrivial fixed-point-free
  characteristic-two rank model of `R^x` with `delta = rk(D_1000) <= (1+eps) c_*`. Let `A` be a proper
  cylinder and `X` any element of `M` commuting with `sigma(iota_A(R^x))`. Then for every proper
  prefix `P`,

  ```text
  | rk(D_(AP) X) - delta · rk(X) |  <=  eps delta .
  ```

  So a near-minimal defect behaves like an independent tensor factor against the whole commutant of
  its cylinder group, not only against other defects. Proposition 4.1 of the descent artifact is the
  case where `X` is a product of disjoint defects. The complement clopen set carries a whole
  fixed-point-free model of `R^x` inside that commutant.
* **Section 3 (established): the Weyl and torus angle is blocked at the level of finite-subgroup
  data.** The regular rank assignment on the group algebras of all finite subgroups of `R^x` is
  consistent, invariant under conjugation by every unit, and satisfies every relation inside finite
  subgroups. On it `rk(D_A) = 3/8` and `rk(D_A D_B) = rk(D_A) rk(D_B)` exactly. Weyl elements over
  `F_2`, the halving sheets, the prefix doubling, the swap, and conjugation by torus units or
  compressors all live inside this data. So none of them can force `theta < 1` without an input that
  finite-subgroup data cannot see.
* **Section 4: where it stops.** A proof must either use a unit of infinite order as a factor, not
  only as a conjugator, or turn a global input (corner locality, globality, compactness) into an upper
  bound. Commutant independence is the global tool on the lower side; the upper side has no mechanism
  yet.

## 1. Setting

* `R = L_(F_2)(1,2)`, `R^x = EL_3(R)` through the code `(0, 10, 11)`.
* `sigma : R^x -> M^x`, where `M` is a rank ultraproduct over a field of characteristic two, with
  faithful rank `rk`, `rk(1) = 1`. Nonzero corners `eMe` are rank ultraproducts after renormalizing.
* For a proper cylinder `C`: `N^C_ab = sigma(iota_C(x_ab(1))) - 1` and `D_C = N^C_23 N^C_12`.
* `sigma` is fixed-point-free when `Fix_r(sigma(R^x)) = 0`. `c_*` is the infimum of `rk(D_1000)` over
  nontrivial fixed-point-free models, so `c_0 <= c_* <= 1/2`
  (`leavitt-rank-model-defect-gap-on-fixed-point-free-quotients`).
* `iota_A o iota_P = iota_(AP)`, so `D_(AP)` lies in the image of `F_2[iota_A(R^x)]`.
* For a fixed-point-free model and every proper cylinder `C`, `rk(D_C) = delta(sigma)` (Fact 1.2).

## 2. Commutant independence

**Theorem 2.1.** Let `sigma` be a nontrivial fixed-point-free characteristic-two rank model of `R^x`
with `delta = rk(D_1000)`. Let `A` be a proper cylinder, and let `X` in `M` satisfy
`X sigma(iota_A(g)) = sigma(iota_A(g)) X` for every `g` in `R^x`. Then for every proper prefix `P`:

```text
c_* · rk(X)  <=  rk(D_(AP) X)  <=  delta - c_* · (1 - rk(X)) .
```

Consequently:
* if `delta <= (1+eps) c_*`, then `| rk(D_(AP) X) - delta · rk(X) | <= eps delta`;
* if `delta = c_*`, then `rk(D_(AP) X) = delta · rk(X)` exactly.

*Proof.* Put `T = D_(AP)`. It is a polynomial in `sigma(iota_A(iota_P(x_ab(1))))`, so it commutes with
`X`, and it preserves every `sigma(iota_A(R^x))`-invariant right ideal.

1. **Two invariant ideals.** `XM` is invariant, because `sigma(iota_A(g)) XM = X sigma(iota_A(g)) M = XM`.
   The right annihilator `K` of `X` is invariant, because `Xm = 0` gives
   `X sigma(iota_A(g)) m = sigma(iota_A(g)) X m = 0`. Both are principal: `XM = eM`, `K = kM` with `e`, `k`
   idempotent, `rk(e) = rk(X)` and `rk(k) = 1 - rk(X)` (Fact 1.1(a)).
2. **The range corner.** By Lemma 1.1 of the defect-piece artifact, `tau_e(g) = e sigma(iota_A(g)) e`
   is a homomorphism `R^x -> (eMe)^x`.
   * *Fixed-point-free.* If `v` in `eM` is fixed by every `tau_e(g)`, then `sigma(iota_A(g)) v` lies in
     `eM`, so it equals `e sigma(iota_A(g)) v = v`. Hence `v` is fixed by `sigma(iota_A(R^x))`, hence by
     `sigma(R^x)` (Lemma 3.0), hence `v = 0`.
   * *Nontrivial* when `X != 0`, since a trivial model fixes its whole corner.
   * *Its defects.* For a proper prefix `P'`, `tau_e(iota_(P')(x_ab(1))) - e = N^(AP')_ab e`, because
     `N^(AP')_ab` preserves `eM`. So the `P'` defect of `tau_e` is `D_(AP') e`, whose image is
     `D_(AP') X M`. Its rank is `rk(D_(AP') X)`.
   * `tau_e` is a model of `R^x`, so Fact 1.2 inside it makes this rank independent of the proper
     prefix `P'`. The normalized defect is at least `c_*`, so `rk(D_(AP) X) >= c_* rk(X)`.
3. **The kernel corner.** The same argument on `kMk` gives a fixed-point-free model whose defect at
   `P` is `D_(AP) k`. If `k != 0` it is nontrivial, so `rk(D_(AP) k) >= c_* (1 - rk(X))`. If `k = 0`
   the bound is trivial.
4. **Triangular count.** `T` maps `K` into `K`. Put `J = TM + K`, a principal right ideal containing
   `K`. By modularity (Fact 1.1(b)),

   ```text
   rk(TM) = rk(TM cap K) + rk(J) - rk(K)  >=  rk(TK) + rk(J) - rk(K) .
   ```

   By Fact 1.1(d) applied to `X`, `rk(J) - rk(K) = rk(XJ) = rk(XTM) = rk(TXM) = rk(TX)`. With
   `rk(TM) = delta` and step 3:

   ```text
   delta  >=  c_* (1 - rk(X)) + rk(D_(AP) X) .
   ```

5. **Estimates.** If `delta <= (1+eps) c_*`:
   * upper: `rk(TX) - delta rk(X) <= (delta - c_*)(1 - rk(X)) <= eps c_* <= eps delta`;
   * lower: `delta rk(X) - rk(TX) <= delta rk(X) (1 - 1/(1+eps)) <= eps delta`.

   If `delta = c_*` both bounds meet. QED

**Corollary 2.2 (special cases).**
1. *Products of defects.* Taking `X = D_(B_1) ... D_(B_k)` for cylinders disjoint from `A` recovers
   Proposition 4.1 of the descent artifact.
2. *Invariant summands.* Every `sigma(iota_A(R^x))`-invariant decomposition `M = J (+) K` has its
   idempotent in the commutant. At a model with `delta = c_*`, both restricted models have normalized
   defect exactly `c_*`.
3. *The complementary model.* The complement of `A` is a nonempty clopen set `E`, and `iota_E(R^x)`
   commutes with `iota_A(R^x)`. The model `sigma o iota_E` is fixed-point-free (Lemma 3.0 applies to
   any cylinder inside `E`). So at near-minimal defect, `D_(AP)` is rank-independent of every element of
   `sigma(F_2[iota_E(R^x)])`: of the root elements, the defects, and the group algebra of a whole
   fixed-point-free model of `R^x` on the complement.

**Remark 2.3 (what independence does not give).** Theorem 2.1 fixes ranks of *products* `D_(AP) X`.
It does not fix ranks of sums of elements from `iota_A` and from the commutant. The doubled defect of
Section 3.3, which the halving relation makes conjugate to a single defect, is such a sum. So
commutant independence and the doubling identity do not combine into a contradiction by rank
arithmetic alone; Section 3 shows why no finite-subgroup argument can do it.

## 3. Finite-subgroup data cannot force a deficit

**3.1 The regular assignment.** For `alpha` in `F_2[R^x]` whose support generates a finite subgroup
`K`, put

```text
rk_reg(alpha) = dim_(F_2)( alpha · F_2[K] ) / |K| .
```

**Lemma 3.1.**
* (a) *Well defined.* If `K <= K'` are finite, `F_2[K']` is a free `F_2[K]`-module of rank `[K':K]`,
  so `dim(alpha F_2[K']) = [K':K] dim(alpha F_2[K])`. The value does not depend on `K`.
* (b) *A genuine rank model on every locally finite subgroup.* On `F_2[K]` it is the normalized rank
  of the regular representation. If `L` is a countable locally finite subgroup, choose finite
  `K_1 <= K_2 <= ...` exhausting `L`. The regular representations of the `K_n`, along a nonprincipal
  ultrafilter, define a homomorphism `lambda_L : L -> M^x` into a rank ultraproduct over `F_2` with
  `rk(lambda_L(alpha)) = rk_reg(alpha)`. If `L` is infinite, `lambda_L` has no nonzero fixed vector,
  because `K_n` fixes a subspace of normalized dimension `1/|K_n|` in its regular representation.
* (c) *Conjugation invariance.* For every unit `g` of `R^x`, `Ad(g)` is an algebra isomorphism
  `F_2[K] -> F_2[gKg^-1]`, so `rk_reg(g alpha g^-1) = rk_reg(alpha)`.
* (d) *Independence on commuting factors.* If finite subgroups `K_1`, `K_2` commute elementwise and
  meet trivially, `F_2[K_1 K_2] = F_2[K_1] (x) F_2[K_2]`, and
  `rk_reg(alpha beta) = rk_reg(alpha) rk_reg(beta)` for `alpha` in `F_2[K_1]`, `beta` in `F_2[K_2]`.

*Proof.* (a), (c), (d) are as stated; for (d) the regular module of `K_1 x K_2` is the tensor product
of the regular modules. (b): relations among finitely many elements of `L` hold inside some `K_n`,
and ranks are ultralimits of the constant values `rk_reg`. QED

**3.2 Values on the configuration.** Let `A` be a proper cylinder, `x = iota_A(x_12(1))`,
`y = iota_A(x_23(1))`. They generate `iota_A(U_3(F_2))`, which is dihedral of order `8`.
* `rk_reg(1 + x) = 1/2`: every involution acts freely on the regular module.
* `rk_reg(D_A) = rk_reg((1+y)(1+x)) = 3/8`. In `F_2[D_8]`, `(1+x)v` lies in the right ideal
  `(1+y)F_2[D_8]` exactly for `v` in a subspace of dimension `4 + dim((1+x)F_2[D_8] cap (1+y)F_2[D_8])`.
  That intersection consists of elements fixed on the left by all of `D_8`, so it is spanned by the sum of the
  group. So the kernel has dimension `5`, the image `3`.
* For disjoint proper cylinders `A`, `B`, `iota_A(R^x) cap iota_B(R^x) = 1` and the two groups commute,
  so by (d) `rk_reg(D_(A_1) ... D_(A_k)) = (3/8)^k`.

**3.3 What lives inside this data.**
1. *Weyl elements over F_2.* `iota_A(w_ij)` lies in the finite group `iota_A(GL_3(F_2))`.
2. *Halving sheets.* `x_12(1) = x_12(e_0) x_12(e_1)` with `e_i = s_i t_i`, and the iterated sheets
   live in `EL_3(C_n)`, `C_n = span{ s_w t_w : |w| = n } ~= F_2^(2^n)`, a finite group.
3. *Prefix doubling.* For a proper prefix `A'` put `rho(g) = iota_0(g) iota_1(g)`. The prefix
   replacement matching `A'00, A'100, A'110, A'01, A'101, A'111` onto
   `0A'0, 0A'10, 0A'11, 1A'0, 1A'10, 1A'11` (complements matched arbitrarily) conjugates
   `iota_(A')(x_ab(1))` to `rho(iota_(A')(x_ab(1)))` for `ab = 12, 23`. So the doubled defect

   ```text
   D^rho = ((1+P_0)(1+P_1) - 1)((1+Q_0)(1+Q_1) - 1),   P_i = N^(iA')_23,  Q_i = N^(iA')_12,
   ```

   has rank `delta` in every model. Since `(1+P_0)(1+P_1) - 1 = (1+P_0)(P_0 + P_1)`, its rank is that of
   `D_(0A')(1 + Q_1) + P_0 Q_1 + Q_0 P_1 (1 + Q_1) + D_(1A')`: a sum across the two commuting halves.
   All of it lies in `F_2[iota_(0A')(D_8) x iota_(1A')(D_8)]`, where the diagonal copy acts freely, so
   `rk_reg(D^rho) = 3/8`, as (c) predicts.
   This is Lemma 5.1 of `research/artifacts/rank-four-orthogonality-check-2026-09-12.md` (w4-r4-orth).
   Its Proposition 5.2 already realizes the halving relations and the swap in the regular model of the
   locally finite group `iota_(A0)(UT_3(R)) x iota_(A1)(UT_3(R)) x| <iota_A(w)>`. Theorem 3.2 extends
   that one configuration to a single conjugation-invariant assignment on all finite subgroups at once.
4. *The swap* of `A` and `B` has order two and normalizes the finite group generated by the two
   configurations.
5. *Torus units and compressors* such as `diag(u, u^-1, 1)` or prefix replacements carrying `A` into a
   sub-cylinder enter the SUB question as conjugators. Rank equalities between conjugate
   finite-subgroup elements hold for `rk_reg` by (c).
6. *Unitriangular data* is the special case of `unitriangular-data-cannot-assemble-corner-leavitt-families`.

**Theorem 3.2 (firewall).** The assignment `rk_reg` is a Sylvester matrix rank function on the group
algebra of every locally finite subgroup of `R^x` and comes from a fixed-point-free rank model of every
infinite one. It is invariant under conjugation by every unit, and it has

```text
rk_reg(D_A) = 3/8 ,     rk_reg(D_A D_B) = rk_reg(D_A) · rk_reg(D_B)
```

for disjoint proper cylinders. Hence no inequality `rk(D_A D_B) <= theta rk(D_A) rk(D_B)` with
`theta < 1` follows from:
* rank calculus in regular rank rings applied to elements of finite-subgroup algebras;
* the group relations among elements of finite subgroups;
* rank equalities for elements conjugate under arbitrary units.

Items 1–6 of 3.3 are inputs of exactly these kinds, so the Weyl, halving, doubling, swap, torus and
compressor mechanisms cannot give a deficit on their own.

**Remark 3.3 (why the regular assignment is the attractor).** Suppose the two halves `iota_(0A')` and
`iota_(1A')` acted as tensor factors on a root involution, each half `(1 - 2nu) Triv (+) 2nu Free`
as a module for that involution. The doubled involution `x (x) x` has free share `1 - (1 - 2nu)^2`, so its
displacement is `2nu - 2nu^2`. Doubling conjugacy (3.3.3, applied to one root element) forces
`2nu - 2nu^2 = nu`, so `nu` is `0` or `1/2`. Iterated second quantization converges to the free,
regular values. So `theta = 1` at `delta = 3/8` is the one tensor-type profile compatible with every
local test; a deficit has to break tensor type through structure that finite subgroups do not carry.

## 4. Where it stops

* **Products are pinned.** At near-minimal defect every product of `D_(AP)` with an element of the
  commutant of `iota_A(R^x)` has independent rank (Theorem 2.1). A deficit cannot come from a commuting
  factor.
* **Local data is pinned.** Everything expressible through finite subgroups and conjugation is realized
  with `theta = 1` (Theorem 3.2).
* **What remains.** A proof of `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` must use at
  least one of:
  * an operator identity in which `sigma` of a subgroup that is not locally finite enters as *factors*,
    not only as conjugators: opposite root elements with non-constant coefficients together (for
    instance `x_12(r)` and `x_21(r')` whose product has infinite order), or torus units and prefix
    replacements of infinite order inside products with defects. The isometry-coefficient root
    elements `n_12(t_i)`, `n_23(s_j)` of `leavitt-isometry-commutators-constrain-el3-rank-models` are
    *not* of this kind: they lie in `UT_3(R)`, which is locally finite (w4-r4-orth, Proposition 2), so
    Theorem 3.2 covers them;
  * a global input (corner locality, globality, displacement, compactness) turned into an *upper* bound.
    Theorem 2.1 is the global tool on products; nothing known bounds sums such as `D^rho` against
    commutant independence.
* **Against w4-r4-orth's untested list** (artifact above, end of Section 5):
  * opposite roots over `F_2` at a child cylinder lie in the finite group `iota_(Ai)(GL_3(F_2))`: covered;
  * compressors used as conjugators: covered by invariance;
  * the nine-leaf configuration enters through globality, a global input: not covered;
  * block root groups `x_12(r)`, `r` in `R`, of `GL_2(R)` normalized by the torus
    `iota_0(R^x) x iota_1(R^x)`. The group `{x_12(r)}` is `(R, +)`, an elementary abelian 2-group, and a finite
    subgroup of the torus conjugates `x_12(r)` to `x_12(g r h^-1)`. So finitely many block root elements
    together with a finite part of the torus generate a finite group: covered. Not covered: opposite
    block roots `x_12(r)`, `x_21(r')` together when they generate an infinite dihedral group, and torus
    elements of infinite order used as factors. That is the live mechanism of the "infinite-order
    factor" kind. (The first landing of this bullet at 01aa418e41 said the block root groups themselves
    are not locally finite; that was wrong and is corrected here.)
* **Sibling firewall.** w4-sub-adversary (`locally-finite-hnn-data-allow-independent-cylinder-defects`,
  artifact `research/artifacts/locally-finite-conjugation-defect-firewall-2026-09-12.md`) builds a
  fixed-point-free rank model on HNN data over a locally finite subgroup, which is stronger than
  Theorem 3.2 on single conjugations. Its first escapes, the frame product
  `b = iota_A(w_23) iota_(A1)(w_12)` of infinite order and `x^A_12(s_0) x^A_21(1)`, are exactly configurations
  outside every locally finite subgroup, consistent with the corrected list above.
* **Most concrete next test.** At a model with `delta = c_*`, Theorem 2.1 says both corners of every
  invariant decomposition of `iota_A` carry defect exactly `c_*`. A contradiction would follow from one
  `sigma(iota_A(R^x))`-invariant summand whose normalized defect differs from `c_*`. Such a summand must be
  built from an infinite-order unit, since finite-subgroup constructions are covered by Section 3.
