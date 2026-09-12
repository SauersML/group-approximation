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
