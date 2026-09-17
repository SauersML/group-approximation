---
rg: 2
id: kazhdan-rational-relation-cover-reduction-proof
kind: route
title: Split torsion along the image, embed with the Fox derivation, and kill root powers with a commutator of kernel roots
target: kazhdan-rational-relation-cover-reduction
requires: []
artifacts:
  - research/kazhdan-rational-relation-cover-reduction.md
---

The notation is that of the claim, in `(RC1)`. Standard facts used:

- Property (T) passes to quotients and to finite-index subgroups.
- A Kazhdan group is finitely generated and has finite abelianization.
- Subgroups of sofic groups are sofic.
- Countable amenable groups, in particular countable abelian groups, are sofic.
- `ZP` is free as a `ZR`-module.

Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Ch. 1, covers the first
two; Pestov's survey on hyperlinear and sofic groups covers the next two.

## 0. Preliminaries

`tors(R^ab)` is a characteristic subgroup of `R^ab`. So its preimage `R_sat`
is characteristic in `R`, and therefore normal in `P`. Also
`[R,R] <= R_sat <= R`, and `A = R^ab / tors(R^ab)` is torsion-free.

`Q` is perfect. `Q^ab` is finite because `Q` is Kazhdan, and it is a finite
quotient of `Q`, so it is trivial.

## 1. Torsion criterion

**Orders.** Let `k in K` have finite order `n`, and let `m` be the order of
`pi(k)`. Then `m | n`, and `k^m` lies in `A` and has finite order. Since `A`
is torsion-free, `k^m = 1`. So `n = m`, and in particular `k = 1` when
`pi(k) = 1`.

**Criterion.** If `K` has a nontrivial torsion element, some power of it has
prime order `l`. So `K` is torsion-free if and only if it has no element of
prime order.

- Let `k` have prime order `l`, and lift it to `f in P`. Then `pi(f) = pi(k)`
  has order `l`, `f^l in R`, and `k^l = 1` means `f^l in R_sat`. So (RLT)
  fails.
- Conversely, suppose `f in P` has `pi(f)` of order `l` and `f^l in R_sat`.
  Then the image `k` of `f` has `k^l = 1` and `k != 1`, so `K` has torsion.

**Tate form.** Write `A` additively, with `c = pi(f)` acting by conjugation
by `f`. The element `f^l` commutes with `f`, so `f^l in A^C`. For `a in A`,

```text
(f a)^l = f^l + (1 + c + ... + c^{l-1}) a = f^l + N_C a.
```

So the coset `fA` contains an element of order `l` if and only if
`f^l in N_C A`. That is, the class of `f^l` in `H^0_hat(C; A)` is zero. The
class does not depend on the lift of `c`, since lifts differ by `A`.

## 2. Universality

Suppose `N <= R` is normal in `P`, `R/N` is abelian, and `P/N` is
torsion-free. Then:

- `R/N` is a torsion-free abelian group, so `N >= [R,R]`.
- The image of `tors(R^ab)` in `R/N` is zero, so `N >= R_sat`.

So `P/N = K/(N/R_sat)` is a quotient of `K` over `Q`.

If `k in K` has prime order `l`, then `pi(k)` has order `l`. So the image of
`k` in `P/N` is nontrivial, yet it satisfies `k^l = 1`, which contradicts
torsion-freeness. Hence `K` is torsion-free, and (RLT) holds. The converse
takes `N = R_sat`.

## 3. Quotientless core

`K` is Kazhdan as a quotient of `P`.

Let `phi: K -> F` be a map onto a finite group. Then `phi(A)` is normal, and
`F/phi(A)` is a finite quotient of `Q`, so it is trivial. Thus `F = phi(A)` is
abelian.

`K^ab` is finite because `K` is Kazhdan. So `D = [K,K]` has finite index, and
`D` is Kazhdan and finitely generated.

Suppose `D` had a proper finite-index subgroup `L`. Its normal core `L_0` in
`K` would have finite index in `K`, and `K/L_0` would be abelian. Then
`L_0 >= [K,K] = D`, which is impossible. So `D` has no proper finite-index
subgroup, and in particular no nontrivial finite quotient.

`D` maps onto `[Q,Q] = Q`, with kernel `A cap D`. `D` is torsion-free
whenever `K` is.

## 4. Linear envelope

**The derivation.** `ZQ` is a right `ZP`-module through `pi`. Set
`d(p) = 1 (x) (p-1)` in `M`. Then

```text
d(pq) = 1 (x) ((p-1) + p(q-1)) = d(p) + pi(p) d(q),
```

so `Phi(p) = (d(p), pi(p))` is a homomorphism `P -> M semidirect Q`, with
product `(m,c)(m',c') = (m + c m', cc')`.

**Kernel of `Phi`.** `Phi(p) = 1` forces `p in R`. Put `J = I_R ZP = ZP I_R`,
a two-sided ideal because `R` is normal. Then `ZQ = ZP/J` and
`M = I_P / J I_P = I_P / I_R I_P`.

- For `r in R`, `d(r)` is the class of `r-1`. It lies in the kernel
  `I_R ZP / I_R I_P` of the map `M -> ZQ` induced by `I_P <= ZP`.
- `ZP` is a free left `ZR`-module on a transversal, so
  `I_R ZP = I_R (x)_{ZR} ZP`.
- By right exactness applied to `0 -> I_P -> ZP -> Z -> 0`,
  `I_R ZP / I_R I_P = I_R (x)_{ZR} Z = I_R / I_R^2`.
- `I_R / I_R^2 = R^ab` via `r-1 -> r[R,R]`. Indeed `rs-1 = (r-1)+(s-1)+(r-1)(s-1)`,
  so `r -> r-1` is a homomorphism `R -> I_R/I_R^2`; the elements `r-1` with
  `r != 1` form a `Z`-basis of `I_R`, so `r-1 -> r[R,R]` defines an additive map
  `I_R -> R^ab`, and it kills `(r-1)(s-1) = (rs-1)-(r-1)-(s-1)` because `R^ab`
  is abelian. The two maps are inverse.

So `d|_R` induces an injection `R^ab -> M`. This is the connecting map of
`0 -> H_1(R) -> M -> I_Q -> 0`, and `ker Phi = [R,R]`.

**Rationalization.** Compose `Phi` with `M -> V`, whose kernel is `tors(M)`.
Since `d(R) = R^ab` sits inside `M`, `d(r)` is torsion in `M` if and only if
`r[R,R] in tors(R^ab)`, that is, `r in R_sat`. So `K -> V semidirect Q` is
injective, which proves `(RC2)`.

**Soficity.** Let `W` be countable abelian, and let `iota: V -> (+)_Q W` be an
injective `QQ`-linear map, where `Q` translates coordinates. Then
`(v,c) -> (iota v, c)` is an injective homomorphism
`V semidirect Q -> W wr Q`, the restricted regular wreath product. `W` is
sofic, being countable abelian. If `Q` is sofic, then `W wr Q` is sofic by the
Hayes--Sale theorem (imported below), and so are its subgroups `K` and `D`.
Free modules are the case `W = Q^m`.

## 5. Free covers

`I_F` is the free left `ZF`-module on `x_1 - 1, ..., x_n - 1` (standard Fox
calculus: `w-1 = sum_i (dw/dx_i)(x_i-1)` with unique coefficients). So `M = ZQ (x)_{ZF} ZF^n = ZQ^n = (+)_Q Z^n`.

By Section 4, `F/[R,R]` embeds in `Z^n wr Q`, which is sofic when `Q` is.
Here `Q` is arbitrary: property (T) is not used in Sections 4 and 5.

## 6. Root-element obstruction (RE)

In `EL_n(S)`, for pairwise distinct `i,j,k`, direct matrix multiplication gives

```text
[e_ik(a), e_kj(b)] = e_ij(ab)
```

(for either commutator convention), and `e_ij(x) e_ij(y) = e_ij(x+y)`.

Let `f = e_ij(u)`. Since `pi(f)` has order `l`, `f^l = e_ij(lu)` lies in `R`,
and

```text
(f^l)^m = e_ij(mlu) = e_ij(ab) = [e_ik(a), e_kj(b)]  in [R,R].
```

So the class of `f^l` in `R^ab` has order dividing `m`. Hence `f^l in R_sat`,
and (RLT) fails at `f`.

**Corollary.** For each `x != y`, put `Lambda_xy = {s in S : e_xy(s) in P}`.
This is an additive subgroup of `S`, of finite index because `P` has finite
index.

- Let `N` be the product of the indices `[S : Lambda_xy]`. Then
  `NS <= Lambda_xy` for all `x != y`.
- The image of `Lambda_12` in `T` has finite index, and `T` is infinite. So
  some `u in Lambda_12` has nonzero image `u_bar`.
- `pi(e_12(u)) = e_12(u_bar)` has order `p`.
- Put `a = pN` and `b = pNu`. Both lie in `NS`, so `e_13(a)` and `e_32(b)` lie
  in `P`. Their images are `e_13(0)` and `e_32(0)`, because `pT = 0`, so they
  lie in `R`.
- `ab = p^2 N^2 u = m p u` with `m = pN^2`.

(RE) with `(i,k,j) = (1,3,2)` and `l = p` gives `p`-torsion in `K`.

For the special case: `EL_3(LC(X,F_q) semidirect Z)` is infinite and has
characteristic `p`. Every ring surjection `Z<x_1,...,x_r> ->> T` induces
`EL_3(Z<x>) ->> EL_3(T)`. So the corollary applies to every finite-index
subgroup.

## Import: Hayes--Sale

B. Hayes and A. W. Sale, *Metric approximations of wreath products*, Ann.
Inst. Fourier **68** (2018) 423--455, arXiv:1608.02610. The abstract was read
on arXiv on 2026-09-17. Verbatim:

"Our main result is the following. Suppose that $H$ is a sofic group and $G$
is a countable, discrete group. If $G$ is sofic, hyperlinear, weakly sofic, or
linear sofic, then $G\wr H$ is also sofic, hyperlinear, weakly sofic, or linear
sofic respectively."

This is used with `G = W` and `H = Q`, for the restricted regular wreath
product.

This import is the regular-action case. It is not the coset-action
generalization refuted in `coordinate-action-not-sofic`.
