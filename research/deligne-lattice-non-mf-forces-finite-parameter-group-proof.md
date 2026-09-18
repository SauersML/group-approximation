---
rg: 2
id: deligne-lattice-non-mf-forces-finite-parameter-group-proof
kind: route
title: Glue one irrational scalar model to the residually finite base, and localize every commutant corner of the central unitary at a parameter
target: deligne-lattice-non-mf-forces-finite-parameter-group
requires:
  - deligne-sep7-norm-parameter-closed-subgroup
  - deligne-sep7-all-cover-mf-radical-classification
  - finitely-generated-linear-groups-are-residually-finite
  - universal-mf-quotient
---

Notation as in the claim. Write elements of `Gamma~ = Gamma x_b Z` uniquely as `z^a s(g)` with `a in Z`, `g in Gamma`,
where `s(g) s(h) = z^(b(g,h)) s(gh)` and `b` is normalized, so `s(e) = e`. Equations `(1)` and `(8)` refer to
`research/artifacts/deligne-sep7-all-cover-mf-classification.md`. `Q = prod_n M_(d_n) / direct_sum_n M_(d_n)`
throughout, and the corona norm is `||[(A_n)]|| = limsup_n ||A_n||`.

Three standard facts about coronas are used:
- *Block sums.* `[(A_n)] (+) [(B_n)] -> [(A_n (+) B_n)]` is an injective unital *-homomorphism from the direct sum of
  two norm matrix coronas into a third one. So a block sum of corona homomorphisms is a corona homomorphism, and its
  kernel is the intersection of the kernels.
- *Lifting.* Projections and unitaries of `Q` lift to coordinatewise projections and unitaries.
- *Rad and MF.* `Gamma~` is MF iff `Rad_MF(Gamma~) = {1}` (`universal-mf-quotient`).

## Step 1: the full circle gives an injective model (item 1)

Suppose `P_op` contains an irrational `theta`. A closed subgroup of `R/Z` with an element of infinite order is the whole
circle, so this is the same as `P_op = R/Z`.

**Scalar model.** Take unitaries `U_n` as in `(1)` at `theta`, with `U_n(e) = I`, and put
`rho(z^a s(g)) = [(exp(2 pi i a theta) U_n(g))_n]`. Then
`rho(z^a s(g)) rho(z^c s(h)) = exp(2 pi i (a+c) theta) c_theta(g,h) [(U_n(gh))]`, by `(1)`. This equals
`rho(z^(a+c+b(g,h)) s(gh))`, so `rho` is a homomorphism into `U(Q)`. Also `rho(z^a) = exp(2 pi i a theta)`, which is
`1` only for `a = 0`.

**Base model.** `Gamma = Sp_4(Z)` is finitely generated linear, hence residually finite
(`finitely-generated-linear-groups-are-residually-finite`). Enumerate finite quotients `Gamma -> F_k` and let
`lambda_k` be the regular permutation representation of `F_k`. Set `pi(g) = [(direct_sum_{k<=n} lambda_k(g))_n]`,
pulled back to `Gamma~` along `z^a s(g) -> g`. Each coordinate is an exact representation, so `pi` is a
homomorphism.

For `g != e`, pick `k` with `g` nontrivial in `F_k`. Then `lambda_k(g)` is a nontrivial permutation matrix. It has a
cycle of length `L >= 2`, hence an eigenvalue `zeta != 1` with `zeta^L = 1`, and `|zeta - 1| >= sqrt 3`. So every
coordinate `n >= k` of `pi(g) - 1` has norm at least `sqrt 3`, and `pi(g) != 1`.

**Injectivity.** Let `Theta = rho (+) pi`. If `Theta(z^a s(g)) = 1`, then `pi` forces `g = e`, and `rho(z^a) = 1`
forces `a = 0`. So `Theta` is injective and `Gamma~` is MF. Only one irrational parameter was used.

## Step 2: the corner lemma (item 2)

Let `q` be a nonzero projection in `Theta(Gamma~)' cap Q`, and let `lambda = exp(2 pi i psi)` with
`||(Z - lambda) q|| <= eta`, where `Z = Theta(z)`.

**Telescoping.** For an integer `c`, put `Z^c - lambda^c = sum_{i<c} Z^(c-1-i) lambda^i (Z - lambda)` if `c > 0`, and
`Z^c - lambda^c = -Z^c lambda^c (Z^(-c) - lambda^(-c))` if `c < 0`. Since `q` commutes with `Z`,
`||(Z^c - lambda^c) q|| <= |c| eta`.

**Corner defect.** In `Q`, `Theta(s(g)) Theta(s(h)) = Z^(b(g,h)) Theta(s(gh))`. Hence

```text
q Theta(s(g)) q Theta(s(h)) q - lambda^(b(g,h)) q Theta(s(gh)) q
   = q (Z^(b(g,h)) - lambda^(b(g,h))) Theta(s(gh)) q,
```

using that `q` commutes with `Theta(s(g))`. Its norm is at most `|b(g,h)| eta`.

**Lifting.** Lift `q` to projections `q_n` and `Theta(s(g))` to unitaries `V_(g,n)`. Since `q != 0`, the set `N` of
`n` with `q_n != 0` is infinite, and `limsup` over `N` of `||q_n||` is `1`.

For each fixed `g`, `||[q_n, V_(g,n)]|| -> 0`. So on the corner `q_n C^(d_n)`, the compression `q_n V_(g,n) q_n` has
unitarity defects that tend to `0`. Its polar part `U_(g,n)` is a corner unitary with
`||U_(g,n) - q_n V_(g,n) q_n|| -> 0`. There is no rank-dependent constant, exactly as in Section 3 of the artifact.

Fix a finite window `W` and `kappa > 0`. The corona inequality above says that, for all large `n` in `N`,

```text
max_{(g,h) in W} ||U_(g,n) U_(h,n) - exp(2 pi i psi b(g,h)) U_(gh,n)|| <= B_W eta + kappa.
```

This is a positive-dimensional tuple on `W`, so `f_W(psi) <= B_W eta + kappa`. Letting `kappa -> 0` proves item 2.

**Lemma D (limits of localized parameters).** Let `K` be a compact subset of `R/Z`. Suppose `psi_j in K` and
`eta_j -> 0` satisfy `f_W(psi_j) <= B_W eta_j` for every finite `W`. Then `K` meets `P_op`.

*Proof.*
1. Pass to a subsequence with `psi_j -> psi*` in `K`.
2. By `(8)`, `f_W(psi*) <= B_W eta_j + 2 pi B_W dist(psi_j, psi*)`, which tends to `0`. So `f_W(psi*) = 0` for every
   `W`.
3. The diagonal argument at the end of Section 5 of the artifact then gives `psi* in P_op`. It takes error below
   `1/n` on the first `n` pairs, with `(e,e)` included for the normalization.

**Uniform form.** For every compact `K` disjoint from `P_op` there is `eta_K > 0` such that, for every corona
homomorphism `Theta` of `Gamma~`:
- no nonzero projection `q in Theta(Gamma~)' cap Q`, and
- no `psi in K`

satisfy `||(Theta(z) - exp(2 pi i psi)) q|| <= eta_K`. Otherwise item 2 and Lemma D give a point of `K cap P_op`.
Note that `eta_K` does not depend on `Theta`.

## Step 3: the arc constraint (item 4)

Assume `P_op = (1/m)Z/Z`. Let `X = sp(Z)` be the spectrum of `Z = Theta(z)` inside `S^1`, and let `lambda in X` lie
in a degenerate component `{lambda}`.

**A small clopen neighbourhood.** In a compact Hausdorff space, components equal quasi-components. So `{lambda}` is
the intersection of the clopen subsets of `X` that contain `lambda`. By compactness, for every `r > 0` some clopen
`C` satisfies `lambda in C subset B(lambda, r)`.

**The corner.** Put `q = chi_C(Z)`. It is well defined because `chi_C` is continuous on `X`, and it is nonzero because
`C` is a nonempty clopen part of the spectrum. Since `z` is central, `q in C*(Z) subset Theta(Gamma~)' cap Q`.
Also `||(Z - lambda) q|| = max_{mu in C} |mu - lambda| <= r`.

**Conclusion.** By item 2, `f_W(psi) <= B_W r` for every `r`, so `f_W(psi) = 0` for every `W`. The diagonal argument
gives `psi in P_op`, so `lambda^m = 1`.

**Consequences.**
- `Z^m` is normal, so `Z^m = 1` iff `X subset mu_m`.
- If `Z^m != 1`, some `lambda in X` has `lambda^m != 1`. It lies in a nondegenerate component, which is a connected
  subset of `S^1` with more than one point, so an arc or the circle.
- Then `X` is infinite. A unitary of finite order has finite spectrum, so `Z` has infinite order.
- By the uniform form of Step 2, applied to closed arcs of parameters that avoid `(1/m)Z/Z`, no commutant corner
  localizes `Z` near any point of such an arc.

## Step 4: the radical dichotomy (item 3)

Assume `P_op = (1/m)Z/Z`.

**Rad is inside `<z^m>`.**
- Let `z^a s(g) in Rad_MF(Gamma~)`. The base model `pi` of Step 1 forces `g = e`.
- The scalar model at `1/m in P_op` sends `z^a` to `exp(2 pi i a/m)`. So `m | a`.
- `Rad_MF` is a subgroup of `<z^m> = Z`, so it is `<z^(km)>` for some `k >= 0`.

**If Rad is nontrivial, it is all of `<z^m>`.** Suppose `k >= 1`.
1. Every corona homomorphism `Theta` has `Theta(z)^(km) = 1`.
2. So `sp(Theta(z))` lies in `mu_(km)`. It is finite, so every point is a degenerate component.
3. By Step 3, `sp(Theta(z)) subset mu_m`, so `Theta(z)^m = 1`. Hence `z^m in Rad_MF` and `k = 1`.

**E_m is MF.** `E_m = Gamma~/<z^m>` is MF by `(6)` of the artifact, since `1/m in P_op`.

## Step 5: the conditional converse (item 5)

Assume `P_op = (1/m)Z/Z` and `(CPE*)`. Suppose, for contradiction, that some `Theta` has `Theta(z)^m != 1`. Put
`Z = Theta(z)` and `delta = ||Z^m - 1|| > 0`. Fix `eta in (0,1)`, and let `q`, `mu` be as in `(CPE*)`, with
`|mu - 1| >= delta` and `||(Z^m - mu) q|| <= eta`.

**Spectrum of the corner.** `Y = Z q` is a unitary of the corner `qQq`, and it commutes with `Theta(Gamma~)`. Since
`Y^m - mu q` is normal, its spectrum `sigma = sp_(qQq)(Y)` lies in `{lambda in S^1 : |lambda^m - mu| <= eta}`.

**Nearest roots.** Let `omega_1, ..., omega_m` be the `m`-th roots of `mu`. Write `lambda = omega_j exp(i phi)` with
`omega_j` a nearest root, so that `|phi| <= pi/m`. Then

```text
|lambda^m - mu| = 2 |sin(m phi / 2)| >= (2/pi) m |phi|,
```

so `|phi| <= pi eta/(2m)`. The closed arcs `A_j` of half-width `pi eta/(2m) < pi/m` around the `omega_j` are pairwise
disjoint, and `sigma` lies in their union.

**Splitting the corner.** The projections `q_j = chi_(A_j)(Y)` lie in `C*(Y)`, so they lie in
`Theta(Gamma~)' cap Q`, and they sum to `q`. Pick `j` with `q_j != 0`. Then
`||(Z - omega_j) q_j|| <= sup_{|phi| <= pi eta/(2m)} |exp(i phi) - 1| <= pi eta/(2m)`. Also
`|omega_j^m - 1| = |mu - 1| >= delta`.

**Contradiction.** Write `omega_j = exp(2 pi i psi_eta)`. Then `psi_eta` lies in the compact set
`K_delta = {psi : |exp(2 pi i m psi) - 1| >= delta}`, which is disjoint from `(1/m)Z/Z = P_op`. By item 2,
`f_W(psi_eta) <= B_W pi eta/(2m)`. Letting `eta -> 0`, Lemma D gives a point of `K_delta cap P_op`, which is a
contradiction.

**Conclusion.**
- `Theta(z)^m = 1` for every `Theta`, so `z^m in Rad_MF`. With Step 4, `Rad_MF(Gamma~) = <z^m>`, which is nontrivial.
  So `Gamma~` is not MF.
- With Step 1: `Gamma~` is MF iff `P_op = R/Z`.
- By `(6)` of the artifact, that holds iff `1/q in P_op` for every `q`, iff every `E_q` is MF.

## Step 6: the flagship decomposition (item 6)

**Forward.** Assume (i), that `Gamma~` is not MF. By Step 1, `P_op = (1/m)Z/Z` with `m` even, the evenness coming
from `deligne-sep7-norm-parameter-closed-subgroup`. By (ii), `3 not | m`, so `1/3, 2/3 notin P_op`. The annihilator
formula of `deligne-sep7-all-cover-mf-radical-classification` at degree three then gives the flagship. This is the
same last step as in `deligne-triple-cover-via-winding-deficit`.

**Backward under (CPE*).** The flagship says `1/3 notin P_op`, so `P_op` is finite. By Step 5, `Gamma~` is then not
MF, which is (i).

**Each prerequisite can fail on its own.**
- (i) fails by an injective corona model of `Gamma~`. By Step 3, when `P_op` is finite such a model must have an arc
  of spectrum for `Theta(z)`.
- (ii) fails by an MF model of `E_6` with `P_op` still finite.

## Remark: a torsion-free test group

Let `Gamma~(3)` be the preimage of the level-three congruence subgroup `Gamma(3)`.
- *Torsion-free.* `Gamma(3)` is torsion-free, and a central extension by `Z` of a torsion-free group is torsion-free.
- *Kazhdan and finitely presented.* Both properties pass to finite-index subgroups.

`Gamma~` is MF iff `Gamma~(3)` is MF:
- MF passes to subgroups.
- Conversely, induce an injective `Theta` from a finite-index subgroup `H` into `U(M_k(Q))`. Here `M_k(Q)` is again a
  norm matrix corona, with coordinate dimensions `k d_n`.
- The induced unitary of `g` permutes the `k` blocks. If `g` acts nontrivially on `G/H`, it moves some block, so it is
  not `1`. Otherwise it is block diagonal with blocks `Theta(t_i^-1 g t_i)`, and these are not all `1` when `g != e`.

So (i) is equivalent to a torsion-free, finitely presented, Kazhdan group with infinite-order central elements being
non-MF.
