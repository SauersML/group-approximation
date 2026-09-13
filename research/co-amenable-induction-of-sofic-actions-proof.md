---
rg: 2
id: co-amenable-induction-of-sofic-actions-proof
kind: route
title: Følner sets of the coset space times a stabilizer model, glued by the section cocycle
target: co-amenable-induction-of-sofic-actions
requires:
  - gkp-sofic-action-toolkit
---

**Definition used (GKP Definition 2.1(3), read from page 3 of the v3 PDF on
2026-09-13).** A map `phi : G -> Sym(A)` is an `(F, E, epsilon)`-orbit
approximation of `alpha : G ↷ X` if there are a finite set `B` and a subset
`S <= A` with `|S| > (1-epsilon)|A|`, and for each `s in S` an injective map
`pi_s : E -> B`, such that `pi_(phi(g)s)(x) = pi_s(alpha(g^-1)x)` for all
`s in S`, `g in F`, `x in E` whenever `phi(g)s in S` and `alpha(g^-1)x in E`.

## (=>)

Restriction to a subgroup preserves soficity: GKP Proposition 2.15(3),
[[gkp-sofic-action-toolkit]].

## (<=)

**Section and cocycle.** Choose `sigma : X -> H` with `sigma(x) x_0 = x` and
`sigma(x_0) = 1`. Put `c(g, x) = sigma(gx)^-1 g sigma(x)`. It fixes `x_0`,
so `c(g,x) in K`. It satisfies `c(1, x) = 1` and the cocycle identity
`c(gh, x) = c(g, hx) c(h, x)`.

**Data.** Fix finite `F <= H`, `E <= X`, `epsilon > 0`, and `delta > 0` with
`2 delta < epsilon` and `(1-delta)^2 > 1-epsilon`. Put `F_2 = F ∪ FF`.

**Følner set.** An amenable action has Følner sets. The invariant mean gives
Reiter's condition by Day's convexity argument, and Namioka's layer-cake
argument turns an almost invariant `ell^1` vector into a finite set. These
are the standard proofs for groups, run on `X`. So there is a finite nonempty
`T <= X` with `|T_0| > (1-delta)|T|`, where
`T_0 = {x in T : gx in T for all g in F_2}`. Indeed, `x in T \ T_0` forces
`x in T \ g^-1 T` for some `g in F_2`, and `|T \ g^-1 T| <= |gT Δ T|`.

**Stabilizer model.** Put `F_K = { c(g,x) : g in F_2, x in T } <= K` and
`E' = { sigma(x)^-1 y : x in T, y in E } <= X`. Both are finite. By
hypothesis there is a unital, `(F_K, delta)`-multiplicative
`psi : K -> Sym(B)` that is an `(F_K, E', delta)`-orbit approximation of
`K ↷ X`. Call its good set `S_B` and its labels `pi_b : E' -> B'`.

**The model.** Put `A = T x B`. For `g in H` define `phi(g)` on
`D_g = { x in T : gx in T } x B` by

```text
phi(g)(x, b) = ( gx, psi(c(g,x)) b ).                              (CI1)
```

This map is injective. Extend it to a permutation of `A` in any way. Then
`phi(1) = id`, because `D_1 = A`, `c(1,x) = 1` and `psi(1) = id`.

**Multiplicativity.** Let `g, h in F` and `x in T_0`. Then `hx in T` and
`ghx in T`. By (CI1),

```text
phi(g)phi(h)(x,b) = ( ghx, psi(c(g,hx)) psi(c(h,x)) b ),
phi(gh)(x,b)      = ( ghx, psi(c(g,hx) c(h,x)) b ),
```

with `c(g,hx), c(h,x), c(gh,x) in F_K`. For each fixed `x` the two disagree on
fewer than `delta |B|` points `b`. So
`d(phi(gh), phi(g)phi(h)) < |T \ T_0|/|T| + delta < epsilon`.

**Orbit approximation.** Put `S = T_0 x S_B`, so `|S| > (1-delta)^2 |A|`.
For `s = (x, b) in S` put

```text
pi_s(y) = pi_b( sigma(x)^-1 y )      (y in E),                        (CI2)
```

which is defined (`sigma(x)^-1 y in E'`) and injective. Let `s in S`,
`g in F` and `y in E`, and suppose `phi(g)s in S` and `g^-1 y in E`. Since
`x in T_0`, `phi(g)s = (gx, psi(k) b)` with `k = c(g,x) in F_K`, and
`psi(k) b in S_B`. Put `z = sigma(gx)^-1 y`. Then `z in E'` because
`gx in T`, and

```text
k^-1 z = sigma(x)^-1 g^-1 sigma(gx) sigma(gx)^-1 y = sigma(x)^-1 g^-1 y  in E',
```

because `g^-1 y in E`. The stabilizer model gives
`pi_(psi(k)b)(z) = pi_b(k^-1 z)`, so

```text
pi_(phi(g)s)(y) = pi_(psi(k)b)( sigma(gx)^-1 y ) = pi_b( sigma(x)^-1 g^-1 y ) = pi_s(g^-1 y).
```

So `phi` is unital, `(F, epsilon)`-multiplicative, and an
`(F, E, epsilon)`-orbit approximation of `alpha`. Since `F`, `E` and
`epsilon` were arbitrary, `alpha` is sofic. `∎`

## Remarks

- Transitivity is used only to have one stabilizer and one section. For an
  intransitive amenable action the same construction works with a section
  over each orbit met by `T`, provided every point stabilizer acts soficly.
  (Pad the stabilizer models to a common size.) This version is not claimed
  here.
- `H` is never approximated. All of its behaviour is carried by `T` and by
  the cocycle into `K`. This is why the theorem needs no soficity of `H`.
