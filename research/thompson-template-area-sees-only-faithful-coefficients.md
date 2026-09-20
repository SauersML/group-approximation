---
rg: 2
id: thompson-template-area-sees-only-faithful-coefficients
kind: claim
title: "Edge area of a conjugate template is the cost of commuting a null-homotopic conjugacy loop past h, and every relation-module area bound with coefficients not faithful modulo the centre is constant on it"
distinct_from:
  finite-mark-centralizer-commutator-area-is-proper: that proves divergence of commutator area for a finite-order mark with a finite-dimensional local system; this shows that finite-dimensional and every other non-faithful local system is constant on conjugate-template edges in F and T-bar, which are torsion-free.
  houghton-cohomological-dehn-lower-bounds-cap-at-quadratic: that caps cocycle certificates for the Dehn function of Houghton groups; this is about single commutator families in a code table, and the cap is a constant, not a growth rate.
  infinite-chromatic-commutator-code-kills-mf-mark: that is the sufficient criterion that turns bounded edge area into a kill; this analyses which lower-bound tools can refute bounded edge area.
  lifted-thompson-t-is-not-mf: that is the target; this is a class kill for the tools that could decide its last open code question, plus an exact reformulation of that question.
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`thompson-template-area-sees-only-faithful-coefficients-proof`.

## Setting

`Gamma = <X | R>` is finitely presented, `N = <<R>>` in the free group
`F(X)`, and `Rel = N/[N,N]` is the relation module, a left `Z Gamma`-module
by conjugation (`g . n[N,N] = g n g^(-1) [N,N]`).  Write `cl(w)` for the class of `w in N`.

A *linear area certificate* is a `Z Gamma`-map `phi: Rel -> M` into a
module `M` with a `Gamma`-invariant seminorm `||.||`, and it gives the bound

```text
L_phi(w) := ||phi(cl w)|| / max_(r in R) ||phi(cl r)||  <=  Area_R(w).     (LC)
```

Special cases of (LC) are:

- the central-extension, Hopf or torus-class bound, where `M = N/[F,N]` is a trivial module;
- cocycle certificates, where `M` is dual to a cohomology class with coefficients in a module;
- the twisted Schreier-chain norms of `finite-mark-centralizer-commutator-area-is-proper`, where `M` is an induced finite-rank local system;
- homological area itself, where `M = Rel` carries the quotient seminorm of
  the ell^1 norm under the surjection `Z Gamma^R -> Rel`.

A *conjugate-template edge* (as in the conjugate-template lane of
`lifted-thompson-t-is-not-mf`) is a word

```text
w_e = [k_e c k_e^(-1), h],    [c,h] != 1,
```

with `c, h` fixed words.  The element `k_e c k_e^(-1)` lies in a fixed
finite set `S` of elements that commute with `h`.  This is condition (N) of
the wave-18 annular localization, and on every arc of the explicit `Sh_3(N)`
template in Thompson's `F` it equals the single element `c_{sI}`.  For each
`s in S` fix a word `sigma_s`, and put

```text
lambda_e := k_e c k_e^(-1) sigma_(s_e)^(-1)  in N      (the conjugacy loop).
```

## Statement

**1. (Exact reduction.)**  With `C_0 = max_(s in S) Area([sigma_s, h])`,

```text
| Area(w_e) - Area([lambda_e, h]) |  <=  C_0,
cl(w_e) = cl([sigma_(s_e), h]) + (1 - h) . cl(lambda_e).
```

So a template has bounded edge area exactly when the diagonal `h`
commutes, at bounded area, with the null-homotopic conjugacy loops
`lambda_e`.  In ultrapower form, let `P_omega = F(X)^omega / <<R>>`, with
the relators taken diagonally.  A sequence of words has `omega`-bounded area
exactly when it is trivial in `P_omega`.  The edge area is bounded exactly
when, for every sequence of arcs and every `omega`, `h` centralizes the
class `Lambda = [lambda_e]_omega`.  That class lies in the kernel of
`P_omega -> Gamma^omega`.

**2. (Blindness.)**  If `h` acts trivially on `M`, then for every conjugate-template edge

```text
L_phi(w_e) <= max_(s in S) L_phi([sigma_s, h])      (a constant).
```

**3. (Which coefficients are blind in F and T-bar.)**

- `Gamma = F`, with `h in F'`: every `Z F`-module on which `h` acts
  nontrivially is faithful, because every nontrivial normal subgroup of `F`
  contains `F'`.
- `Gamma = T-bar`, with `h` in the lifted copy of `F'`: every module on
  which `h` acts nontrivially has kernel inside the centre `<z>`, because
  every non-central normal subgroup contains `[T-bar, T-bar]`, which contains
  the lifted `F' = [F', F']`.

Both apply to the `Sh_3(N)` template, where `h = c_{sK}` is supported in
`(1/4, 1/2)`.

## What this changes

- **Class kill.**  Several tools prove the words `w_e` have unbounded area
  in other lanes: central extensions, the Euler and discrete
  Godbillon–Vey classes, `H_2` torus classes, cocycles pulled back from
  abelian, finite, linear or residually finite quotients, and all
  finite-rank twisted Schreier norms, as in the finite-mark FMC1 theorem.
  None of them can do so here, for any choice of the words `u_v`.  This
  covers the top-bounty need on `Area([k c k^(-1), h])` in `T-bar`.  All
  linear bounds from a coefficient module that is not faithful modulo the
  centre are constant on every conjugate-template edge.  This includes
  every finite-dimensional representation, since `F` and `T` have no
  nontrivial finite-dimensional image beyond abelian quotients.
- **Decomposition.**  What remains splits into two statements that can each
  fail:
  - **(D1)** `sup_e L_phi(w_e) = infinity` for some faithful module, such as
    `ell^1(Gamma)` (homological area) or a permutation module
    `ell^1(Gamma/D)` with `D` the centralizer intersection of the template.
    By item 1 this is the statement that `||(1-h) phi(cl lambda_e)||` is
    unbounded.  For homological area, this means that no ell^1 fillings `Psi_e`
    of the conjugacy loops have `(1-h) Psi_e` bounded modulo 2-cycles.
    The natural way to make it bounded is a near-`h`-periodic filling
    `sum_(i<n) h^i psi` (heuristic).
  - **(D2)** If every linear certificate is bounded, the kill must be
    nonabelian: `h` centralizes `Lambda` modulo `[K, K]` but not in `K`,
    where `K = ker(P_omega -> Gamma^omega)`.
