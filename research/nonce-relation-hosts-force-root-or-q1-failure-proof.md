---
rg: 2
id: nonce-relation-hosts-force-root-or-q1-failure-proof
kind: route
title: Lift the measured full semigroup class-bijectively into the host, pad splittings by a Bernoulli shift, cut finite isotropy by the central corner, and read off the actor's crossed product
target: nonce-relation-hosts-force-root-or-q1-failure
requires:
  - free-action-covariant-models-contain-the-crossed-product
  - finite-isotropy-relation-is-central-corner
  - amenable-by-virtually-free-twisted-crossed-products-are-ce
  - free-actor-extensions-cannot-host-nonce-relation
  - non-ce-relation-is-not-treeable
  - non-ce-property-t-equivalence-relation-exists
---

**Standard facts used.**
* (CE) Connes embeddability passes to trace-preserving von Neumann subalgebras and to corners `pMp` with the
  normalized trace (if `M ⊆ R^omega` then `pMp ⊆ p R^omega p ≅ R^omega`). It also passes to increasing unions. A
  group `G` is hyperlinear iff `L(G)` is CE (Radulescu). Only these directions are used.
* (FM) Feldman–Moore. For an essentially free action `Lambda ↷ (Z, zeta)` preserving a sigma-finite measure,
  `L^infinity(Z) ⋊ Lambda = L(R_Lambda(Z))`. For `A ⊆ Z` with `zeta(A) < infinity`,
  `1_A L(R_Lambda(Z)) 1_A = L(R_Lambda(Z)|A)`, and `L(S) ⊆ L(R_Lambda(Z)|A)` trace-preservingly for a Borel
  subrelation `S`.
* (LN) Lusin–Novikov. A countable Borel relation is a countable union of graphs of Borel partial maps.
* (TYPE I) If a.e. class of `R` is finite, `L(R)` is a direct integral of matrix algebras, hence CE.
* (CFW) Connes–Feldman–Weiss. The orbit relation of an amenable group, restricted to a set of finite measure for an
  invariant sigma-finite measure, is hyperfinite, and a pmp hyperfinite relation has a hyperfinite von Neumann
  algebra.
* (JKL) Restrictions to Borel subsets and Borel subrelations of treeable relations are treeable. This is
  Jackson–Kechris–Louveau Prop. 3.3, as quoted in `non-ce-relation-not-treeable-proof`, part (2). The Cayley graphing
  of an essentially free action of a free group is a treeing. Both statements are Borel and need no measure.

## Step 1. The class-bijective lift (item 1)

This is Step 1 of `jacobson-el-sofic-bilateral-lift-proof`, stated for an arbitrary host. Discard an `S`-invariant
null set, so that `r` is class-bijective everywhere on `A`. This is possible since the `S`-saturation of a
`zeta_A`-null set is null.

For a Borel partial bijection `phi` of `X` with graph in `R`, and `a ∈ r^(-1)(dom phi)`, let `phi~(a)` be the
unique `a' ∈ [a]_S` with `r(a') = phi(r(a))`. Then:
* `phi~` is Borel by (LN), and it is a partial bijection with graph in `S` by class-bijectivity;
* it preserves `zeta_A`, since its graph lies in a measure-preserving relation;
* `(phi psi)~ = phi~ psi~` and `(phi^(-1))~ = (phi~)^(-1)`, because both sides pick the same point of the same class;
* `r ∘ phi~ = phi ∘ r` on `r^(-1)(dom phi)`;
* `Fix(phi~) = r^(-1)(Fix phi)`, since the point of `[a]_S` over `r(a)` is `a` itself. So
  `zeta_A(Fix phi~) = mu(Fix phi)`.

Send `f ∈ L^infinity(X)` to `f ∘ r` and the partial isometry `v_phi` to `v_(phi~)`. The relations of the
algebraic full-semigroup algebra are preserved: multiplicativity, adjoints, and covariance
`v_phi f v_phi^* = (f ∘ phi^(-1)) 1_(ran phi)`, which follows from `r ∘ phi~ = phi ∘ r`. The trace of
`f v_phi` is `integral_(Fix phi) f dmu`. That equals the trace of `(f ∘ r) v_(phi~)`, namely
`integral_(Fix phi~) f ∘ r d zeta_A`, because `Fix phi~ = r^(-1) Fix phi` and `r_* zeta_A = mu`.

A trace-preserving `*`-homomorphism of a weakly dense `*`-subalgebra of `L(R)` extends to a normal trace-preserving
embedding, by GNS. So `L(R) ⊆ L(S) ⊆ L(R_Lambda(Z)|A) = 1_A (L^infinity(Z) ⋊ Lambda) 1_A`, by (FM), with the trace
normalized by `zeta(A)`.

**Finite host.** Normalize `zeta` to a probability measure. If `L(R)` is not CE, then the corner is not CE by
Step 1, so `L^infinity(Z) ⋊ Lambda` is not CE by (CE). If `Lambda` is hyperlinear, this pmp action of `Lambda` has a
non-CE crossed product. By `free-action-covariant-models-contain-the-crossed-product` item 3, (a) fails for this
`Lambda` and this action, so Q1 fails at `Lambda`. Otherwise `Lambda` is non-hyperlinear. This proves item 1.

## Step 2. Splittings give finite hosts (item 2)

Let `c : R -> Lambda` be a Borel cocycle, `c(x, x'') = c(x', x'') c(x, x')`, with `c(x, x') · x = x'`. For fixed
`x`, the map `x' -> c(x, x')` is injective on `[x]_R`, since `c(x, x') · x = x'`. So if `L(R)` is not CE, `R` has
infinite classes on a positive set by (TYPE I), and hence `Lambda` is infinite.

Let `(Y, nu) = ([0,1], Leb)^Lambda` with the Bernoulli shift. For infinite `Lambda` it is essentially free, so the
diagonal action on `(Z, zeta) = (X × Y, mu × nu)` is essentially free and pmp. This is item 2 of
`free-action-covariant-models-contain-the-crossed-product`. Put `A = Z` and

```text
S = { ((x, y), (x', c(x, x') y)) : (x, x') in R }.
```

* **Equivalence relation.** Reflexivity: `c(x, x) = 1` by the cocycle identity. Symmetry:
  `c(x', x) = c(x, x')^(-1)`. Transitivity: `c(x', x'') c(x, x') y = c(x, x'') y`.
* **Borel and countable.** It is the image of `R × Y` under a Borel map that is injective on each fibre.
* **Inside the free orbit relation.** `c(x, x') · (x, y) = (c(x, x') x, c(x, x') y) = (x', c(x, x') y)`.
* **Class-bijective over `R`.** With `r(x, y) = x`, the class of `(x, y)` is
  `{(x', c(x, x') y) : x' ∈ [x]_R}`, and `r` maps it bijectively onto `[x]_R`.
* **Measure.** `r_* (mu × nu) = mu`.

So `(Lambda ↷ Z, A = Z, S, r)` is a finite free host.

## Step 3. Finite stabilizers (item 3)

Let `R` be ergodic, generated by a pmp action of `Lambda` with finite stabilizers a.e. The order `x -> |Stab(x)|` is
`R`-invariant, since `Stab(g x) = g Stab(x) g^(-1)`. So it is a.e. a constant `m` by ergodicity.
`finite-isotropy-relation-is-central-corner` then gives `L(R) ≅ (p P p, m tau_P)` with `P = L^infinity(X) ⋊ Lambda`.
If `L(R)` is not CE, `P` is not CE by (CE). If `Lambda` is hyperlinear, Q1 fails at `Lambda` by the same item 3 of
`free-action-covariant-models-contain-the-crossed-product`.

## Step 4. The equivalence (item 4)

* **(c) ⇒ (b).** An essentially free pmp action of `Lambda` generating `R` is a finite free host of `R` with
  `Z = A = X`, `S = R` and `r = id`.
* **(b) ⇒ (a).** Item 1.
* **(a) ⇒ (c), non-hyperlinear case.** Let `K` be countable and non-hyperlinear; it is infinite. Its Bernoulli shift
  on `([0,1], Leb)^K` is essentially free and ergodic. Its orbit relation has factor `L^infinity(Y) ⋊ K ⊇ L(K)` by
  (FM). `L(K)` is not CE, so the relation factor is not CE by (CE).
* **(a) ⇒ (c), Q1 case.** If Q1 fails at `Lambda`, some pmp action of `Lambda` has a non-CE crossed product
  (`free-action-covariant-models-contain-the-crossed-product` item 3).
  * By (DI) below, some ergodic component of that action has a non-CE crossed product.
  * Its Bernoulli padding is essentially free and ergodic, and its crossed product contains the old one (item 2 of
    the same claim). So it is non-CE.
  * Its orbit relation has that crossed product as factor by (FM).

(DI) is the standard direct-integral fact. A pmp action decomposes over its invariant sigma-algebra into ergodic
components, and the crossed product is the direct integral of the components' crossed products. A pmp relation's
factor decomposes the same way over its ergodic components. A measurable direct integral of CE tracial algebras
with separable predual is CE. So if the whole algebra is non-CE, a positive-measure set of components is non-CE.

## Step 5. The obstruction (item 5)

Fix `R` with `L(R)` not CE. Two established inputs:
* For `Lambda` amenable-by-(finitely generated virtually free), every pmp action of `Lambda` has a CE crossed
  product. This is (TCE1) of `amenable-by-virtually-free-twisted-crossed-products-are-ce` with the trivial cocycle.
* For a countable free `Lambda`, every pmp crossed product is CE by
  `free-actor-extensions-cannot-host-nonce-relation`.

Then:
* **No finite host.** Item 1 would give a non-CE crossed product of `Lambda`.
* **No splitting.** Item 2 would give a finite host with actor `Lambda`.
* **No finite-stabilizer generator.** If `R` is ergodic, item 3 would give a non-CE crossed product. If not, by
  (DI) some ergodic component `R_t` has non-CE factor. A generating action of `R` restricts to a generating action
  of `R_t` with the same stabilizers, and item 3 applies to `R_t`.
* **No infinite-measure host for amenable `Lambda`.** `R_Lambda(Z)|A` is hyperfinite by (CFW). So
  `L(R) ⊆ L(R_Lambda(Z)|A)` lies in a hyperfinite algebra and is CE.
* **No infinite-measure host for free `Lambda`.** The Cayley graphing is a treeing of `R_Lambda(Z)`, and its
  restriction to `A` is treeable by (JKL). So the pmp relation `(R_Lambda(Z)|A, zeta_A)` is treeable. Its factor is
  then CE by `non-ce-relation-is-not-treeable` item 1, read contrapositively: a relation with non-CE factor is not
  treeable. By Step 1, `L(R)` is CE.

Each case contradicts the choice of `R`. The Manzoor relation `R_mu` has non-CE factor by
`non-ce-relation-is-not-treeable` item 3. The property-(T) relation has non-CE factor by
`non-ce-property-t-equivalence-relation-exists`. So both are instances.

## Step 6. Treeings are splittings

Let `{phi_n}` be a treeing of `R` by pmp partial isomorphisms `phi_n : A_n -> B_n` of a non-atomic `(X, mu)`.
* **Extend the partial maps.** `mu(X \ A_n) = mu(X \ B_n)`, so there is a measure isomorphism `X \ A_n -> X \ B_n`.
  Gluing it to `phi_n` gives `T_n ∈ Aut(X, mu)` that extends `phi_n`. Let `F_infinity = <a_n>` act by `a_n -> T_n`.
* **Define the cocycle.** For `(x, x') ∈ R`, the treeing gives a unique reduced path from `x` to `x'` in the edges
  `phi_n^(±1)`. Let `c(x, x')` be the corresponding reduced word in the `a_n^(±1)`. It is Borel by (LN).
* **Cocycle identity.** Concatenate the paths `x -> x'` and `x' -> x''`, then cancel backtracks to get the path
  `x -> x''`. A backtrack cancels as `a_n a_n^(-1)` in `F_infinity`, so `c` is a cocycle.
* **Splitting.** Along the path each step is `phi_n^(±1) = T_n^(±1)` on its domain, so `c(x, x') · x = x'`.

So a treeing is a splitting into `F_infinity`, and item 5 recovers `non-ce-relation-is-not-treeable` item 1. ∎
