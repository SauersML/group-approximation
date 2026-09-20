---
rg: 2
id: pre-injective-automata-can-destroy-never-created-letters-proof
kind: route
title: Over two letters charge noncreation makes a never-created letter inert; over three, a leaf of the tree hull of a difference is seen by a clean neighbour in both slot types
target: pre-injective-automata-can-destroy-never-created-letters
requires:
  - finite-injective-charge-noncreation-forces-surjectivity
---

Complete proof. Notation as in the target.

## Import, verbatim

`finite-injective-charge-noncreation-forces-surjectivity`: "Let A be a finite alphabet with a distinguished
quiescent symbol 0, let G be any group, and let tau:A^G->A^G be a cellular automaton fixing 0^G. Give each
nonzero symbol a strictly positive real charge w(a), and put w(0)=0. [...] Suppose tau is injective on finitely
supported configurations and W(tau(x)) <= W(x) for every finite x. Then equality holds for every finite x."

## Part (a): two letters

Let `A = {c, d}` with `c` never created.

1. **`d` is indestructible and quiescent.** If `x(g) = d` then `τ(x)(g) ≠ c`, so `τ(x)(g) = d`. In
   particular `τ(d^G) = d^G`.
2. **Charge.** Take the quiescent symbol `0 := d`, with `w(c) = 1`. For a configuration `x` with finitely many
   `c`-sites, `W(x)` is the number of `c`-sites. By item 1 the `c`-sites of `τ(x)` lie among those of `x`, so
   `W(τ(x)) <= W(x)`. By hypothesis `τ` is injective on these configurations. Pre-injectivity implies this,
   since two such configurations differ at finitely many sites.
3. **Equality.** The import gives `W(τ(x)) = W(x)`. Together with the inclusion in item 2, the `c`-sites of
   `τ(x)` are exactly those of `x`, for every such `x`.
4. **Inertness.** Let `M` be the memory and `f` the local rule, and let `p ∈ A^M` with `p(1) = c`. Extend `p` by
   `d` outside `M` to get `x`, which has finitely many `c`-sites. Item 3 gives `f(p) = τ(x)(1) = c`. So
   `x(g) = c` implies `τ(x)(g) = c` for every configuration, and `c` is inert.

This also settles the binary case of need `ebb50f1d`: the non-`c` sites of `τ(x)` are exactly those of `x`.

## Part (b): the construction

Let `H = F_2 = <a, b>` and `S = {a, A', b, B'}` with `A' = a^-1`, `B' = b^-1`. The right Cayley graph of `H`
with respect to `S` is the 4-regular tree `T`. Its edges are `{k, ks}`. Let `τ` be the automaton of the target.

1. **Well defined.** Injective pairs `(α, β)` exist because `m + 1 <= m^2` for `m >= 2`. The alphabet
   `{c} ⊔ Z/m` has size `m + 1`, which takes every value `>= 3`.
2. **Quiescent and never created.** A site holding `e ∈ Z/m` is sent to `Z/m`. A `c`-site with four `c`
   neighbours stays `c`. So `τ(c^H) = c^H`, and `τ(x)(k) = c` forces `x(k) = c`.
3. **Growth.** Let `x` hold `e ∈ Z/m` at `1` and `c` elsewhere. Then `τ(x)(1) ∈ Z/m`. Each of the four sites
   `s^-1` (`s ∈ S`) is a `c`-site with the non-`c` neighbour `1`, so its image lies in `Z/m`. Every other site
   `k` holds `c` with four `c` neighbours, since only the neighbours of `1` see `1`, so `τ(x)(k) = c`. The image
   has exactly five non-`c` sites.

## Part (b): pre-injectivity over `F_2`

Let `x ≠ x'` differ exactly on a finite nonempty set `D ⊂ H`. Let `K` be the convex hull of `D` in `T`: the
union of the geodesics between points of `D`. `K` is a finite subtree.

1. **A leaf.** If `K` is a single vertex, let `ℓ` be that vertex. Otherwise let `ℓ` be a leaf of `K`. In both
   cases `ℓ ∈ D`, since an endpoint of a hull lies in the generating set. At most one neighbour of `ℓ` lies in
   `K`, so at least three neighbours `ℓt` (`t ∈ S`) lie outside `K`.
2. **Clean neighbours.** Let `k = ℓt ∉ K`. Then `k ∉ D`. Any neighbour `k' ≠ ℓ` of `k` lies outside `K`: the
   geodesic from `k'` to `ℓ` passes through `k`, so `k' ∈ K` would put `k` in `K` by convexity. Hence `x` and
   `x'` agree at `k` and at every neighbour of `k` except `ℓ`.
3. **Slot seen.** From `k = ℓt`, the site `ℓ` is `k t^-1`, read through the slot `t^-1`. As `t` ranges over at
   least three elements of `S`, the slots `t^-1` include one of `a, b` (an `α` slot) and one of `A', B'` (a `β`
   slot), since each type has only two elements.
4. **Choose the slot.** `x(ℓ) ≠ x'(ℓ)` and `(α, β)` is injective, so `α` or `β` separates `x(ℓ)` from `x'(ℓ)`.
   By item 3, choose a clean neighbour `k` whose slot `s = t^-1` toward `ℓ` has a separating type. Then
   `φ_s(x(ℓ)) ≠ φ_s(x'(ℓ))`, and `Σ(k) - Σ'(k) = φ_s(x(ℓ)) - φ_s(x'(ℓ)) ≠ 0` in `Z/m`, because every other
   term agrees by item 2.
5. **Outputs differ at `k`.** Write `e = x(k) = x'(k)`.
   - `e ∈ Z/m`: the outputs are `e + Σ(k) ≠ e + Σ'(k)`.
   - `e = c`, with some neighbour of `k` other than `ℓ` not `c`: both outputs follow the letter branch, and they
     are `Σ(k) ≠ Σ'(k)`.
   - `e = c`, with all neighbours of `k` other than `ℓ` equal to `c`: if `x(ℓ) = c`, then `τ(x)(k) = c`, while
     `x'(ℓ) ≠ c`, so `τ(x')(k) ∈ Z/m`, and they differ. The case `x'(ℓ) = c` is symmetric. If neither is `c`,
     both outputs follow the letter branch, and they are `Σ(k) ≠ Σ'(k)`.

So `τ(x) ≠ τ(x')`, and `τ` is pre-injective over `F_2`.

## Part (b): groups containing `F_2`

Let `H = F_2 ≤ G`, and let `τ_G` use the same memory `{1} ∪ S ⊂ H` and the same rule. For a left coset `gH`,
the sites `g h` read only sites `g h s` in `gH`. So under `h ↦ g h`, `τ_G` acts on `A^{gH}` as `τ` acts on
`A^H`.
- **Pre-injective.** If `x, x'` differ at finitely many sites, pick a coset `gH` where they differ. Their
  restrictions there differ at finitely many sites, so the images differ on `gH`.
- **The other properties.** Quiescence and the never-created property are sitewise, so they carry over.
  Growth carries over with the single letter placed at `1`, since the other cosets stay at `c`.

This proves the target.

## Checks

- `experiments/dual-charge-calibration-2026-09-17/verify_preinjective.py` checks the `m = 2` case over `F_2`
  (run with seed 1). It confirms growth from one site to five. For 300 backgrounds outside the 1-ball,
  including the all-`c` one, the `3^5` fillings of the 1-ball have pairwise distinct images. Twenty thousand
  random asymptotic pairs also have distinct images.
- `f2_binary_search.py` tests all `2^15 - 1` binary growth rules on the four neighbours in `F_2`, with the
  letter `c = 0` never created. It finds 3904 rules injective on subsets of the 1-ball and none on subsets of
  the 2-ball, in line with part (a).
- `ball_collisions.py` and `rules_search.py` find explicit collisions for binary leaf-type growth rules on the
  3-regular tree.
