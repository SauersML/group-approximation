---
rg: 2
id: bounded-valence-trees-scale-only-primes-below-the-valence
kind: claim
title: In a tree of valence at most d, a root of prime order l > d of g fixes exactly Fix(g); so groups acting on bounded-valence trees with prime-root-bounded vertex stabilizers are prime-root bounded and contain no (Q,+), GL_n(Q) or Z_(p)
requires:
  - divisible-elements-act-elliptically-on-trees
distinct_from:
  divisible-elements-act-elliptically-on-trees: that shows, for any tree, that an element with roots of infinitely many orders is elliptic and that (Q,+) fixes a vertex or exactly one end; this adds the prime budget of a bounded-valence tree, so primes above the valence cannot be scaled at an end at all and their roots lie in one vertex stabilizer.
  gl-n-q-fixes-a-vertex-in-free-splittings: that is the trivial-edge-stabilizer case, where the valence is infinite and all divisibility sits at a vertex; this is the finite-valence case with arbitrary edge stabilizers, where all but finitely many primes' worth of divisibility sits at a vertex.
  no-q-in-tree-product-actions-with-finite-stabilizers: that needs finite vertex stabilizers; this allows any vertex stabilizers in which each element of infinite order has roots of only finitely many prime orders, e.g. hyperbolic, CAT(0), finitely generated abelian or Thompson-type stabilizers.
  gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings: that exhibits PGL_2(Q) on T_(p+1), with the prime p scaled at an end and the other primes inside Z_(p); this shows that pattern is forced, since a tree of valence p+1 can scale no prime above p+1.
---

**ESTABLISHED** (lane bh-gln-tracka, 2026-09-18; elementary Bass–Serre theory, lane proof, not reviewed; no
priority claimed).

## Setting

`T` is a simplicial tree and `H` acts on `T` by automorphisms without inversions, with every vertex of valence at
most `d`. `Fix(g)` is the fixed subtree of an elliptic `g`, and `H_v` is the stabilizer of the vertex `v`.

A group `K` is **prime-root bounded** if every element of infinite order of `K` has an `ℓ`-th root in `K` for only
finitely many primes `ℓ`.

## Theorem

1. **Same fixed tree.** Let `g ∈ H` be elliptic, `ℓ > d` a prime and `h ∈ H` with `h^ℓ = g`. Then `h` is
   elliptic and `Fix(h) = Fix(g)`.
2. **All high roots in one stabilizer.** If `g` has an `ℓ`-th root for infinitely many primes `ℓ`, then `g` is
   elliptic, and for every `v ∈ Fix(g)` every `ℓ`-th root of `g` with `ℓ > d` prime lies in `H_v`.
3. **Closure.** If every vertex stabilizer `H_v` is prime-root bounded, then so is `H`.
4. **Divisible subgroups.** Let `A ≤ H` be isomorphic to a nonzero subgroup of `(Q,+)` that is `ℓ`-divisible for
   every prime `ℓ` in an infinite set `P`. Then `A_v = A ∩ H_v` is nonzero for some vertex `v`, and every nonzero
   `A_v` is `ℓ`-divisible for every `ℓ ∈ P` with `ℓ > d`.
5. **Exclusions.** If every vertex stabilizer is prime-root bounded, then `H` contains no nonzero subgroup of
   `(Q,+)` divisible by infinitely many primes: no `(Q,+)`, no `Z_(p)`, and no `GL_n(Q)`, `SL_n(Q)`,
   `PGL_n(Q)` (`n >= 2`), `Aff(Q)` or `U_3(Q)`.

**Graphs of groups.** Let `G = π_1(𝕐)` for a finite graph of groups in which every edge group has finite index in
both adjacent vertex groups. Then the Bass–Serre tree has valence at most `d = max_y Σ_(e: o(e)=y) [G_y : G_e]`.
So if every vertex group is prime-root bounded, `G` is prime-root bounded and contains none of the groups in 5.

## Proof

**1.** If `h` were hyperbolic with translation length `τ >= 1`, then `g = h^ℓ` would be hyperbolic with
translation length `ℓτ`. So `h` fixes a vertex `u`, and `g = h^ℓ` fixes `u` too.
- Let `v ∈ Fix(g)`, and let `u = x_0, x_1, ..., x_r = v` be the geodesic. `Fix(g)` is a subtree, so `g` fixes it
  pointwise.
- Suppose `h` fixes `x_i`, and let `e_i = [x_i, x_(i+1)]`. The `⟨h⟩`-orbit of `e_i` consists of edges at `x_i`, so
  it has at most `d` elements.
- Its stabilizer in `⟨h⟩` contains `h^ℓ = g`, so the orbit size divides `ℓ`. Since `ℓ` is prime and `ℓ > d`, the
  size is 1. So `h` fixes `e_i`, and with it `x_(i+1)`.
- By induction `h` fixes `v`. Hence `Fix(g) ⊆ Fix(h)`, and `Fix(h) ⊆ Fix(h^ℓ) = Fix(g)` always holds.

**2.** Suppose `g` were hyperbolic with translation length `τ`, and let `h^ℓ = g` with `ℓ > τ`. If `h` is elliptic,
so is `g`. If `h` is hyperbolic, then `τ = ℓ·τ(h) >= ℓ > τ`. Both are impossible. So `g` is elliptic, and part 1
applies to each root with `ℓ > d`.

**3.** Let `g ∈ H` have infinite order and roots of infinitely many prime orders. By part 2, `g` lies in some
`H_v`, together with its `ℓ`-th roots for the infinitely many primes `ℓ > d`. So `H_v` is not prime-root bounded.

**4.** Each nonzero `a ∈ A` has the root `a/ℓ` for every `ℓ ∈ P`, so it is elliptic by part 2, and `a ∈ A_v` for
every `v ∈ Fix(a)`. If `a ∈ A_v` and `ℓ ∈ P` with `ℓ > d`, then `a/ℓ` is an `ℓ`-th root of `a` (written
additively), so by part 1 it fixes `Fix(a) ∋ v`. Thus `a/ℓ ∈ A_v`.

**5.** By part 4, some `H_v` contains a nonzero `a` of infinite order with roots `a/ℓ ∈ H_v` for infinitely many
primes. Each group listed contains `(Q,+)`: it is a root group `e_ij(Q)` of `GL_n(Q)`, `SL_n(Q)` or `PGL_n(Q)`, the
translations of `Aff(Q)`, and the centre of `U_3(Q)`. `Z_(p)` is divisible by every prime except `p`. ∎

## Sharpness and examples

- **Sharp.** `PGL_2(Q)` acts faithfully on the `(p+1)`-regular tree
  (`gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings`). The unipotent `Q` is parabolic, and scaling at the
  end supplies only the prime `p ≤ d = p+1`. Every other prime divides inside the vertex stabilizer `Z_(p)`,
  exactly as part 4 demands. Likewise `Z[1/m] ≤ BS(1,m)` on the tree of valence `m+1` scales only the primes
  dividing `m`.
- **Prime-root-bounded classes** (context; standard facts, recalled, not re-read):
  - finite groups and finitely generated abelian groups (by inspection);
  - residual finiteness is not enough: `Z_(p)` is residually finite but not prime-root bounded. Part 5 needs only
    that no stabilizer contains a nonzero subgroup of `(Q,+)` divisible by infinitely many primes;
  - groups acting properly by semisimple isometries on CAT(0) spaces (translation lengths of infinite-order
    elements are bounded away from 0 in the cocompact case, Bridson–Haefliger II.6.10);
  - Gromov hyperbolic groups (stable translation lengths of infinite-order elements are bounded below);
  - Thompson's `V` (Higman's lemma, quoted in `divisible-elements-act-elliptically-on-trees`);
  - by part 3, every group acting on a bounded-valence tree with stabilizers in these classes, e.g. every
    generalized Baumslag–Solitar group.

## Reading for Boone–Higman

A locally finite tree has a **prime budget** equal to its valence. Scaling at an end, the mechanism by which
`BS(1,m)` and the `p`-adic tree carry divisibility, reaches only primes at most the valence. Divisibility by every
larger prime must already be present, element by element, in a single vertex stabilizer.

For an input with infinitely divisible elements, such as `GL_n(Q)`, the synthesis v5 dichotomy "scale or sit at an
infinite emitter" therefore sharpens. In every Bass–Serre coding by a finite graph of groups:
- **all edge groups of finite index** (bounded valence `d`): divisibility by every prime `> d` sits in a vertex
  group (this node);
- **trivial edge groups:** all of it sits in a vertex group, and `GL_n(Q)` fixes a vertex
  (`gl-n-q-fixes-a-vertex-in-free-splittings`);
- **what remains:** divisibility can spread along the tree only through an edge group of infinite index that is
  nontrivial, i.e. through a vertex of infinite valence with nontrivial edge stabilizers: an infinite emitter.

So tree geometry never removes the divisibility problem. It pushes the problem into a vertex group, or it forces an
infinite emitter. For `GL_n(Q)` this is a second, property-(T)-free reason, beside
`kazhdan-simple-groups-act-only-on-exotic-2d-buildings`, for the emitter gate (IE) on Track A′.

## Lesson for general BH

Finite valence is a finite prime budget. A bounded-valence tree lets an element have roots of prime order larger than
the valence only when those roots fix the same subtree. So every finite-type tree coding carries divisibility, and
more generally roots of unbounded order, only inside its vertex groups. The inputs that tree geometry cannot resolve
are therefore of two kinds: Kazhdan inputs without finite quotients, which fix points (813bff6dd), and divisible
inputs, whose divisibility fixes points. Both must be carried by a vertex group or by an infinite emitter. Any
proposed tree-type host for such an input should first say which vertex group or which emitter carries it.
