---
rg: 2
id: invariant-measure-forbids-finite-similarity-type-systems
kind: claim
title: "An invariant probability measure of full support on an infinite unit space forbids every finite similarity type system, so finite-type Stein–Farley finiteness proofs never produce an amenable full group"
distinct_from:
  finite-similarity-types-bound-minimal-invariant-sets: That bounds the number of minimal invariant sets by the number of types, which says nothing for a minimal groupoid; this kills finite type systems on minimal groupoids through the invariant measure.
  v-times-shift-groupoid-has-no-finite-similarity-types: That applies the minimal-set bound to a groupoid with 2^aleph_0 minimal sets; this applies to uniquely ergodic minimal groupoids such as Labbé's Wang shift, where that bound is vacuous.
  amenable-full-group-forces-invariant-measure: That turns amenability into an invariant measure; this turns an invariant measure into the absence of finite similarity types, and together they separate finite-type finiteness proofs from amenability.
  labbe-shift-derived-full-group-escapes-known-obstructions: That records informally that the invariant measure forbids compression; this names the exact structure a Brown-criterion proof needs (a finite similarity type system) and proves the measure destroys it.
---

**ESTABLISHED.**

**Setting.** `G` is an étale groupoid whose unit space `X` is Hausdorff and totally disconnected.
A *similarity type system* is as in `finite-similarity-types-bound-minimal-invariant-sets`: compact
open sets `B_j` (`j ∈ J`) such that every point of `X` has a neighbourhood basis of compact open
*basic sets* `U`, each the range of a compact open bisection with source some `B_{j(U)}`. It is
*finite* if `J` is finite. A Borel probability measure `μ` on `X` is *`G`-invariant* if
`μ(r(S)) = μ(s(S))` for every compact open bisection `S`.

**Theorem.**
1. **Measures of types go to zero.** Let `μ` be `G`-invariant and positive on nonempty open sets.
   For every similarity type system and every integer `N <= |X|`, some basic set has type `j` with
   `μ(B_j) <= 1/N`. If `X` is infinite, the infimum of `μ(B_j)` over the types of basic sets is `0`.
2. **No finite system.** Under the hypotheses of item 1 with `X` infinite, `G` has no finite
   similarity type system. More generally, no similarity type system has type measures bounded
   below by a positive constant.
3. **Minimal case.** Let `G` be minimal with compact, infinite, second countable unit space. If `G`
   has a finite similarity type system, then `X` carries no `G`-invariant probability measure.
4. **No amenable output.** Let `G` also be effective, Hausdorff and ample. If `G` has a finite
   similarity type system, then no group realizing moving bisections is amenable. In particular,
   no group containing `D([[G]])` is amenable, including `D([[G]])` and `[[G]]`.

Proof in `invariant-measure-forbids-finite-similarity-type-systems-proof`.

## What this kills

**The class.** Brown-criterion finiteness proofs for full groups built on a Stein–Farley-type
complex of expansions whose pieces fall into finitely many similarity types. That finiteness is what
makes one-piece vertices fall into finitely many orbits and descending links independent of scale
(motivation in `finite-similarity-types-bound-minimal-invariant-sets`). Members:
- Thompson's `V` and `nV`: one type;
- Matui's `F_∞` theorem for one-sided irreducible SFT groupoids (arXiv:1210.5800, Theorem `finite`,
  as recorded in `labbe-shift-derived-full-group-is-finitely-presented`): cylinders `C_w` are
  bisection-similar to `C_{t(w)}`, so the types are the graph vertices;
- expansions of hyperbolic groupoids (Nekrashevych arXiv:1312.5654) and products of one-sided SFTs
  (Li arXiv:2110.04505), as recorded on the target node;
- groups of local similarities with a finite similarity structure (Farley–Hughes). This member was
  not verified from source.

**The invariant.** A `G`-invariant probability measure of full support.

**The step where every member dies.** Choosing the finite list of types. A bisection preserves
measure, so a type fixes the measure of every piece of that type, and small neighbourhoods need
small pieces (item 1).

**Scope.**
- **Labbé's Wang shift** (`labbe-shift-derived-full-group-is-finitely-presented`). `Z^2 ~ Omega_U` is
  minimal on an infinite Cantor space, and `Z^2` is amenable, so an invariant probability exists and
  has full support. So no finite-type expansion complex proves finite presentation. The same holds for
  the Penrose group (`penrose-derived-full-group-is-finitely-presented`), for every free minimal
  `Z^d`-subshift, and for every minimal action of an amenable group on the Cantor set.
- **The flagship** `fp-infinite-simple-amenable-group`. By item 4, a finite-type Brown-criterion proof
  applied to the full group of a minimal effective ample groupoid always outputs a non-amenable group.
  This whole family of finiteness techniques cannot supply the example, whatever the groupoid.

**What survives: the gate.** A surviving proof must use infinitely many types, with measures
accumulating at `0`. That means a filtration with a scale parameter, as already demanded for a
different reason in `v-times-shift-groupoid-has-no-finite-similarity-types`, together with
connectivity estimates that are uniform in scale. The measure does not obstruct similarity **up to
reduction isomorphism**, where `G|_U ≅ G|_{B_j}` as groupoids but not through a bisection. For Labbé's
shift, `labbe-full-group-embeds-in-its-supertile-corner` gives `G ≅ G|_A` with `μ(A) < 1`. So the
level-`k` supertile cylinders `ω^k([P])` have reductions isomorphic to `G|_{[P]}` for the finitely
many legal collared patches `P`. That is the candidate loophole: the orbits of `Γ` separate the
scales, and `Φ^k` identifies their links. This part is not claimed here. It needs the side lengths of
the blocks `ω^k(a)` to grow in both directions, and the descending-link estimates remain the crux.
