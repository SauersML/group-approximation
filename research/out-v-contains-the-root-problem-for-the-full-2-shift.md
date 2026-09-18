---
rg: 2
id: out-v-contains-the-root-problem-for-the-full-2-shift
kind: claim
title: The Lipschitz part of Out(V) is the inert automorphism group of the full 2-shift, so any bound on roots in Out(V) settles cases of Boyle's open root problem, and a copy of Q in Out(V) must use non-Lipschitz transducers
distinct_from:
  aff-q-embeds-in-aut-v: that asks for Aff(Q) in Aut(V), equivalently in Out(V) = O_2; this locates the root question for O_2 relative to a recognized open problem, and constrains where a copy of Q can sit.
  pgl-2-q-embeds-in-the-rational-group: that embeds PGL_2(Q) in the rational group; this is about the smaller group of bi-synchronizing transducers.
artifacts:
  - research/artifacts/gq-gq-infinite-primes-out-v-reading.md
---

**ESTABLISHED** through `out-v-contains-the-root-problem-for-the-full-2-shift-proof`, by citation plus a short
argument. Refereed: gq-referee-a PASS, proof-gap lens (report 0da548b9b, W1 and N1
applied); one referee so far. The inputs were read in TeX at source, except Boyle--Lind--Rudolph
and Boyle 2008, which were read through Salo. See the artifact. No priority is claimed.

**Notation.** `O_2 ≅ Out(V)` is the group of non-initial bi-synchronizing core transducers over `{0,1}` (BCMNO).
`L_2 = O_2 ∩ SL_2` is its *Lipschitz part*: the elements in which every circuit outputs a word of the same length
as its input. `σ` is the shift of `X_2^Z = {0,1}^Z`, and `Aut = Aut(X_2^Z, σ)`.

**Statement.**
1. **The Lipschitz part is the inert group.** `Aut ≅ <σ> × L_2`, and `L_2 ≅ ker(dim)`, the kernel of the dimension
   representation `dim : Aut -> <2> ⊂ Q^x`. So `L_2` embeds in `Aut`.
2. **No `Q` there.** `L_2` is residually finite. So `L_2` contains no copy of `(Q,+)`, and every copy `D` of `Q` in `O_2`
   meets `L_2` in a proper subgroup of `D`. A copy of `Q` in `Out(V)` must therefore contain transducers that
   violate the Lipschitz constraint SL3 on some circuit. (Whether such an element must change the length of some
   periodic orbit is not shown here; gq-referee-a, W1.)
3. **Transfer of roots.** Let `g in Aut` have infinite order and `n`-th roots in `Aut` for every `n` in a set `I`.
   If `I` is infinite, then the image of `g` in `L_2 ⊂ O_2` has infinite order and has `n`-th roots for every `n in I`.
   So the transfer gives exactly Boyle's form of the question inside `L_2` (gq-referee-a, N1).
   Also, `Z[1/2]` embeds in `Aut` if and only if it embeds in `L_2`.
4. **Calibration.**
   - Suppose an argument shows that no nontrivial element of `O_2` has roots of infinitely many orders. Then it
     answers negatively the open problem whether `Aut` has elements of infinite order with roots of infinitely many
     orders (Boyle 2008, as quoted by Salo 2023), for the full 2-shift. It also shows `Z[1/2] ∉ G`, where `G` is
     the class of groups embedding in the automorphism group of the `Z`-full shift. Salo records that question as open.
   - An argument showing only that no nontrivial element of `O_2` is divisible by every integer would still decide
     the "all orders" case of that problem for the full 2-shift.
   - So an obstruction to `Aff(Q) <= Aut(V)` through roots must either settle these cases or use the coherence of
     the roots, as a copy of `Q` requires. Residual finiteness gives the coherent case on `L_2` (item 2), but not on
     `O_2`.

## Consequences for `aff-q-embeds-in-aut-v`

- It stays **OPEN**. The two candidate routes the coordinator named are now constrained.
  - **Obstruction.** An invariant that grows under taking roots, applied to all of `O_2`, would also apply to
    `L_2 ≅ Inert(σ_2)` and decide a case of Boyle's problem. Invariants that see only coherent roots avoid this.
    Examples are residual finiteness of a suitable quotient, or a faithful action with finite orbits. Core growth
    class is invariant under powers (Olukoya, arXiv:2004.00516), so it cannot serve.
  - **Construction.** A copy of `Q` cannot lie in `L_2`. It needs non-Lipschitz bi-synchronizing transducers with
    coherent roots of every order.
- The periodic orbit representation of BBCO makes `O_2` act faithfully on prime cyclic words. `L_2` preserves
  lengths. A copy of `Q` fixes every finite invariant set of cyclic words pointwise, since `Q` has no nontrivial
  finite quotients. So every nontrivial copy of `Q` in `O_2` has orbits on prime cyclic words of unbounded length.
