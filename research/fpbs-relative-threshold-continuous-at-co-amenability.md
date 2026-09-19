---
rg: 2
id: fpbs-relative-threshold-continuous-at-co-amenability
kind: claim
title: The relative threshold is bounded by a trifurcation-versus-Schreier-Cheeger threshold, so it tends to p_c as the Schreier Cheeger constant tends to 0, and no relative gap is uniform over non-co-amenable subgroups
distinct_from:
  fpbs-co-amenable-subgroup-relative-threshold-is-pc: that proves p_c(I;G) = p_c(G) when the Schreier Cheeger constant h(I) is 0; this proves the quantitative bound p_c(I;G) <= p_tri(h(I)) for every infinite subgroup, with h(I) > 0 allowed, and deduces continuity as h(I_k) -> 0.
  fpbs-percolation-schreier-kesten-gap: that conjectures p_c(G) < p_c(I;G) for each non-co-amenable I; this proves that any such gap degenerates, p_c(I_k;G) -> p_c(G), along every sequence with h(I_k) -> 0, so no gap bound depending only on (Gamma,S) exists.
  fpbs-relative-gap-along-any-subgroup-separates: that proves p_c(I;G) <= p_u(I;G) <= p_u(G); this proves the monotone transfer p_c(N;G) <= p_u(M;G) for every infinite N <= M.
  fpbs-quotient-l2-threshold-sandwich: that bounds p_c(N;G) below by the quotient l2 threshold, which is blind to amenable extensions; this gives upper bounds on p_c(N;G) that are also blind to amenable extensions, giving a two-sided extension-invariant sandwich.
  fpbs-tree-subgroup-relative-gap-iff-not-co-amenable: that computes relative thresholds on the free-group tree by cogrowth; this is an inequality on every Cayley graph and is consistent with the tree formula, where rho_H -> 1 forces R_H -> 1/q.
---

**ESTABLISHED.** Proof in `fpbs-relative-threshold-continuous-at-co-amenability-proof`.

**Setting.**
- `G = Cay(Gamma,S)` for a finitely generated `Gamma` and a finite symmetric
  generating set `S`, with edges `{x, xs}`.
- For an infinite subgroup `I`, `p_c(I;G)` is the Hutchcroft–Pan relative
  threshold of `fpbs-relative-gap-along-any-subgroup-separates`.
- `p_u(I;G)` is the infimum of the `p` at which a.s. exactly one cluster meets
  `I` in infinitely many vertices.
- `h(I) = inf_F |∂F|/|F|` is the Cheeger constant of the Schreier graph
  `Sch(I\Gamma,S)`. The infimum runs over finite nonempty `F ⊆ I\Gamma`, and
  `∂F = {(phi,s) : phi in F, s in S, phi s ∉ F}`. So `h(I) = 0` iff `I` is
  co-amenable.
- For `p in (p_c(G), p_u(G))`, `delta(p) = P_p(o is a trifurcation) > 0`.
  Here `o` is a trifurcation if `K(o) \ {o}` has at least three infinite
  components.
- Put `p_tri(h) = inf{ p in (p_c(G), p_u(G)) : delta(p) > p h }`, with
  `inf ∅ = p_u(G)`.

**Theorem.**

1. *(Quantitative transfer.)* For every infinite subgroup `I`,
   `p_c(I;G) <= p_tri(h(I))`. Explicitly, if `p in (p_c,p_u)` and
   `delta(p) > p h(I)`, then `p_c(I;G) <= p`.
2. *(Continuity at co-amenability.)* If `I_k` are infinite subgroups with
   `h(I_k) -> 0`, then `p_c(I_k;G) -> p_c(G)`. So there is no function
   `g(Gamma,S) > 0` with `p_c(I;G) >= p_c(G) + g` for every non-co-amenable
   `I`.
3. *(Uniqueness transfer.)* If `N <= M` are infinite subgroups, then
   `p_c(N;G) <= p_u(M;G)`. Here `N` need not be normal and nothing is assumed
   about the index.
4. *(Cheeger invariance under amenable extension.)* If `N <= M` are normal in
   `Gamma` and `M/N` is amenable, then `h(N) = h(M)`, so
   `p_tri(h(N)) = p_tri(h(M))`.
5. *(Extension-invariant sandwich.)* For `N <= M` infinite and normal with
   `M/N` amenable, let `p^Q` be the quotient l2 threshold of
   `fpbs-quotient-l2-threshold-sandwich`. Then

   ```text
   p^Q(N) = p^Q(M) <= p_c(M;G) <= p_c(N;G) <= min{ p_tri(h(M)), p_u(M;G) }.
   ```

   So `p_c(N;G) = p_c(M;G)` whenever `p_c(M;G)` equals either end.
   A pair with `p_c(M;G) < p_c(N;G)`, which would refute clause C4 of
   `fpbs-relative-threshold-is-quotient-l2-threshold`, must have `p_c(N;G)`
   strictly below `p_u(M;G)`. It must also satisfy `delta(p) <= p h(M)` for
   every `p in (p_c(G), p_c(N;G))`.

**Existence of the sequences in item 2.** Take `F_2 = <a,b>` with its free
basis.
- Start from the Schreier graph of `(Z/k)^2`, with `a` and `b` acting as the
  two unit shifts.
- Delete one `a`-arc and attach a 4-regular labelled half-tree at each of its
  two loose ends.
- The result is a connected, properly labelled 4-regular graph, so it is
  `Sch(I_k\F_2,S)` for an infinite-index subgroup `I_k`.
- It is quasi-isometric to a tree with all degrees at least 3 outside a finite
  set. So it is nonamenable and `I_k` is not co-amenable.
- The torus block has `|∂F| = 2` and `|F| = k^2`, so `h(I_k) <= 2/k^2 -> 0`.

The same surgery works in every group with a free quotient. On the tree this
agrees with `fpbs-tree-subgroup-relative-gap-iff-not-co-amenable`: each
`p_c(I_k;T) > 1/3`, and `p_c(I_k;T) -> 1/3`.

**What this kills.**
- Any proof of `fpbs-percolation-schreier-kesten-gap` must produce a gap that
  tends to 0 with `h(I)`. Arguments that give a gap from data of `(Gamma,S)`
  alone, uniformly over non-co-amenable `I`, are false.
- The obstruction is the trifurcation density itself. Once `h(I) < delta(p)/p`,
  a cluster at level `p` meets `I` infinitely.
- By items 4 and 5, both ends of the sandwich are unchanged under amenable
  extension. So neither the quotient l2 method nor trifurcation cutting can
  separate `p_c(N;G)` from `p_c(M;G)`. Clause C4 is decided only inside the
  window described in item 5.
