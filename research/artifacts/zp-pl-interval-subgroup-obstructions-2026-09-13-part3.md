# Testing the candidates inside V: germs at hyperbolic periodic points

Lane z2-15b-biorderable, 2026-09-13. Parts 1 and 2 show that the Heisenberg group, `BS(1,n)`
(n ≥ 2), hyperbolic `Z^2 ⋊_A Z` and `Z ≀ Z^2` are bi-orderable and are not subgroups of `F`.
Each is a "no" witness for reposed Problem 2.15 iff it embeds in `V`. This part tests them
in `V`.

## Germs of elements of V at fixed points (proved here)

`V` acts on `C = {0,1}^ω`. An element `g` has a finite complete prefix code `{u_i}` and a
bijection onto a complete prefix code `{v_i}` with `g(u_i w) = v_i w`.

**Lemma V-A.** Suppose `g(p) = p`. Choose a piece `u_i` containing `p`. Put
`g'(p) := 2^{|u_i| − |v_i|}`. This does not depend on the refinement, because refining
`u_i → u_i r` changes `v_i → v_i r`.
(a) If `g'(p) = 1` then `g` is the identity on the cone `u_i C`.
(b) On the stabilizer of `p`, `g ↦ log_2 g'(p)` is a homomorphism to `Z`.
(c) Conjugation by any `h` fixing `p` preserves `g'(p)`.
(d) `g` has at most as many fixed points with `g'(p) ≠ 1` as it has pieces.

*Proof.* Write `p = u_i q`, so that `g(p) = v_i q = p`. If `|u_i| = |v_i|`, both words are
the prefix of `p` of that length, so `u_i = v_i` and (a) holds. For (b), take a cone
around `p` small enough to lie in one piece of `g` and of `h`, with `h` mapping it into
one piece of `g`. Composition of prefix replacements adds the length differences. (c)
follows from (b). For (d), a fixed point in a piece with `|u_i| ≠ |v_i|` forces one word
to be a proper prefix of the other, say `v_i = u_i r` with `r` nonempty. Then `q = r q`,
so `q = r^∞` and the fixed point is unique. ∎

Call a periodic point `p` of `g` *hyperbolic* if `(g^k)'(p) ≠ 1` for the least `k` with
`g^k(p) = p`.

## Input needed from the structure theory of V (not proved here)

**(V0)** Every element of `V` of infinite order has a hyperbolic periodic point.

This is part of the revealing-pair picture: every element of `V` splits into a periodic
part and finitely many attractor–repeller flow components (Brin, "Higher dimensional
Thompson groups", Geom. Dedicata 108 (2004); Salazar-Díaz, "Conjugacy in Thompson's
group V"). The exact statements were NOT read this session: arXiv was rate-limited and
the search budget was exhausted. Recorded as open claim
`infinite-order-elements-of-v-have-hyperbolic-periodic-points`. A stronger form (V0+)
says each element has only finitely many hyperbolic periodic orbits.

## Consequences of (V0)

**N1-V. Torsion-free nilpotent subgroups of V are abelian.** Let `H ≤ V` be torsion-free
and nilpotent but not abelian. Take `x`, `y` with `z = [x,y] ≠ 1` central in `<x,y,z>`.
`z` has infinite order, so by (V0) some `z^k` has a hyperbolic fixed point. The set `P`
of hyperbolic fixed points of `z^k` is finite (V-A(d)) and nonempty. `x` and `y` commute
with `z^k`, so by V-A(c) they permute `P`. With `r = |P|!`, the elements `x^r`, `y^r` and
`z^r` fix every `p` in `P`. In class 2, `[x^r, y^r] = z^{r^2}`, so V-A(b) at `p` gives
`log_2 (z^{r^2})'(p) = 0`. But `k·log_2 (z^{r^2})'(p) = r^2·log_2 (z^k)'(p) ≠ 0`.
Contradiction. ∎

**N2-V. `Z[1/n]` (n ≥ 2) is not a subgroup of V, hence neither is `BS(1,n)`.** Let `a ≠ 1`
have arbitrary `n^j`-th roots `b_j` (in `BS(1,n)`, `b_j = t^{-j} a t^j`). `a` has infinite
order, so by (V0) some `a^k` has a hyperbolic fixed point `p`. Its set `P` of hyperbolic
fixed points is finite. Each `b_j` commutes with `a^k`, so `b_j^r` fixes `p` for
`r = |P|!`. By V-A(b), `r·log_2(a^k)'(p)` equals `k n^j·log_2(b_j^r)'(p)`, so `n^j` divides
`r·k·log_2(a^k)'(p) ≠ 0` for every `j`. Contradiction. ∎

**N3-V (only sketched, needs V0+).** For `Z^2 ⋊_A Z` with `A` hyperbolic: at a hyperbolic
periodic point `p` of `u` in `N = Z^2`, a finite-index `L ≤ N` fixes `p`, and `log_2` of
the slope is a nonzero functional on `L` with kernel a rational line `K_p`. `t` carries
`(p, K_p)` to `(t p, A K_p)`, and hyperbolic `A` has no invariant rational line. So the
points `t^j p` are pairwise distinct, and for all but one `j` they are hyperbolic periodic
points of `u`. That contradicts V0+.

So, granting (V0) and (V0+), the three "easy" candidates fail in `V` for the same germ
reason that kills them in `F`. The live candidate is `Z ≀ Z^2`.

## Z ≀ Z^2 inside V: what is known, and the gap

Put `Q = <s,t> ≅ Z^2`, with lamp `a`.

1. **No free wandering.** Granting V0+, commuting `s, t` restricted to a common flow
   component of `s` generate a group whose slope map at an attracting periodic point has
   a nonzero kernel element `c`. By the V-analogue of germ determination (every forward
   orbit in the component converges to the attracting orbit), `c` is the identity on the
   component. So no clopen set has pairwise disjoint `Q`-translates: every point of `C`
   has a nonzero `Q`-stabilizer. This matches the Bodart–D'Angeli–Perego–Rodaro criterion
   (arXiv:2608.02111: f.g. subgroups of `V` are exactly the groups with a faithful
   context-free action). A free `Q`-orbit would place `n × n` grids in a context-free
   Schreier graph, of unbounded tree-width. Whether context-free graphs have bounded
   tree-width in the form needed was not checked.
2. **Cone-preserving lamps give torsion.** Take `s`, `t` flowing on the disjoint cones `0C`
   and `1C` respectively. If `a` preserves both cones then `(1 − x^s)(1 − x^t)·a = 1`,
   since `x^t` fixes the restriction to `0C` and `x^s` fixes the restriction to `1C`. So
   the base module is not free.
3. **Cone-swapping lamps do not commute.** In the same model, with `a(0w) = 1φ(w)` and
   `a(1w) = 0ψ(w)`, requiring `a` to commute with its conjugates by `t^d` forces
   `ψ σ^d φ = ψ σ^{-d} φ`, i.e. `σ^{2d} = 1`, for every `d`. Here `σ` is the flow.
   Impossible.
4. **Gap.** The `F`-proof of part 2 uses one structural fact that `V` lacks: supports
   (bumps) of commuting lamps are equal or disjoint, which makes the bump orbits
   invariant under both `M` and `Q`. In `V`, commuting lamps only preserve each other's
   supports, and the basins of different lamps can overlap. A complete non-embedding
   proof must replace the bump orbits by `Q`-invariant, `M`-invariant pieces on which a
   nonzero stabilizer acts trivially on the restricted lamp. A construction must exploit
   exactly that overlap. Neither is done.
