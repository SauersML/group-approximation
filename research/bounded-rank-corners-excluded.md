---
rg: 2
id: bounded-rank-corners-excluded
kind: claim
title: A corner detecting the mark cannot have bounded rank
distinct_from:
  commutant-projection-extraction: that claim asks whether a detecting corner exists at all; this one is established and constrains what any such corner must look like, ruling out the bounded-rank ones.
  coordinate-ultraproduct-transport: that claim is the transport statement on the coordinate ultraproduct; this one is a consequence of it about projections in the relative commutant.
---

Let the transport data be as in `coordinate-ultraproduct-transport`: `Gamma`
Kazhdan, `iota : Gamma -> H`, `t` compressing, `c` centralizing,
`u = [t c t^-1, iota a]`, and a central `eps` in the normal closure of `u`
inside `H_0`.  Let `Theta` be a corona representation, `q != 0` a projection
in the relative commutant `Theta(H)' cap Q` with

    ‖(Theta(eps) - lambda) q‖ = 0   for some lambda != 1,

that is, a corner of the kind `commutant-projection-extraction` asks for.
If the lifted ranks of `q` are bounded by `r` along the ultrafilter, and
**every unitary representation of `iota(Gamma)` of dimension at most `r` is
trivial**, then no such `q` exists.

Two instances.  If `iota(Gamma)` is perfect, every one-dimensional
representation is trivial, so no detecting corner has rank one.  If
`iota(Gamma)` is minimally almost periodic — every finite-dimensional
unitary representation trivial, as the repository's Steinberg group
`St_5(L)` is — then no detecting corner has bounded rank at all.

**Compatibility with the block-decomposition lane.**  This does not
constrain `hs-expander-block-decomposition`, whose blocks are almost
invariant in **normalized Hilbert--Schmidt** norm and are explicitly allowed
to have vanishing normalized trace; those blocks do not lie in the relative
commutant used here, which is an exact commutant of the ultraproduct in
operator norm.  The two statements meet only under a strengthening: an
operator-norm version of that block decomposition would have to produce
blocks of **unbounded rank** over a minimally almost periodic source, since
bounded-rank blocks are excluded here.  Worth knowing before either lane
strengthens its norm.

**Consequence for method.**  The only known way to build such a corner is to
produce an approximate joint eigenvector and take the rank-one projection
onto it.  That technique is therefore unavailable for exactly the groups
this program cares about.  See `commutant-projection-extraction` for the
model where the technique does work and why the difference is the
abelianization.
