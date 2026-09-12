# Surjectivity on subgroup-fixed configurations, and its exact reach

Lane `w4-free-pos-b`, 2026-09-12. Mathematics on paper; no computation.

**The approach.** A strict automaton has a closed invariant image `X`. Every subgroup `H` gives a
subshift `Fix_H` of configurations constant on right cosets of `H`, and the automaton acts on it as an
automaton on the labelled Schreier graph `H\G`. If that graph admits a surjunctivity argument (finite,
or amenable with enough recurrence), then `Fix_H` lies in `X`. If the admissible subgroups separate
finite sets, the union of the `Fix_H` is dense and `X` is everything. This note proves the transfer,
proves it for finite and repetitive amenable Schreier graphs, determines exactly which groups it can
decide (Section 3), and records that it says nothing on the recorded negative hosts (Section 4).

The open claim `co-amenable-fixed-configurations-lie-in-injective-images` is what the approach aims at.
It is implied by the conjecture.

## 0. Conventions

- `G` is a group and `A` is a finite alphabet with `q = |A| >= 2`.
- An automaton with memory `M` and rule `mu : A^M -> A` is `tau(x)(g) = mu((x(g m))_(m in M))`.
- The shift is `(g.x)(h) = x(g^-1 h)`, and automata commute with it.
- `sigma` has memory `N` and rule `nu`, and `sigma tau = id`. Put `X = tau(A^G)`.
- For `H <= G`, `Fix_H = { x : h.x = x for all h in H }`. Since `(h.x)(g) = x(h^-1 g)`, these are the
  configurations constant on each right coset `Hg`.
- `S = H\G` is the set of right cosets, with the right action `(Hg).k = Hgk`, which is well defined.
- For a finite label set `D`, the labelled Schreier graph `S_D` has an edge `v -> v.d` labelled `d`
  for each `v in S` and `d in D`. `B_R(v)` is the rooted ball of radius `R` in the graph with labels
  `D cup D^-1`.

## 1. Theorem A: restriction to the Schreier graph

**Theorem A.** Let `tau, sigma` be automata over `G` with `sigma tau = id`, and let `H <= G`.

1. `tau(Fix_H) = X cap Fix_H`.
2. The bijection `A^S -> Fix_H`, `y |-> x` with `x(g) = y(Hg)`, conjugates `tau` on `Fix_H` to the
   graph automaton
   `tau_S(y)(v) = mu((y(v.m))_(m in M))`,
   and `sigma` to `sigma_S(y)(v) = nu((y(v.n))_(n in N))`. Moreover `sigma_S tau_S = id`.
3. `Fix_H` is contained in `X` exactly when `tau_S` is surjective, and exactly when `sigma_S` is
   injective.
4. If `H` is normal, `S` is the group `G/H` and `tau_S` is the automaton over `G/H` with memory
   `MH/H`. So `Fix_H` lies in `X` whenever `G/H` is surjunctive.

**Proof.**
1. `tau` commutes with the shift, so it maps `Fix_H` into `Fix_H`. Conversely, suppose `tau(x)` lies in
   `Fix_H`. For `h in H`, `tau(h.x) = h.tau(x) = tau(x)`, and injectivity gives `h.x = x`.
2. If `x(g) = y(Hg)`, then `tau(x)(g) = mu((x(gm))_m) = mu((y(Hgm))_m) = tau_S(y)(Hg)`. The same holds for
   `sigma`. The identity `sigma tau = id` restricts to `Fix_H`, which gives `sigma_S tau_S = id`.
3. `sigma_S tau_S = id` makes `tau_S` injective and `sigma_S` surjective. So `tau_S` is onto iff it is
   bijective, iff `sigma_S` is its inverse, iff `sigma_S` is injective. Part 1 translates `tau_S` onto
   into `Fix_H` contained in `X`.
4. For normal `H`, `Hgm = (gH)(mH)`, so `tau_S` is the displayed automaton. Surjunctivity of `G/H`
   makes the injective automaton `tau_S` onto. QED.

Part 4 is the case recorded under `every-injective-ca-preserves-uniform-bernoulli-measure`. The
content of Theorem A is that the same restriction works for every subgroup, with the group replaced
by its coset space. `X` is invariant, so `Fix_H` lies in `X` iff `Fix_(gHg^-1) = g.Fix_H` does.

**Garden of Eden filter.** Suppose `Fix_H` lies in `X`. Let `p` be a pattern on a finite `E <= G` that
is constant on each class `E cap Hg`. Then `p` extends to a configuration in `Fix_H`, which lies in
`X`, so `p` is not a Garden of Eden pattern. So every Garden of Eden pattern of a strict automaton
takes two different values at two sites `e, e'` of `E` with `e' e^-1 in H`, for every admissible `H`
and every conjugate of it.
