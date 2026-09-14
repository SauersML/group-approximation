# A non-unimodular calibration, universal Bernoulli preservation, and measure-side dead ends

Lane `gk-rokhlin`, 2026-09-12, landing the handoff of lane `gk-free`, which ended
without landing anything. Supports `end-fixing-tree-symmetries-carry-strict-automata`
and the open claim `every-injective-ca-preserves-uniform-bernoulli-measure`. Proofs
on paper; no computation.

## 1. Calibration: an amenable symmetry group that carries a strict automaton

Let `T` be the 3-regular tree with vertex set `V`, `xi` an end of `T`, and
`Gamma = Aut(T, xi)` the automorphisms fixing `xi`. Every vertex `v` has exactly
one neighbour `p(v)` on the ray from `v` to `xi`, and two children, its other
neighbours. Every automorphism fixing `xi` commutes with `p` and permutes the two
children of each vertex. `Gamma` acts transitively on `V`.

* **Amenable, not unimodular.** The Busemann character `Gamma -> Z` records the
  shift along `xi`. Its kernel, the horocyclic subgroup, is an increasing union of
  compact open subgroups. So `Gamma` is amenable, and its modular function is `2`
  raised to the Busemann character, so `Gamma` is not unimodular.

**Proposition 1.** Let `A` be a totally ordered finite alphabet with `|A| >= 2`,
and put

```text
tau(x)(v) = x(p(v)),        sigma(y)(w) = min{ y(c), y(c') },  c, c' the children of w.
```

Both maps are continuous, `Gamma`-equivariant and local, and `sigma tau = id`.
`tau` is injective and not surjective.

*Proof.*
* `gamma(p(v)) = p(gamma v)` for `gamma in Gamma`, so `tau` is equivariant. The
  children of `w` form a `Gamma`-canonical unordered pair and `min` is symmetric,
  so `sigma` is equivariant too.
* For `y = tau(x)`, both children of `w` carry `x(w)`, so `sigma(y)(w) = x(w)`.
* Any configuration giving two siblings different symbols is not in the image.
  QED

**What this calibrates.** Amenability of a symmetry group and local geometry do not
force surjectivity, even for a transitive action on the index set. Over a group
`G` acting on itself, an equivariant map of the index set is a right
multiplication `g -> g m`, which is a bijection, so this copying mechanism does not
exist. A positive proof must therefore use that the index set is a group:

* unimodularity, or equivalently mass-transport balance, as in
  `certificate-controlled-routing-is-surjunctive`;
* the invariance of the uniform measure;
* or finite models.

The entropy route `strict-automaton-lowers-bernoulli-rokhlin-entropy` uses only a
free measure-preserving group action, consistent with this.

## 2. Universal Bernoulli preservation

**Claim (open).** For every group `G` and finite alphabet `A`, every injective
cellular automaton on `A^G` preserves the uniform Bernoulli measure `mu_A`.

* It implies Gottschalk's conjecture by `injective-measure-preserving-ca-is-surjective`.
* It follows from Gottschalk's conjecture by `bijective-ca-preserve-uniform-bernoulli-measure`.

So it is equivalent to the goal, automaton by automaton. It holds over sofic groups
because Gromov--Weiss makes the automaton bijective.

**Window balance.** Let `tau` have memory `M`. Then `tau_* mu_A = mu_A` exactly when,
for every finite `Omega` and every `p in A^Omega`,

```text
#{ q in A^(Omega M) : tau(q)|_Omega = p } = |A|^(|Omega M| - |Omega|),
```

because the output on `Omega` reads the input on `Omega M`. For a strict automaton,
a Garden-of-Eden pattern gives count `0`. This is a finite statement about the
incidence pattern of the products `Omega M`, in the same spirit as
`bernoulli-rokhlin-deficit-has-a-finitary-witness`.

## 3. Duplicate not landed

gk-free proved that `F_2[G]` is directly finite if and only if `c_0(G, Z_2)` is,
by a Neumann series and reduction mod 2. `padic-c0-direct-finiteness-equivalence`
on main already proves this for every prime and every matrix size. It is not
landed again.

## 4. Measure-side dead ends checked on paper (gk-free)

* **Fixed points of a normal subgroup.** `tau(Fix_H)` lies in `Fix_H`, and `tau` is
  bijective on it when `H` is normal with surjunctive quotient. This is empty on
  simple hosts.
* **Coinvariants.** `H_0(G; C(A^G, Z))` is free abelian on orbits of pattern
  monomials. The induced map is onto with a section, and the class of a missing
  cylinder lies in its kernel. The rank is infinite and the states are just the
  invariant measures, so there is no contradiction.
* **von Neumann kernel.** The kernel of `f -> f o tau` on `L^inf(mu_A)` is the
  invariant ideal `L^inf(A^G \ X)`. Ergodicity gives `mu_A(X)` in `{0, 1}`, so the
  trace argument is vacuous. This is consistent with
  `injective-ca-product-trace-zero-one-law`.
* **Naive per-site entropy.** Over a nonamenable group it depends on the cover
  (Proposition 4 of `gottschalk-rokhlin-entropy-route-2026-09-12.md`). gk-free also
  recorded Burton's zero-or-infinity dichotomy for naive entropy; not re-checked.
* **Iterated images.** `X_n = tau^n(A^G)` decrease strictly. On the attractor
  `X_inf`, `tau` is a homeomorphism, and Cesàro limits of `tau^n_* mu_A` give
  invariant measures there. No contradiction was found.
* **Information transport.** Mass-transport accounting of information is blocked by
  synergy (XOR). See
  `research/artifacts/gottschalk-information-transport-pinning-control-2026-09-08.md`.
  Kazhdan `H^1`-vanishing as a source of the missing global cancellation is untested.
