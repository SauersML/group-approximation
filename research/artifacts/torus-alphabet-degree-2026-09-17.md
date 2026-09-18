# Torus-alphabet surjunctivity through the degree matrix (2026-09-17)

Agent: swarm-0917-w4-gs-decomp-new. Paradigm lane: a new decomposition of Gottschalk
surjunctivity that replaces counting on finite models by topological degree on
connected alphabets.

## 0. Setting and notation

- `G` is a countable group, `d >= 1`, `T = R/Z`, `X_d = (T^d)^G` with the product
  topology and the shift `(h x)_g = x_(h^-1 g)`.
- A *torus automaton* is any continuous `G`-equivariant map `tau: X_d -> X_d`. No finite
  memory is assumed.
- `H^1` is Čech cohomology with `Z` coefficients. For a compact space `Y`,
  `H^1(Y) = [Y, T]` (homotopy classes of maps to the circle).
- `X_d` is the inverse limit of the tori `(T^d)^F`, `F` finite. By continuity of Čech
  cohomology, `H^1(X_d) = colim_F Z^(dF) = Z[G]^d`, with basis `e_(h,i)` = the class of
  the coordinate `x -> (x_h)_i`. The left `G`-action on `X_d` induces left multiplication
  on `Z[G]^d` (row vectors).
- **Degree matrix.** `tau^*` is a `Z`-linear endomorphism of `Z[G]^d` commuting with the
  left `G`-action, so it is right multiplication by a unique `D = D(tau) in M_d(Z[G])`:
  `tau^*(xi) = xi D`. Row `i` of `D` is `tau^*(e_(1,i))`, the class of `x -> tau(x)_(1,i)`.
- `epsilon: Z[G] -> Z` is the augmentation, applied entrywise to matrices.
- For a finite-index normal subgroup `N`, `p_N: Z[G] -> Z[G/N]` is the quotient map,
  applied entrywise.

Two standard facts are used.

- **(F1)** A continuous map between tori `T^n -> T^m` is determined up to homotopy by its
  `H^1` matrix (tori are `K(Z^n, 1)`). When `n = m` its degree is the determinant of that
  matrix (it is homotopic to the linear map with the same matrix).
- **(F2)** A continuous map of nonzero degree between closed connected oriented
  manifolds of equal dimension is surjective. An injective continuous self-map of a closed
  connected manifold is a homeomorphism: its image is open by invariance of domain, closed
  by compactness, hence everything by connectedness.

## 1. Degree lemma (C1): regular degree forces surjectivity, over every group

**Theorem 1.** Let `tau` be a torus automaton on `X_d` over any countable group `G`. If
right multiplication `xi -> xi D(tau)` is injective on `Q[G]^d`, then `tau` is surjective.
No injectivity of `tau` is assumed.

*Proof.*
1. *Finite target windows.* Fix a finite `F in G`. Put `R = {(h,i): h in F, 1 <= i <= d}`.
   The rows `e_(h,i) D`, `(h,i) in R`, are the images of `|R| = dF` independent vectors
   under an injective `Q`-linear map, so they are `Q`-linearly independent. Their supports
   lie in a finite set `R' = F' x {1..d}`, `F' = F . supp(D)`. The integer matrix
   `M in Z^(R x R')` with rows `e_(h,i) D` has rank `|R|`, so there is `S in R'` with
   `|S| = |R|` and `det M_(R,S) != 0`.
2. *Slice map.* Fix any `c in X_d` and let `s: T^S -> X_d` put the given values on the
   coordinates in `S` and `c` elsewhere. Let `pi_F: X_d -> (T^d)^F` restrict to `F`. Then
   `phi = pi_F o tau o s : T^S -> T^R` is a continuous map between tori of the same
   dimension.
3. *Its degree.* On `H^1`, `pi_F^*` includes the basis vectors `e_(h,i)`, `(h,i) in R`.
   `tau^*` multiplies them by `D`. `s^*` sends `e_(k,j)` to itself if `(k,j) in S` and to
   `0` otherwise, since the other coordinates are constant on the slice. So the `H^1`
   matrix of `phi` is `M_(R,S)`, and by (F1) `deg phi = +- det M_(R,S) != 0`.
4. *Window surjectivity.* By (F2), `phi` is onto. So every `y in (T^d)^F` is
   `tau(x)|_F` for some `x`.
5. *Compactness.* `tau(X_d)` is compact, hence closed, and by step 4 it meets every
   cylinder set, hence is dense. So `tau(X_d) = X_d`. QED.

*Remarks.*
- For the linear automaton `tau_D` with the same matrix, Pontryagin duality gives the
  converse: `tau_D` is onto iff `xi -> xi D` is injective on `Z[G]^d`. So Theorem 1 says
  *a torus automaton is onto whenever its linearization is onto*. It is a nonlinear
  transfer that uses no approximation of `G`.
- The converse fails for nonlinear maps. A sitewise map `x -> f(x_1)` with `f: T -> T`
  onto of degree `0` (wind around and back) is onto, and `D = 0`.
- *Conventions.* `tau^*` commutes with the `G`-action, so it is a `Z[G]`-module
  endomorphism of the free module `Z[G]^d`. Every statement below is about whether this
  endomorphism is injective after tensoring with `Q`, or about its reductions mod finite
  quotients, so it does not depend on how `D` is written (left or right, `g` or `g^-1`).

## 2. Periodic-point lemma: injectivity pins the degree on every finite quotient

**Lemma 2.** Let `tau` be an injective torus automaton on `X_d` over any group `G`.
1. `epsilon(D) in GL_d(Z)`, that is `det epsilon(D) = +-1`.
2. For every finite-index normal subgroup `N`, right multiplication by `p_N(D)` is
   invertible on `Z[G/N]^d`.

*Proof.* Part 1 is part 2 with `N = G`, so we prove part 2.
- `Fix(N) = {x in X_d : n x = x for all n in N}` is the set of configurations constant on
  cosets of `N`. The map `i_N: (T^d)^(G/N) -> X_d`, `y -> y o quotient`, is a
  homeomorphism onto `Fix(N)`.
- `tau` is equivariant, so it maps `Fix(N)` into itself. Write
  `tau_N = i_N^-1 o tau o i_N`, a continuous injective self-map of the closed connected
  manifold `T^(d [G:N])`. By (F2) it is a homeomorphism, so `tau_N^*` is invertible on
  `H^1 = Z[G/N]^d`.
- On `H^1`, `i_N^*` sends `e_(h,i)` to `e_(hN,i)`, so `i_N^* = p_N`. Since
  `tau o i_N = i_N o tau_N`, we get `tau_N^*(p_N xi) = p_N(xi D) = p_N(xi) p_N(D)`, using
  that `p_N` is a ring map. As `p_N` is onto, `tau_N^*` is right multiplication by
  `p_N(D)`. QED.

**Theorem 3 (torus surjunctivity, two cases).**
- (a) If `G` is residually finite, every injective torus automaton on every `X_d` is
  surjective.
- (b) If `Q[G]` has no zero divisors, every injective torus automaton on `X_1 = T^G` (the
  circle alphabet) is surjective.

*Proof of (a).* Suppose `xi D = 0` with `0 != xi in Q[G]^d`. Clearing denominators we may
take `xi in Z[G]^d`. Choose a finite-index normal `N` such that `p_N` is injective on the
finite set `supp(xi)`; this is possible because `G` is residually finite. Then
`p_N(xi) != 0` and `p_N(xi) p_N(D) = p_N(xi D) = 0`, contradicting Lemma 2(2) after
tensoring with `Q`. So `xi -> xi D` is injective on `Q[G]^d`, and Theorem 1 applies.

*Proof of (b).* By Lemma 2(1), `epsilon(D) = +-1`, so `D != 0`. In a domain `xi D = 0`
forces `xi = 0`. Theorem 1 applies.

*Scope of (b).* The hypothesis holds for every group with unique products, in particular
every left-orderable group (standard leading-term argument), and more generally for every
group satisfying Kaplansky's zero-divisor conjecture over `Q`. None of these hypotheses
involves soficity. So (b) is a surjunctivity theorem, for a connected alphabet, proved by
an argument that uses no approximation of the group.

*Why (b) needs no finite model.* Lemma 2(1) only uses the circle of constant
configurations, which exists over every group. The counting on finite models that drives
Gromov–Weiss is replaced by invariance of domain on that circle together with the degree on
finite windows.

## 3. The route and its three independent prerequisites

Route `gottschalk-via-torus-alphabet-degree-transfer`:
`GOT(G) <= C1 and C2(G) and C3(G)`, for all `G`.

- **C1** (`torus-automata-with-regular-degree-are-surjective`): Theorem 1. ESTABLISHED
  here for every group.
- **C2(G)** (`injective-torus-automata-have-regular-degree`): for every `d`, every
  injective torus automaton on `X_d` over `G` has `xi -> xi D` injective on `Q[G]^d`.
  OPEN. With C1 it gives torus surjunctivity `TS(G)`.
- **C3(G)** (`torus-surjunctivity-implies-finite-alphabet-surjunctivity`): if `TS(G)`,
  then `G` is surjunctive on every finite-alphabet full shift. OPEN.

Each prerequisite can fail on its own.
- C1 cannot fail: it is proved.
- C2 fails over `G` exactly when some injective torus automaton has a singular degree
  matrix. That is a topological invariance-of-domain failure for the `G`-shift and is
  independent of any finite-alphabet question.
- C3 fails over `G` if `G` is torus-surjunctive but not finite-alphabet surjunctive.

### 3.1 What is known about C2

- *Residually finite `G`, all `d`*: true (Theorem 3(a)).
- *`Q[G]` a domain, `d = 1`*: true (Theorem 3(b)).
- *Augmentation alone does not suffice at `d = 1` over groups with torsion.* In
  `Z[Z/2 x Z/3]`, with `t` of order 2 and `s` of order 3, put `D = s + s^2 - t`. Then
  `epsilon(D) = 1`, and `xi = (1 - t)(1 - s)` satisfies `xi D = 0`.
  - *Check.* On the component `t = -1` of `Q[Z/2 x Z/3]`, `D` becomes `1 + s + s^2` and
    `xi` becomes `2(1 - s)`, and `(1 - s)(1 + s + s^2) = 0`. On the component `t = 1`,
    `xi` vanishes.
  - *Consequence.* Over a group containing `Z/6`, a proof of C2 must use more than the
    circle of constants. Finite quotients supply more (Lemma 2(2)), but a non-residually-
    finite host has too few of them.
- *Augmentation does suffice at every `d` when `Q[G]` is a semifir*, e.g. `G` free. This uses Cohn's theory of full matrices over semifirs, recalled from memory without a verbatim citation. It is not used in any ESTABLISHED statement.
  - A square matrix over a semifir is regular iff it is full, that is, it does not
    factor through a smaller size.
  - A factorization `D = P Q` through size `d - 1` gives `epsilon(D) = epsilon(P) epsilon(Q)`
    of rank `< d`.
  - So `epsilon(D) in GL_d(Z)` forces `D` full, hence regular. Free groups are residually
    finite anyway, so this adds no new host.
- *Where C2 dies with current tools.* Take `G` non-residually-finite with `d >= 2`, or
  with torsion. Invariance of domain is available only on finite-dimensional invariant
  submanifolds, and the only ones supplied by the group are the `Fix(N)`, `N` of finite
  index. A proof beyond that needs an infinite-dimensional replacement for invariance of
  domain, such as a strict decrease of a mean-dimension-type invariant on proper
  subsystems. Over sofic groups that is sofic mean dimension. Beyond sofic groups no such
  invariant is known.

### 3.2 What is known about C3

- **(O1) No factor maps.** `X_d` is connected, so every continuous map `X_d -> A^G` is
  constant. Information can only move from `A^G` into a torus shift as a subsystem, never
  back out as a factor.
- **(O2) Subsystem transfers are invisible to TS.** Take `iota: A^G -> X_d` equivariant
  and injective, e.g. `(Z/n)^G = ker[n] in T^G`. Let `sigma` be a torus automaton with
  `sigma o iota = iota o tau`.
  - Even if `sigma` is injective, `TS(G)` only makes `sigma` a homeomorphism.
  - A homeomorphism may map the closed invariant set `iota(A^G)` strictly into itself.
    Excluding that is precisely the Gottschalk statement for `tau`.
  - So transfer through subsystems plus TS gives no contradiction, unless one also proves
    `sigma^-1(iota A^G) = iota A^G`, which is equivalent to the conclusion.
- **(O3) Mixed alphabets.** On `A x T^d` the automaton `tau x id` is injective and strict
  whenever `tau` is. Degree acts inside components of window spaces, and the component
  set of a window is `A^F`. So surjectivity on components is the finite-alphabet counting
  problem again. Degree theory handles only the connected factor.
- **Consequence.** C3 is the weak link. Every mechanism for it through equivariant maps
  between the finite shift and a torus shift dies at (O1) or (O2). A proof of C3 needs
  data that is not an equivariant map, e.g. a construction that turns a strict datum
  `(tau, sigma, P)` into a torus automaton whose degree matrix is singular. The candidate
  mechanism is a linearization of the strict datum over `Z` that is invisible mod `p` but
  visible over `Q`. No such construction is known.
- **Tension with linear shadows.** By Pontryagin duality a linear torus automaton `tau_D`
  is injective iff `xi -> xi D` is onto `Z[G]^d`, i.e. `D` has a left inverse. It is onto
  iff that map is injective. So linear TS follows from stable finiteness of `Z[G]`, which
  holds for every group because `C[G]` is stably finite (Kaplansky).
  The linear case of finite-alphabet surjunctivity is stable finiteness of `F_p[G]`, which
  is open. So C3 would carry characteristic-zero information into characteristic `p`. That
  is a reason to expect C3 to be deep or false.
