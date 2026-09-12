# What property (T) and superrigidity give the Bernoulli dynamics of a strict automaton

Lane `gk-p-inf-kazhdan`, 2026-09-12. Supports the Cairn claims
`fg-infinite-simple-groups-are-minimally-almost-periodic`,
`popa-bernoulli-cocycle-superrigidity`,
`kazhdan-map-bernoulli-finite-extensions-are-trivial` and
`strict-pair-flip-lifts-are-relatively-weakly-mixing`, and Attempts entries on
`bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups` and
`fg-simple-kazhdan-groups-are-surjunctive`.

**Question.** On a finitely generated infinite simple Kazhdan group, can spectral gap,
strong ergodicity, cocycle or orbit-equivalence superrigidity, or the absence of finite
quotients bound how far a strict automaton pushes the uniform Bernoulli measure? Can they
bound Bernoulli Rokhlin entropy from below?

**Answer.** No, and the reason can be stated exactly.

* **The image action.** An injective automaton is a measure conjugacy onto its image, so
  every invariant of the image action agrees with Bernoulli. That is already recorded in
  Section 3.2 of `simple-kazhdan-hosts-2026-09-12.md`. Base blindness of Koopman, cost and
  weak-equivalence data is the business of the sibling lanes `gk-p-inf-wild` and
  `gk-p-inf-cost`.
* **What superrigidity does see.** A strict pair also creates extensions of the Bernoulli
  base. Cocycle superrigidity forces triviality of every *finite* extension of that base
  (Theorem 4.1), and under a second import every *compact* one (Remark 4.3).
* **What a strict pair actually produces.** The extensions every strict pair carries, the
  flip lifts, are relatively weakly mixing: they are relative factors of i.i.d. product
  extensions (Proposition 5.1). Such extensions exist over every countable group and carry
  no cocycle into a compact group, so superrigidity can never contradict a strict pair.
* **Counting.** In-group partition counting certifies maximal Bernoulli Rokhlin entropy
  exactly on amenable groups. Property (T) makes every generating set expand, which caps the
  certified bound on windows that contain large balls (Section 5.4).

## 1. Setting

`G` is a countable group, `A` a finite alphabet with `q = |A| >= 2`, and `lambda` the
uniform product measure on `A^G`, with `(g.x)(h) = x(g^-1 h)`. A strict split pair is a pair
of cellular automata `tau, sigma` with `sigma o tau = id` and `tau o sigma != id`.

All actions are measure preserving on standard probability spaces. An *extension*
`pi: (Z, m) -> (X, mu)` is a `G`-equivariant measure-preserving factor map. The relative
product `Z x_X Z` is `(Z x Z, integral m_x (x) m_x dmu(x))`, where `m = integral m_x dmu` is
the disintegration of `m` over `pi`. The extension is *relatively weakly mixing* when both
`Z` and `Z x_X Z` are ergodic.

## 2. Minimal almost periodicity of simple hosts

**Lemma 2.1.** Let `G` be a finitely generated infinite simple group, and `rho: G -> K` a
homomorphism into a compact group. Then `rho` is trivial.

*Proof.* Suppose `rho(g) != 1`.
* By Peter–Weyl there is a finite-dimensional continuous unitary representation
  `pi: K -> U(d)` with `pi(rho(g)) != 1`.
* `pi o rho (G)` is a finitely generated subgroup of `GL_d(C)`, hence residually finite by
  Malcev's theorem.
* `pi o rho` is nontrivial and `G` is simple, so `pi o rho` is injective. Then `G` is
  residually finite.
* An infinite residually finite group has a proper nontrivial normal subgroup of finite
  index, and a simple group has none. Contradiction. QED

In particular such a `G` has no nontrivial finite quotient and no nontrivial
finite-dimensional unitary representation. This covers the Leavitt unit group `R^x`, the
scalar quotients of `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`, and every host of
`countable-group-embeds-in-fg-simple-kazhdan-group`. It does not cover groups that are not
simple, such as the Fournier–Facio group, whose m.a.p. is recorded separately.

## 3. The import: Popa's cocycle superrigidity

**Theorem 3.1** (Popa, *Cocycle and orbit equivalence superrigidity for malleable actions of
w-rigid groups*, Invent. Math. 170 (2007) 243–295, Theorem 0.1). Let `G` be a countable group
containing an infinite normal subgroup `H` such that `(G, H)` has the relative property (T);
for example, `G` infinite with property (T) and `H = G`. Let `G ↷ (X, mu)` be an s-malleable
action whose restriction to `H` is weakly mixing; the standard example is the Bernoulli action
`([0,1], Leb)^G` with diffuse base. Let `V` be a closed subgroup of the unitary group of a
separable II_1 factor, a class `U_fin` containing every countable discrete group. Then every
measurable cocycle `c: G x X -> V` is cohomologous to a homomorphism `G -> V`.

*Trust surface.* Statement-level import. The theorem number and the exact definitions of
s-malleability and of `U_fin` were not re-verified against the PDF in this lane. Theorem 4.1
below uses only finite targets `V`, and only the diffuse-base Bernoulli action.

*Scope correction (2026-09-12).* The first version of this section stated Theorem 3.1 for
Bernoulli actions with an arbitrary nontrivial base. gk-vf-positive (Section 12 of
`gk-vf-positive-verification-2026-09-12.md`) flagged that the abstract-level statement concerns
s-malleable actions, so coverage of atomic bases such as `A^G` would have to be read at source.
Step 0 of the proof of Theorem 4.1 removes the need for it.

## 4. Finite extensions of Bernoulli over Kazhdan groups without finite quotients

**Theorem 4.1.** Let `G` be an infinite countable group with property (T) and no nontrivial
homomorphism to a finite group, and `(X, mu) = (X_0, mu_0)^G` a Bernoulli action with nontrivial
standard base, atomic or not. Let `pi: (Z, m) -> (X, mu)` be an extension with `(Z, m)` ergodic,
such that for `mu`-almost every `x` the conditional measure `m_x` is supported on a finite set.
Then `pi` is an isomorphism mod null sets.

*Proof.*
0. *Base reduction (added 2026-09-12 after gk-vf-positive, Section 12).* Let `(Y, nu) = ([0,1], Leb)^G`.
   The space `(X_0 x [0,1], mu_0 (x) Leb)` is a standard probability space without atoms, hence
   isomorphic to `([0,1], Leb)`. Applied coordinatewise, this makes `(X x Y, mu (x) nu)`
   equivariantly isomorphic to `([0,1], Leb)^G`. Let `G` act diagonally on `Z x Y`, and put
   `pi~ = pi x id`.
   * `pi~` is an extension of `X x Y` whose conditional measure at `(x, y)` is `m_x (x) delta_y`.
     So it is finite-to-one with the same multiplicity function.
   * `Z x Y` is ergodic: `Y` is a Bernoulli action of an infinite group, hence mixing and so weakly
     mixing, and an ergodic action times a weakly mixing one is ergodic.
   * A finite-to-one extension is an isomorphism mod null sets exactly when its multiplicity is `1`
     almost everywhere. So `pi~` is an isomorphism exactly when `pi` is.

   So it suffices to treat the base `([0,1], Leb)^G`. That action is s-malleable and weakly mixing,
   so Theorem 3.1 applies to it in its abstract-level form. Assume this base from now on.
1. *Constant multiplicity.* Put `n(x) = |supp m_x|`. It is measurable, and invariant because
   `g_* m_x = m_{gx}`. `(X, mu)` is ergodic, so `n(x) = n` almost everywhere. Let `Z_1` be the
   conull invariant set of points `z` with `m_{pi(z)}({z}) > 0`.
2. *Sheets.* `pi|Z_1` is a countable-to-one Borel map with finite fibres. A Borel linear order
   on `Z_1` (Lusin–Novikov uniformization) enumerates each fibre. This gives a Borel
   isomorphism `Z_1 -> X_1 x {1, ..., n}` over a conull invariant `X_1`.
3. *Cocycle.* In these coordinates `g.(x, i) = (gx, c(g, x)(i))`, where
   `c: G x X_1 -> Sym(n)` is a measurable cocycle. The cocycle identity follows from the action
   axioms.
4. *Superrigidity.* `Sym(n)` is finite, and the base is the diffuse-base action of step 0, so
   Theorem 3.1 applies. There are a homomorphism `rho: G -> Sym(n)` and a measurable
   `f: X_1 -> Sym(n)` with `c(g, x) = f(gx) rho(g) f(x)^-1` for almost every `x` and every `g`.
   The image of `rho` is a finite quotient of `G`, so `rho = 1`.
5. *Untwisting.* `Phi(x, i) = (x, f(x)^-1(i))` satisfies
   `Phi(g.(x, i)) = (gx, f(gx)^-1 c(g, x)(i)) = (gx, f(x)^-1(i))`. So `Phi` conjugates the
   action to `g.(x, j) = (gx, j)`.
6. *Ergodicity.* The `n` sheets `X_1 x {j}` are invariant in the new coordinates. Each has
   positive measure, since every point of `supp m_x` has positive conditional mass. `(Z, m)` is
   ergodic, so `n = 1`, and `pi` is injective on a conull invariant set. QED

**Corollary 4.2.** The conclusion holds over every finitely generated infinite simple Kazhdan
group, in particular over `R^x` (`binary-leavitt-unit-group-is-simple` and the Kazhdan property
from `rank-twelve-leavitt-simple-non-mf`), and over every host of
`countable-group-embeds-in-fg-simple-kazhdan-group`. Lemma 2.1 is not needed here: an infinite
simple group has no nontrivial finite quotient.

**Remark 4.3 (compact extensions; not landed as a node).** Theorem 3.1 also accepts compact
targets. By the Mackey–Zimmer representation, a compact ergodic extension is a homogeneous skew
product `X x_c K/L` with a cocycle `c` into a compact group `K`. The same untwisting, with
Lemma 2.1 in place of "no finite quotients", then shows that over a Kazhdan group with no
nontrivial homomorphism to a compact group, every ergodic compact extension of a Bernoulli action
is trivial. Hence every ergodic extension is relatively weakly mixing. The base reduction of step 0
applies verbatim. This adds Zimmer's structure theorem as a second trust surface, and needs compact
groups in `U_fin`, which this lane did not re-verify. Nothing below depends on it.

## 5. The sharp test on strict automata

### 5.1 The image action is invisible

`tau: (A^G, lambda) -> (A^G, tau_* lambda)` is a measure conjugacy. So:
* spectral gap and strong ergodicity agree;
* orbit equivalence class, cocycle superrigidity and OE superrigidity agree;
* weak containment class and Rokhlin entropy agree.

Only the coordinate process differs: `tau_* lambda` misses a cylinder. No invariant of the
action, and in particular no conclusion of Theorem 3.1 about cocycles of the image action, can
separate the two measures.

### 5.2 The decoder extensions are relatively weakly mixing

For a strict split pair, the flip lift of `strict-split-pairs-carry-positive-entropy-flip-lifts`
is `nu = F_* P`. Here:
* `Omega = A^G x [0,1]^G x {0,1}^G`, with `P = lambda (x) Leb^G (x) Bern(1/2)^G`;
* `F` is equivariant;
* `sigma o F = pr_1`;
* `H_nu(x(e) | sigma) > 0`.

**Proposition 5.1.** `sigma: (A^G, nu) -> (A^G, lambda)` is a relatively weakly mixing extension.
It is an intermediate factor of the product extension `pr_1: (Omega, P) -> (A^G, lambda)`, whose
fibre process `Y = ([0,1] x {0,1})^G` is i.i.d. and independent of the base.

*Proof.*
* *Intermediate factor.* `sigma o F = pr_1`, so `(A^G, nu)` sits between `Omega` and
  `(A^G, lambda)`.
* *The product extension.* `Omega x_X Omega = X x Y x Y`, with `X = (A^G, lambda)`. The
  Bernoulli action on `Y x Y` is mixing, hence weakly mixing. The product of an ergodic system
  with a weakly mixing one is ergodic, so `X x Y x Y` is ergodic. `Omega` is ergodic too, being
  a Bernoulli action of an infinite group.
* *Passing to the factor.* The disintegration of `P` over `X` pushes forward under `F` to the
  disintegration of `nu`. So `(A^G, nu) x_X (A^G, nu)` is a factor of `Omega x_X Omega`, hence
  ergodic. `(A^G, nu)` is ergodic as a factor of `Omega`. QED

The extension has positive conditional entropy, so it is not an isomorphism. It is not a finite
or compact extension either: those have zero relative entropy, and by Theorem 4.1 (resp. Remark
4.3) they are trivial over Kazhdan hosts anyway.

### 5.3 Consequences for the Kazhdan attack

* **Superrigidity is consistent with every strict pair, over every host.** Its content for
  extensions of the Bernoulli base is triviality of finite and compact parts. Every strict pair
  carries positive-entropy extensions of the Bernoulli base that are relatively weakly mixing,
  relative factors of i.i.d. product extensions. They exist over every countable group, and they
  carry no cocycle into a finite or compact group.
* **Where a lower bound would have to act.** What a strict pair adds over the Bernoulli base,
  beyond conjugacy-invariant data, is relative entropy of a relatively weakly mixing extension
  (`H_nu(x(e) | sigma) > 0`). A proof of INF on a Kazhdan host must control relative Rokhlin
  entropy of such extensions. Spectral gap, strong ergodicity and superrigidity are orthogonal
  to it.
* **Design filter for the negative lanes.** Over `R^x` and every finitely generated simple
  Kazhdan host, no strict design can use a finite-to-one measurable structure over the Bernoulli
  base. Theorem 4.1 collapses any ergodic invariant lift on which a decoder is finite-to-one.
  Every lift must be infinite-to-one with positive relative entropy.

### 5.4 In-group counting certifies INF exactly on amenable groups

Let `C` be the canonical one-site partition of `(A^G, lambda)`, and `P` a countable generating
partition. For `eps > 0` choose a finite `F` with `H(C | P^F) <= eps`, where
`P^F = vee_{f in F} f.P`. For every finite `F'`, the translates `g.C` (`g in F'`) are
independent and each is `eps`-determined by `P^(gF)`. So

    |F'| log q = H(C^(F')) <= H(P^(F'F)) + |F'| eps <= |F'F| H(P) + |F'| eps,

and hence

    H(P) >= (log q - eps) * sup_{F'} |F'| / |F'F|.

* **Amenable groups.** The supremum equals `1` for every finite `F` exactly when `G` is amenable
  (Følner). Then `H(P) >= log q - eps` for all `eps`, which recovers maximal Bernoulli Rokhlin
  entropy.
* **Kazhdan groups.** Let `S` be a finite generating set containing `e`. An infinite group with
  property (T) is nonamenable, so there is `c > 0` with `|ES| >= (1 + c)|E|` for every finite `E`.
  Iterating, `|E S^r| >= (1 + c)^r |E|`. If `F` contains a translate `gS^r`, then
  `|F'F| >= |F'g S^r| >= (1 + c)^r |F'|`, and the certified bound is at most `(1 + c)^-r log q`.
  *Scope (tightened 2026-09-12 after gk-vf-positive, Section 12).* The window `F` that approximates
  `C` to within `eps` need not contain balls. So this is not a proved decay along windows: it caps
  what the mechanism certifies on windows that contain a translate of `S^r`.

Stronger expansion from property (T) therefore makes this mechanism worse. The known way around
expansion is to count on finite models (sofic entropy), which a nonsofic host does not have.

## 6. Where the lane stops

* No tool in the (T)/superrigidity family yields a positive lower bound on Bernoulli Rokhlin
  entropy on a nonsofic host.
* The remaining knob is relative entropy of relatively weakly mixing extensions of the Bernoulli
  base, i.e. a relative form of INF. No mechanism for it is known either.
