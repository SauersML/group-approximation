# Decoder fibers: the equivalence, the flip lift, and what a proof still needs

Lane `gk-decoder-fiber`, 2026-09-12. Supports the Cairn nodes
`countable-transitive-decoder-fiber-from-gottschalk`,
`strict-split-pairs-carry-positive-entropy-flip-lifts`,
`xor-lift-of-bernoulli-has-positive-fiber-entropy`,
`ca-bernoulli-lifts-have-zero-fiber-entropy` and
`gottschalk-via-flip-lift-and-zero-fiber-entropy`.

**Gottschalk's conjecture is not decided here.** The proofs below are ordinary
mathematics, not Lean-verified. The examples in Section 4 are classical and no
priority is claimed for them.

## 1. The countable-fiber route is valid and is a restatement

The route `gottschalk-via-countable-transitive-decoder-fiber` argues as follows.
Let `tau` be an injective automaton on `A^G` with memory `M`, and put `H = <M>`.
The rule acts on each left coset of `H` separately, so the induced automaton
on `A^H` is injective. Finite `H` is settled by counting. For infinite `H`, the
open prerequisite `injective-ca-admit-countable-transitive-decoder-fiber` gives a
decoder `sigma` with `sigma tau = id` and a transitive `z` with countable
`sigma^-1(z)`. By `split-decoders-have-generic-cantor-fibers` the decoder is
bijective, so `tau` is surjective on `A^H`, hence on `A^G` coset by coset. Each
step checks. The route is valid.

**Converse.** Suppose every group is surjunctive. Let `G` be finitely generated
and infinite, and `tau` injective. Then `tau` is bijective. Its inverse is
continuous and commutes with the shift, so it is a cellular automaton `sigma`
(Curtis–Hedlund–Lyndon), and `sigma tau = id`. Every fiber of `sigma` is a
singleton. `G` is countable, so a configuration with dense orbit exists: enumerate
the finite patterns and place them on pairwise disjoint translates. Its fiber is
countable. This proves the prerequisite.

So the prerequisite is equivalent to the goal, and the two routes form a cycle.
The forward route is an exact reformulation, not a reduction to something
weaker. What it genuinely adds is the zero-one law: over transitive outputs, a
decoder's fibers are either all singletons or all contain Cantor sets. The rest
of this note develops that law in the form an entropy argument would consume,
and locates where such an argument stops.

## 2. Setting

`G` is a countable group, `A` a finite alphabet with `|A| >= 2`, and `lambda`
the uniform Bernoulli measure on `A^G`. Automata read `x` on `gM` to produce
their value at `g`, and `(h.x)(g) = x(h^-1 g)`. Let `tau, sigma` be automata with
`sigma tau = id` and `R = tau sigma != id`. For finite `G` no such pair exists,
since an injective self-map of a finite set is bijective.

From Sections 2–4 of `research/artifacts/gottschalk-decoder-fibers-2026-09-07.md`
we take the following. Let `N` and `M` be memories of `tau` and `sigma` containing
`e`, and put `K = NM`. There are configurations `u != v` with
`sigma(u) = sigma(v)` and `v = R(u)`, differing exactly on a finite set `D`
with `e in D` and `D ⊆ KK^-1`. Put `H = D M^-1 M`, `W = HN`, `z_0 = sigma(u)`
and `p = z_0|W`. Say `z` *has `p` at `h`* when `z(hk) = p(k)` for all `k in W`.

**Guard lemma.** Let `J ⊆ G` be a set at every point of which `z` has `p`, with
the translates `hW` (`h in J`) pairwise disjoint. Then `tau(z)(hd) = v(d)` for
`h in J` and `d in D`. For every `J' ⊆ J`, the configuration obtained from
`tau(z)` by writing `u(d)` at `hd` for all `h in J'` and `d in D` is again a
preimage of `z` under `sigma`.

The first assertion holds because `tau(z)` on `hH` reads `z` only on
`hHN = hW`, where `z` copies `p`, and `tau(z_0) = R(u) = v`. The second is
Section 4 of that artifact: every output window `gM` meeting a replacement set
`hD` lies inside `hH ⊆ hW`, and these windows are pairwise disjoint.

## 3. The flip lift

**Theorem.** There is a `G`-invariant Borel probability measure `nu` on `A^G`
with the following properties.

1. `sigma_* nu = lambda`, and `R_* nu = tau_* lambda`.
2. `H_nu( x(e) | sigma^-1(Borel) ) >= log 2 / ( |A|^|W| |W W^-1| ) > 0`.
3. `nu` is a factor of an i.i.d. process: `nu = F_* P` for an equivariant Borel
   map `F`, each coordinate of which reads finitely many input coordinates.

*Proof.* Put `Delta = W W^-1`. It is finite, symmetric and contains `e`. Let
`Omega = A^G x [0,1]^G x {0,1}^G` with
`P = lambda (x) Leb^G (x) Bern(1/2)^G`, and let `G` act diagonally by left
translation. For `(z, omega)` set

```text
I(z, omega) = { h in G : z has p at h, and omega(h) < omega(h delta) for all delta in Delta \ {e} }.
```

*Disjointness.* If `h != h'` both lie in `I` and `hW` meets `h'W`, then
`h' in h Delta` and `h in h' Delta`. The label conditions give
`omega(h) < omega(h')` and `omega(h') < omega(h)`, a contradiction. So the
translates `hW`, `h in I`, are pairwise disjoint.

*Equivariance.* `g.z` has `p` at `gh` exactly when `z` has `p` at `h`, and
`(g.omega)(gh delta) = omega(h delta)`. Hence `I(g.z, g.omega) = g I(z, omega)`.

*The map.* Let `F(z, omega, xi)` be `tau(z)` with `u(d)` written at `hd` for
every `h in I(z, omega)` with `xi(h) = 1` and every `d in D`. At most one `h`
touches a given site, so `F` is well defined. It is equivariant. Its coordinate
at `g` reads `z` on the finite set `gN ∪ g D^-1 W`, `omega` on `g D^-1 Delta`,
and `xi` on `g D^-1`, so it is Borel. Put `nu = F_* P`. Then `nu` is invariant,
because `P` is invariant and `F` is equivariant.

*Property 1.* By the guard lemma with `J = I(z, omega)` and
`J' = {h in J : xi(h) = 1}`, `sigma(F(z, omega, xi)) = z` for every input. So
`sigma_* nu = lambda`, and `R(F) = tau(sigma(F)) = tau(z)` gives `R_* nu = tau_* lambda`.

*Property 2.* The joint law of `(x(e), sigma(x))` under `nu` is the law of
`(F(e), z)` under `P`. Conditioning on more information does not increase
entropy, so

```text
H_nu( x(e) | sigma ) = H_P( F(e) | z ) >= H_P( F(e) | z, omega ).
```

The event `J_e = { e in I(z, omega) }` is measurable in `(z, omega)`. On `J_e`
the site `e` lies in `eD`, and no other `h in I` has `e in hD`, since `hW` misses
`W`. The guard lemma gives `tau(z)(e) = v(e)`. So `F(e) = u(e)` when `xi(e) = 1`
and `F(e) = v(e)` when `xi(e) = 0`. Now `xi(e)` is a fair bit independent of
`(z, omega)`, and `u(e) != v(e)`. Given `(z, omega)` on `J_e`, `F(e)` is therefore
uniform on two symbols, and

```text
H_P( F(e) | z, omega ) >= P(J_e) log 2 = |A|^-|W| · |Delta|^-1 · log 2.
```

Here `P(J_e)` factors as `lambda(z has p at e)`, which is `|A|^-|W|`, times the
probability `1/|Delta|` that the first of `|Delta|` i.i.d. uniform labels is the
smallest.

*Property 3* is the construction. QED

The proof also shows more. Given `(z, omega)`, the values `F(h)` for `h in I`
are independent fair choices between `u(e)` and `v(e)`.

**Remark (why this repairs Section 7 of the 2026-09-07 artifact).** There, the
section measure `tau_* lambda` was shown to have point-mass conditionals over
`sigma`, even though every fiber is uncountable. The flip lift is a different
invariant lift of the same output law, and it has positive conditional entropy.
This is the object an entropy argument needs.

**Remark (amenable groups).** Let `(F_n)` be a Følner sequence, and write
`F_n'' = { g : gM ⊆ F_n }` and `F_n' = { h : hD ⊆ F_n }`. Since `sigma(x)|F_n''`
is a function of `x|F_n`,

```text
|F_n| log|A| >= H_nu(x|F_n) = H(sigma(x)|F_n'') + H(x|F_n | sigma(x)|F_n'')
             >= |F_n''| log|A| + |F_n'| P(J_e) log 2.
```

The last term uses the independent flips at the distinct sites `h in I ∩ F_n'`.
Følner sets have `|F_n''|, |F_n'| = |F_n| - o(|F_n|)`, so for large `n` the right
side exceeds the left. Thus no strict pair exists over an amenable group. This
recovers the classical theorem and is a consistency check, not a new result.

## 4. Single-site fiber entropy contradicts nothing

**Example (XOR over `Z`).** Let `G = Z`, `A = Z/2` and
`sigma(x)(n) = x(n) + x(n+1)`. Then `sigma_* lambda = lambda` and
`H_lambda( x(0) | sigma^-1(Borel) ) = log 2`.

*Proof.* For `m >= 0`, the linear map `(Z/2)^[0, m+1] -> (Z/2)^[0, m]`,
`x -> (x(n) + x(n+1))_n`, is onto: choose `x(0)` freely and solve recursively. An
onto linear map between finite vector spaces pushes the uniform measure to the
uniform measure. So every marginal of `sigma_* lambda` on an interval is
uniform, and by invariance the same holds for every finite set. For the
entropy, the involution `x -> x + 1` (add `1` at every site) preserves `lambda`
and commutes with `sigma`. Hence
`P(x(0) = a, sigma(x) in B) = P(x(0) = a + 1, sigma(x) in B)` for every Borel
`B`. So `P(x(0) = 0 | sigma) = 1/2` almost surely, and the conditional entropy is
`log 2`. QED

`Z` is residually finite and amenable, so it is surjunctive. A positive
single-site conditional entropy of an invariant lift of uniform Bernoulli is
therefore not contradictory. The universal zero-entropy statement
`ca-bernoulli-lifts-have-zero-fiber-entropy` is false, and the route combining
it with the flip lift is dead. In the amenable remark the contradiction came
from averaging over Følner sets, not from Property 2 alone.

**Example (Ornstein–Weiss, over `F_2`).** Let `G = F_2 = <a, b>` and
`phi(x)(g) = ( x(g) + x(ga), x(g) + x(gb) )` on `(Z/2)^G`. This pushes the uniform
Bernoulli measure onto the uniform Bernoulli measure on `((Z/2)^2)^G`.

*Proof.* For finite `F ⊆ G` it suffices that the linear map from
`(Z/2)^(F ∪ Fa ∪ Fb)` to `(Z/2)^(F x 2)` is onto, i.e. that its transpose is
injective. Let `c_1, c_2 : F -> Z/2` not both vanish, extended by `0`. The
coefficient of `x(k)` in `sum_g c_1(g)(x(g) + x(ga)) + c_2(g)(x(g) + x(gb))` is

```text
c_1(k) + c_2(k) + c_1(k a^-1) + c_2(k b^-1).
```

Pick `g_0` of maximal reduced length with `(c_1, c_2)(g_0) != 0`.

* If `c_1(g_0) = 1` and `g_0` does not end in `a^-1`, then `k = g_0 a` is longer
  than `g_0`, and so is `k b^-1 = g_0 a b^-1`. The coefficient of `x(k)` is
  `c_1(g_0) = 1`.
* If `c_2(g_0) = 1` and `g_0` does not end in `b^-1`, then `k = g_0 b` has
  coefficient `c_2(g_0) = 1` in the same way.
* Otherwise `(c_1, c_2)(g_0)` is `(1, 0)` with `g_0` ending in `a^-1`, or `(0, 1)`
  with `g_0` ending in `b^-1`. In both cases `g_0 a^-1` and `g_0 b^-1` are longer
  than `g_0`, so the coefficient of `x(g_0)` is `c_1(g_0) + c_2(g_0) = 1`.

QED

On the square alphabet `A = (Z/2)^2`, the automaton `sigma(x_1, x_2) = phi(x_1)`
pushes `lambda` onto `lambda` and ignores `x_2`. Its conditional entropy is
`log 2` at every site. The interior `{ g : g{e, a, b} ⊆ F }` of a ball in
`F_2` is a fixed fraction of the ball smaller than one. So the Følner
inequality of Section 3 has no analogue: the uniform image occupies only the
interior's share of the entropy budget.

## 5. What separates strict defect from reversible growth

Let `O` be the rational algebra of local functions on `A^G`. The pullbacks
`T = tau^*` and `S = sigma^*` are unital equivariant algebra endomorphisms with
`TS = I`, and `E = I - ST`.

**Proposition (algebraic Wold decomposition).** For every `n >= 1`,

```text
O = EO ⊕ S E O ⊕ ... ⊕ S^(n-1) E O ⊕ S^n O,        EO = ker T,
```

and each `S^j` maps `EO` isomorphically onto `S^j E O`. The pair is strict
exactly when `EO != 0`.

*Proof.* `E` and `ST` are complementary idempotents: `(ST)^2 = ST`, and
`E ST = ST E = 0`. Since `T` is onto, `ST O = S O`, so `O = EO ⊕ SO`. Apply the
same splitting inside `SO` through the injective map `S`, and iterate. `TE = 0`
gives `EO ⊆ ker T`. If `Tf = 0` then `Ef = f`, so `ker T ⊆ EO`. Finally `EO = 0`
means `ST = I`, i.e. `R = id`. QED

The defect tower of `split-ca-defects-force-linear-observable-rank`,
`theta(P_0), S theta(P_0), ...`, sits in the shift part `⊕_j S^j E O`. The
reversible growth of `reversible-xor-has-linear-observable-rank` sits entirely
in `S^n O = O`, since there `E = 0`. The invariant that separates the two cases
is the multiplicity `EO = ker T` of the shift part, not the growth of any span
of words. `ker T` is an ideal of `O`. It contains the indicator of every cylinder
missing from the image `X = tau(A^G)`.

**Lemma (kernel is bounded by growth).** Let `H_k` be finite Hilbert orbit
modules as in Section 1 of `research/artifacts/gottschalk-observable-growth-2026-09-07.md`,
with von Neumann dimensions `b_k`, `S H_k ⊆ H_(k+1)` and `T H_(k+1) ⊆ H_(k+2)`.
Then

```text
dim_G ker( T : H_(k+1) -> H_(k+2) ) <= b_(k+1) - b_k.
```

*Proof.* The bounded extensions satisfy `T S = inclusion` on `H_k`, so the
closed range of `T` on `H_(k+1)` contains `H_k`. For a bounded equivariant map
between finite Hilbert `G`-modules, `dim_G ker + dim_G closure(range) = dim_G`
of the source, by polar decomposition. QED

For a strict pair, `ker T` meets every product-closed module in the large ideal
generated by a missing cylinder. A Følner filtration makes the relative growth
at logarithmic scale `o(|F|)`, and that is the classical counting
contradiction in dimension form. Over a nonamenable group the relative growth of
every ball filtration is a positive fraction of `|F|` at logarithmic scale, and
the lemma yields nothing. Section 4's Ornstein–Weiss example shows the same
boundary in entropy form. The last two sentences are heuristic orientation, not
a theorem: no statement here excludes a cleverer filtration or a different
averaging.

**Relation to Kaplansky.** Every separating invariant of this kind with a
universal bound would prove Gottschalk's conjecture. By
`stable-finiteness-failure-refutes-surjunctivity` it would also prove stable
finiteness of `F_p[G]` for every group. That statement is open for nonsofic groups,
and other lanes are attacking it negatively on the binary Leavitt unit group.

## 6. A cellular choice of packing centers, and a decorated embedding

Section 7 of the 2026-09-07 artifact notes that its packing centers are chosen
externally, not by a cellular rule. A marker rule chooses them cellularly.

**Theorem.** Let `G` be infinite and `tau, sigma` a split pair with
`tau sigma != id`, with `D, W, p, u, v` as in Section 2 and `Delta = W W^-1`.
Fix a site `q` and a symbol `a in A`, and for `z in A^G` put

```text
J(z) = { h : z has p at h, z(hq) = a, and for every delta in Delta \ {e}
             it is not the case that (z has p at h delta and z(h delta q) = a) }.
```

1. The translates `hW`, `h in J(z)`, are pairwise disjoint, and `J(g.z) = g J(z)`.
2. `F(z) = tau(z)` with `u(d)` written at `hd` for all `h in J(z)` and
   `d in D` is a cellular automaton with `sigma F = id`. If `q` avoids the finite
   set `W ∪ Delta^-1 W`, then `F != tau`. Varying `q` gives infinitely many
   distinct cellular sections of `sigma`. A bijective `sigma` has exactly one
   section, its inverse.
3. The closed invariant subshift
   `Y = { (z, xi) in (A x {0,1})^G : xi(h) = 0 for all h not in J(z) }` embeds
   injectively and equivariantly into `A^G` through
   `Phi(z, xi) = tau(z)` with `u(d)` written at `hd` for `h in J(z)` with
   `xi(h) = 1`. Moreover `sigma Phi(z, xi) = z`, `Phi(z, 0) = tau(z)`, and
   `Y != A^G x {0}`.

*Proof.* (1) If `h` and `h' = h delta` both lie in `J(z)` with `delta != e`, the
condition at `h` forbids exactly what `h'` satisfies. So `J(z)` contains no two
points differing by an element of `Delta \ {e}`. If `hW` meets `h'W` then
`h' in h Delta`, so the translates are disjoint. Membership of `h` reads `z` on
the finite set `hW ∪ {hq} ∪ ⋃_delta (h delta W ∪ {h delta q})`, and every clause is
translation invariant.

(2) `F` is well defined because the replacement sets are disjoint, and it is
local and equivariant by (1). The guard lemma with `J = J'` gives `sigma F = id`.
For `F != tau`, prescribe `z = p` on `W`, `z(q) = a`, and `z(delta q) != a` for
`delta in Delta \ {e}`. These sites are pairwise distinct and none lies in `W`,
by the choice of `q`. Then `e in J(z)`, so `F(z)(e) = u(e) != v(e) = tau(z)(e)`.
Choose `q_1, q_2, ...` recursively, each outside the finite set of sites used
by the earlier ones together with `W ∪ Delta^-1 W`. For `i < j`, prescribing
`z(q_j) != a` in addition keeps `e in J_(q_i)(z)` and removes `e` from
`J_(q_j)(z)`, so `F_(q_i) != F_(q_j)`. If `sigma` is bijective, `sigma F = id`
forces `F = sigma^-1`.

(3) `Y` is closed and invariant because its defining condition is local and
equivariant. `Phi` is continuous and equivariant for the same reason, and
`sigma Phi(z, xi) = z` by the guard lemma. For injectivity, `y = Phi(z, xi)`
determines `z = sigma(y)`, hence `J(z)`. For `h in J(z)` only the flip at `h`
touches the site `h`, and `tau(z)(h) = v(e)`, so `xi(h) = 1` exactly when
`y(h) = u(e)`. Off `J(z)`, `xi` vanishes by definition. Finally `(z, xi)` with
`e in J(z)` and `xi = 1` at `e` only lies in `Y \ (A^G x {0})`. QED

**Consequences and limits.** `Phi` restricts to `tau` on `A^G x {0}`. The full
shift `A^G` therefore contains an equivariant injective image of a subshift that
strictly contains a copy of itself, with one extra bit at a cellularly chosen
independent set of guard occurrences. Over an amenable group this is
contradictory, since topological entropy is monotone under injective factor
maps and `h(Y) >= log|A| + P(e in J) log 2`. For a general group no such
monotone invariant is known. The decorations vanish on constant configurations,
so this embedding does not contradict anything on fixed points. It also does not
contradict the 2026-09-07 remark that a full larger shift cannot embed.

## 7. Status

* Established: the converse route (`countable-transitive-decoder-fiber-from-gottschalk`),
  the flip lift (`strict-split-pairs-carry-positive-entropy-flip-lifts`), the
  XOR counterexample (`xor-lift-of-bernoulli-has-positive-fiber-entropy`), and the
  marker sections with the decorated embedding
  (`strict-split-decoders-have-infinitely-many-sections`).
* Refuted: `ca-bernoulli-lifts-have-zero-fiber-entropy`. The route
  `gottschalk-via-flip-lift-and-zero-fiber-entropy` is dead.
* Open, and equivalent to the goal: `injective-ca-admit-countable-transitive-decoder-fiber`.
  A proof along this line needs an averaging principle for the conditional
  entropy of lifts over a split decoder that survives nonamenable boundaries.
  Only the existence of the section `tau` distinguishes a strict split pair
  from the Ornstein–Weiss situation, so the principle must use `tau`.
