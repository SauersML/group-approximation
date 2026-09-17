# Denying homogeneity: surjunctivity of invariant random subgroups (a-gs-heretic, 2026-09-17)

Lane: paradigm/decomposition, heretic role on `gottschalk-surjunctivity-conjecture`.
Nodes written from this artifact:

- `atomic-irs-strict-designs-are-nonsurjunctive-quotients` (Section 3, proved)
- `co-sofic-irs-carry-no-strict-design` (Section 4, proved)
- `free-group-irs-carry-no-strict-design` (open, a strengthening of the goal)
- `non-co-sofic-free-group-irs-carry-no-strict-design` (open, the only hole of the strengthening)
- `some-free-group-irs-carries-a-strict-design` (open, counterexample program)
- `irs-strict-designs-yield-nonsurjunctive-groups` (open, the transfer step)
- `some-group-is-not-surjunctive` (open program root, negation of the goal)
- routes `gottschalk-via-irs-surjunctivity`, `irs-surjunctivity-via-co-sofic-split`,
  `nonsurjunctive-group-via-irs-strict-design`, and the two proof routes.

No step of this artifact proves or refutes the goal. It is a decomposition.

## 1. Three unstated assumptions of the HOT families

The two hot families on the root are the entropy and measure family (Bernoulli
preservation, Rokhlin entropy, the random-order transport identity) and the local
designs family (table groups, hinge words, memory holonomy). Both assume the
following without saying so.

**A1. Invariant accounting.** Every counting or entropy identity is balanced by an
invariant measure or the mass-transport principle.

*Denial.* Use nonsingular, non-unimodular accounting.
*Where it dies.* Already calibrated. `end-fixing-tree-symmetries-carry-strict-automata`
gives a strict automaton on a transitive amenable non-unimodular space, and
`injective-ca-random-order-transport-identity` records that its transport has ratio 2
there. Dropping A1 gives counterexamples to the theorem-shaped statements, not a
route. So A1 is a genuine prerequisite of any positive proof.

**A2. Homogeneity.** The index set is a group acting on itself, so every site sees
the same forward table and the same reverse table. Every HOT invariant is a root
statistic transported by translation.

*Denial.* Keep A1 but drop A2. Replace the group by the Schreier graph of an
invariant random subgroup (IRS) of a free group. That is a unimodular random network
whose local tables change from site to site. This is the lane developed below.

**A3. Exactness.** The forward identity holds at every site with error zero.

*Denial.* Allow a positive density `eps` of forward-bad sites and bound the density
`delta` of reverse-bad sites by `C eps`.
*Where it dies alone.* On a vertex-transitive index set, forward-good is all or
nothing, so `eps` is 0 or 1 and the inequality has no content. A3 can only be denied
after A2. Once A2 is denied it is exactly the engine of Section 4: the inequality
`delta <= C eps` is a closed convex condition on IRS space.

## 2. Setting

Let `Gamma = F_r` be free on `a_1..a_r`, and let `d_k` be the size of the radius-`k`
ball of the `2r`-regular tree. For `H <= Gamma` let `X_H = H\Gamma` carry the right
action `(H g).w = H g w`. Its labelled Schreier graph has edges `v -> v.a_i`. The
stabilizer of `v = H g` is `g^-1 H g`, and `v.w = v.w'` iff `w w'^-1` lies in that
stabilizer. `B_k(v)` is the induced labelled subgraph on the vertices at distance at
most `k`, rooted at `v`. It has at most `d_k` vertices, and its isomorphism type is
determined by which words of length at most `2k+1` lie in `Stab(v)`. So every
"shape of `B_k(v)`" event is clopen in `Sub(Gamma)`.

An **IRS** is a conjugation-invariant Borel probability measure `mu` on `Sub(Gamma)`.
The rooted graph `(X_H, H)` with `H ~ mu` is the associated random rooted network.
The root `H g` of `(X_H, H g)` has stabilizer `g^-1 H g`, which again has law `mu`.

**Shape-dependent automata.** A radius-`R` automaton on Schreier graphs over a finite
alphabet `A` is a function `F` from isomorphism types of `A`-coloured rooted labelled
balls of radius `R` to `A`. It acts on every `X_H` by `tau x(v) = F(B_R(v), x|B_R(v))`.
It commutes with every label-preserving automorphism of `X_H`. A **design** is a pair
`(tau, sigma)` of such automata, with radii `R_tau` and `R_sigma`. Put
`r = R_tau + R_sigma`.

- `v` is **forward-good** if `sigma(tau x)(v) = x(v)` for all colourings `x` of `B_r(v)`.
- `v` is **reverse-bad** if some colouring `p` of `B_r(v)` has `tau(sigma p)(v) != p(v)`.

Both are conditions on the shape of `B_r(v)`, hence clopen in `Sub(Gamma)`. Write
`eps_D(mu) = mu(root forward-bad)` and `delta_D(mu) = mu(root reverse-bad)`. They are
continuous affine functionals of `mu`.

**Lemma 2.1 (one graph).** On a fixed `X = X_H` these are equivalent:

- (a) `sigma tau = id` on `A^X` and `tau` is not surjective;
- (b) every vertex is forward-good and some vertex is reverse-bad.

*Proof.* (a) gives forward-good everywhere by evaluating on configurations extending
a colouring of `B_r(v)`. If no vertex were reverse-bad then `tau sigma = id`, and
`tau` would be surjective. Conversely, forward-good everywhere is `sigma tau = id`.
If `v` is reverse-bad with witness `p`, extend `p` to `y`. Then `tau sigma y(v) != y(v)`.
But `y = tau x` would give `tau sigma y = tau sigma tau x = tau x = y`. QED

**Definition.** `mu` **carries a strict design** if for some design
`eps_D(mu) = 0` and `delta_D(mu) > 0`. By invariance, `eps_D(mu) = 0` makes every
vertex of `mu`-a.e. `X_H` forward-good, since `Gamma` is countable. By Lemma 2.1, `mu`
then gives positive probability to Schreier graphs over which `tau` is injective and
not surjective, with a local left inverse `sigma`. Conversely, if `mu` a.s. has a
local left inverse everywhere and positive probability of non-surjectivity, then
`mu` carries the design.

**Lemma 2.2 (strict pairs).** If a group `Q` is not surjunctive, then some cellular
automaton `tau_Q` over `Q` is injective and not surjective and has a cellular left
inverse `sigma_Q`.

*Proof.* `tau_Q` is a homeomorphism onto its closed image `Y`. The map
`y -> tau_Q^-1(y)(1)` is continuous on the compact set `Y`, so it depends only on `y`
restricted to a finite window `M_Q`. Extend its rule arbitrarily to `A^(M_Q)`. The
automaton `sigma_Q` with this rule satisfies `sigma_Q tau_Q = id` by equivariance. QED

**Lemma 2.3 (locality).** A group is surjunctive iff all of its finitely generated
subgroups are.

*Proof.* One direction is `surjunctivity-passes-to-subgroups`. Conversely, let `tau`
over `G` be injective and not surjective, with memory `S`, and let `K = <S>`. As in
the proof of `surjunctivity-passes-to-subgroups`, `tau` acts on each factor of
`A^G = prod_(cosets gK) A^(gK)` as one copy of the restricted automaton `tau_K`.
Injectivity of `tau` gives injectivity of `tau_K`. If `tau_K` were surjective, `tau`
would be surjective factor by factor. So the finitely generated `K` is not
surjunctive. QED

## 3. The atomic case is exactly the group problem

Let `mu` be an ergodic IRS with an atom `H`. All conjugates of `H` have the same mass,
so the conjugacy class is finite, and ergodicity makes `mu` uniform on it. Hence
`N = N_Gamma(H)` has finite index `k` and is finitely generated (Schreier), and
`Q = N/H` is finitely generated.

**Theorem 3.1.** `mu` carries a strict design iff `Q = N_Gamma(H)/H` is not
surjunctive. In particular, for normal `H`, `delta_H` carries a strict design iff
`Gamma/H` is not surjunctive.

Because `mu` is uniform on the conjugates `g^-1 H g`, and all these Schreier graphs are
isomorphic to `X = X_H`, with the root running over all vertices,
`mu` carries a strict design iff `X` carries a pair as in Lemma 2.1(a).

Choose coset representatives `Gamma = disjoint union of N g_i`, `i = 1..k`. Every
vertex is uniquely `H n g_i` with `nH in Q`. This is the bijection `X = Q x {1..k}`.

**(=>)** `Q` acts on `X` from the left by `nH . H g = H n g`. This is well defined
because `nH = Hn`, and it commutes with the right action, so it acts by
label-preserving automorphisms. It is free, since `H n g = H g` iff `n in H`. In the
coordinates above it is `q'.(q, i) = (q' q, i)`. So
`A^X = (A^k)^Q` with `Q` acting by left translation. A strict pair `(tau, sigma)` on
`X` commutes with this action. The map `tau` is continuous for the product topology,
which the bijection of index sets preserves. By the Curtis-Hedlund-Lyndon theorem
over arbitrary groups, `tau` is a cellular automaton over `Q` with alphabet `A^k`. It
is injective and not surjective. So `Q` is not surjunctive.

**(<=)** Let `tau_Q` and `sigma_Q` be as in Lemma 2.2, over the alphabet `B`, with
`tau_Q z(q) = F((z(q s))_(s in S_Q))` and similarly `sigma_Q`. For `s in S_Q ∪ M_Q`
fix a lift `m_s in N`, and put `w_(i,s) = g_i^-1 m_s g_i`. At `v = H n g_i`,

```text
v . w_(i,s) = H n m_s g_i ,
```

which corresponds to `(q s, i)`. This does not depend on the representative `n` or
the lift `m_s`. Replacing `m_s` by `m_s h` with `h in H` changes nothing, because
`(n m_s) h (n m_s)^-1 in H`.

The layer `i` of `v` is detected by its shape. `v` lies in layer `i` iff
`Stab(v) = g_i^-1 H g_i`, and the `k` conjugates are distinct. Finitely many words
separate them, so the shape of a ball of some radius `R_0` determines `i`. Define

```text
tau x(v)   = F( (x(v . w_(i,s)))_(s in S_Q) ),   i = layer of v,
sigma y(v) = G( (y(v . w_(i,s)))_(s in M_Q) ).
```

These are shape-dependent automata of finite radius. On layer `i`, with
`x_i(q) = x(q, i)`, they act as `tau_Q` and `sigma_Q`. So `sigma tau = id`, and `tau`
is not surjective, since it fails on any single layer. QED

**Corollary 3.2.** Gottschalk's conjecture is equivalent to: for every `r`, no atomic
ergodic IRS of `F_r` carries a strict design.

*Proof.* If `G` is not surjunctive, Lemma 2.3 gives a finitely generated
non-surjunctive `K = F_r/N`, and Theorem 3.1 gives a strict design on `delta_N`.
Conversely a strict design on an atomic ergodic IRS gives the non-surjunctive group
`Q`. QED

**Remark (IRS-rigid hosts add nothing).** Let `G = F_r/N`. The IRS of `F_r`
supported on subgroups containing `N` are pull-backs of the IRS of `G`. If `G` has
only the trivial ergodic IRS, as the binary Leavitt unit group does by
`leavitt-invariant-random-subgroups-are-trivial-mixtures`, those are mixtures of
`delta_N` and `delta_(F_r)`. `delta_(F_r)` gives the one-vertex graph, over which
every injective map is surjective. So on such hosts the IRS strengthening says
nothing beyond surjunctivity of `G` itself.

## 4. Co-sofic IRS carry no strict design

Call `mu` **co-sofic** if it lies in the weak-* closure of the IRS `mu_X`, where
`X` is a finite `Gamma`-set and `mu_X` is the law of `Stab(o)` for `o` uniform in `X`.

**Theorem 4.1.** For every design `D` over the alphabet `A` there is

```text
C_D = d_(R_tau) + d_(2r) |A|^(d_r) ln|A|
```

such that every co-sofic IRS `mu` satisfies `delta_D(mu) <= C_D eps_D(mu)`.
Consequently no co-sofic IRS carries a strict design.

*Proof.* Take a finite `Gamma`-set `X` with `|X| = N`.
Let `G` be its forward-good set and `Bad` its reverse-bad set, so that
`|X \ G| = eps N` and `|Bad| = delta N`.

*Lower bound.* For `v in G`, `x(v) = sigma(tau x)(v)`. The map
`tau(A^X) -> A^G`, `y -> (sigma y)|G`, is onto. Every `z in A^G` extends to some
`x`, and then `(sigma tau x)|G = z`. So `|tau(A^X)| >= |A|^((1-eps)N)`.

*Excluded patterns.* Let `v in Bad` with witness `p_v` on `B_r(v)`, and suppose
`B_(R_tau)(v) ⊆ G`. For `y = tau x`, `sigma y = x` on `B_(R_tau)(v)`, so
`tau sigma y(v) = tau x(v) = y(v)`. Hence `y|B_r(v) != p_v`. The vertices of `Bad`
failing `B_(R_tau)(v) ⊆ G` lie within distance `R_tau` of `X \ G`, and there are at
most `eps N d_(R_tau)` of them. Let `D` be the rest, so `|D| >= (delta - eps d_(R_tau)) N`.
Choose greedily `D' ⊆ D` with pairwise distances `> 2r`. Each choice removes at most
`d_(2r)` candidates, so `|D'| >= |D| / d_(2r)`, and the balls `B_r(v)` for `v in D'`
are disjoint. Therefore

```text
|tau(A^X)| <= |A|^N prod_(v in D') (1 - |A|^(-|B_r(v)|)) <= |A|^N (1 - |A|^(-d_r))^|D'| .
```

*Combine.* Using `ln(1-u) <= -u`,

```text
(1-eps) N ln|A| <= N ln|A| - |D'| |A|^(-d_r),
```

so `|D'| <= eps N |A|^(d_r) ln|A|`. Then
`delta - eps d_(R_tau) <= d_(2r) |D'| / N <= eps d_(2r) |A|^(d_r) ln|A|`.
This is `delta_D(mu_X) <= C_D eps_D(mu_X)`.

Both sides are continuous affine functionals of `mu`, because the events are clopen.
So the set of IRS satisfying the inequality is closed and convex and contains every
`mu_X`. It therefore contains every co-sofic IRS. If `eps_D(mu) = 0` then
`delta_D(mu) = 0`, so `mu` carries no strict design. QED

For normal `N`, `delta_N` is co-sofic exactly when `F_r/N` is sofic. With
Theorem 3.1 this recovers Gromov-Weiss for finitely generated sofic groups. That
remark is not used by any node.

## 5. The decomposition

```text
gottschalk  <=  L1 (Theorem 3.1, proved)  +  P1 : no IRS of any F_r carries a strict design
P1          <=  L2 (Theorem 4.1, proved)  +  P1': no non-co-sofic IRS carries a strict design
not gottschalk  <=  C1 : some IRS of some F_r carries a strict design
                  +  C2 : a strict design on an IRS yields a non-surjunctive group
```

- **P1** is a strengthening in form. By Corollary 3.2 its atomic part is the goal, so
  P1 implies the goal. C2 is equivalent to "the goal implies P1", so P1 is equivalent
  to the goal exactly when C2 holds.
- **P1'** is the only open part of P1. By L2, C1 is exactly the negation of P1'.
- **C1** can fail on its own (P1 true) without deciding the goal.
- **C2** can fail on its own: a non-co-sofic nonatomic IRS might carry a strict design
  while every group is surjunctive.

**What C1 would kill.** Any argument that uses only root-ball statistics of the index
set plus the mass-transport principle holds verbatim on unimodular IRS Schreier
graphs with shape-dependent rules. Such an argument proves P1'. A witness for C1
would therefore rule out every such argument, a precise obstruction to the
entropy-measure family, before any group counterexample is known. This transfer is
a program statement, not a proved claim. Checking HOT tools one by one for IRS
robustness is listed as a `need` on the bus.

**What L2 kills on the counterexample side.** Every finite computation produces a
finite `Gamma`-set, hence a co-sofic IRS. So no finite-model search can produce a
C1 witness, and a C1 witness must be an infinite non-co-sofic construction. The known
existence of non-co-hyperlinear, hence non-co-sofic, IRS (`non-cohyperlinear-irs-exists`)
is the only supply. Section 3's remark shows IRS-rigid hosts such as the binary
Leavitt unit group supply nothing new.

## 6. Why the table-group reduction does not transfer, and where C2 dies

**Word-rule designs on Schreier graphs.** Let `tau` and `sigma` use fixed memory words
`S` and `M` with no shape dependence. The forward table at `v` is the partition of the
words `m s` by right cosets of `L = Stab(v)`, and the reverse table is the same for the
words `s m`. Over a group, `L` is normal, so every relation forced at one site holds at
all sites. That is why `strict-automata-live-on-canonical-table-groups` can pass to the
normal-closure group `U_E`. On a Schreier graph a forward relation at `v` generates only
the subgroup it lies in. The site-to-site condition is that **every conjugate**
`g^-1 L g` in the support has a forward-sufficient coset table, while some conjugate has
a reverse-insufficient one. So C1 is a search over conjugation-invariant laws on
subgroups whose conjugates all pass the forward test. The canonical table group of a
design no longer bounds it.

**Diracization is monotone the wrong way (C2 attempt).** The canonical passage from an
IRS to a normal subgroup is iid intersection (`character-diracization-limit`: the
intersection IRS has character `tau_mu^k -> 1_core`). For word-rule designs:

- Intersections shrink stabilizers and so refine the coset tables. Forward sufficiency
  is an up-set (it passes to coarser tables), so refinement can destroy forward-good
  sites.
- Joins `<H_1, H_2>` of independent samples coarsen tables and preserve forward-good
  sites. But reverse failure passes only to finer tables, so joins can destroy
  reverse-bad sites.
- In the limit, the normal core, or the normal closure, can be a quotient that is not
  approximable. Each direction moves one of the two defining conditions the wrong way.

For shape-dependent rules both conditions move arbitrarily, because the rules change
with the shapes. So C2 has no monotone mechanism. It is recorded as open, with this
failure. The hyperlinear analogues `atomic-noncohyperlinear-irs-forces-nonhyperlinear`
and `ergodic-nonce-irs-fg-support-is-terminal` show the atomic and finitely generated
branches are terminal for Connes embeddability. Theorem 3.1 is the surjunctivity
version of the atomic branch.

**Finitely generated support (side remark, not a node).** If `mu` is ergodic and a.s.
supported on finitely generated subgroups, it has an atom, because there are countably
many such subgroups. Theorem 3.1 then applies. So a C1 witness that does not already
refute the goal must be nonatomic and a.s. infinitely generated. That is the same
unresolved branch as for the non-co-hyperlinear IRS.
