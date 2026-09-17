# Normal subgroups of finite cost and positive rank gradient: a counterexample reduction and where it dies

Agent `swarm-0917-w4-fp-heretic`, 2026-09-17. This is a written deduction, not a
formal verification. Conventions: groups are countable; actions are
essentially free and probability measure preserving (p.m.p.); `C(alpha)` is the
cost of the orbit relation of `alpha`; `cost(G)` is the infimum of `C(alpha)`
over free p.m.p. actions of `G`. "`N` has bounded action cost `K`" means every
free p.m.p. action of `N` has cost at most `K`. (For finitely generated groups this
is automatic with `K = d(N)`; in general, heuristically, it says that the Bernoulli
shift of `N` has finite cost. Nothing below uses that reformulation.)

## 0. Class audit for the assignment

| Candidate class | Invariant proposed to separate two actions | Where it dies |
|---|---|---|
| Groups with infinite or varying `l2` Betti numbers | `beta_n^(2)` of the orbit relation | Gaboriau (Publ. IHES 95, 2002): `beta_n^(2)(R_alpha) = beta_n^(2)(G)` for every free p.m.p. action `alpha`. Every `l2` invariant is action-independent, so it gives the same lower bound `1 + beta_1^(2)(G)` for all actions and cannot separate them. |
| `SL_3(Z) x F_n`, and more generally products of infinite groups | cost of the Bernoulli shift against a cheap action | Products of two infinite groups have fixed price one (Khezeli; Gaboriau's commensurated-chain criterion). Dead. |
| Tarski monsters, and simple torsion groups in general | none available | They have no finite quotients (so no profinite actions and no rank gradient), no infinite amenable subgroups, no infinite normal subgroups, and `beta_1^(2)` is action-independent. Every known *action-dependent* lower bound on cost is the Abert--Nikolov formula for profinite actions, and it is vacuous here. This is **certificate starvation**, not a kill: no known invariant can certify that some action costs more than `1 + beta_1^(2)`. |

The only known machine that produces two free actions of provably different cost is the following:

* a *cheap-action theorem*: Hutchcroft--Pete for Kazhdan groups, or Gaboriau's finite-cost normal subgroup theorem;
* compared against the *Abert--Nikolov* identity `C(boundary action) = 1 + RG`.

The Kazhdan instance is `fpbs-kazhdan-rankgradient-counterexample-reduction`. Section 1 records the normal-subgroup instance (reduction R). Sections 2--4 show precisely where every member of that instance dies, except on two named survivor classes.

## 1. Reduction R

**Imported inputs (verbatim).**

* **[DES, Theorem 2.2].** Donoso-Echenique and Silva, *Free Burnside groups of large odd exponent have cost 1*, Theorem 2.2, quoting [Gab02b, Theorem 3.4]:
  > "Let G be a countable group and let N◁G be an infinite normal subgroup such that N has infinite index in G and cost(N)<∞. Then cost(G) = 1."

  The same paper adds: "In [Gab02b] it is assumed that N is finitely generated, but this can be replaced by the assumption that N has finite cost; see the footnote on page 884 of [HP20] and [Gab25, Theorem 2.56]". Here `cost` is the *infimal* cost.
* **[AN, Theorem 1].** Abert and Nikolov, *Rank gradient, cost of groups and the rank versus Heegaard genus problem*, arXiv:math/0701361v3:
  > "Let (Γ n) be a Farber chain in Γ . Then RG(Γ , (Γ n)) = cost( E)− 1 where E denotes the orbit relation given by the action of Γ on the boundary of the coset tree T (Γ , (Γ n))."

  They also say: "This is the case for example when the chain consists of normal subgroups of Γ and their intersection is trivial. Note that then ∂T is simply the profinite completion of Γ with respect to (Γ n) endowed with the normalized Haar measure."

  Here "Γ" is finitely generated, and `RG(Γ,(Γ_n)) = lim (d(Γ_n) - 1)/[Γ:Γ_n]`.

**Theorem R.** Suppose:

* `G` is a finitely generated group;
* `N ◁ G` is infinite, of infinite index, with `cost(N) < ∞`;
* `(G_n)` is a descending chain of finite-index normal subgroups with trivial intersection and `RG(G,(G_n)) > 0`.

Then `G` does not have fixed price, so `fpbs-fixed-price-counterexample-exists` holds.

*Proof.* By [DES, Theorem 2.2], `cost(G) = 1`, so for every `ε > 0` some free p.m.p. action `beta` has `C(beta) < 1 + ε`. The chain is Farber by the sentence quoted from [AN]. By [AN, Theorem 1], the boundary action `alpha` on `lim G/G_n` is free and has `C(alpha) = 1 + RG(G,(G_n)) > 1`. Take `ε < RG(G,(G_n))`. □

**Remarks.**

1. Theorem R needs no property (T) and no attainment of the infimum, so it is distinct from the Kazhdan reduction.
2. If `N` is finitely generated, the chain argument in the proof of [AN, Proposition 13] shows that `RG(G,(G_n)) = 0` whenever `[G:G_nN]` is unbounded. So a finitely generated `N` can only work through chains with `[G:G_nN]` bounded. Section 2 extends this to every `N` of bounded action cost.

## 2. Theorem A': cost one over a free quotient by a larger kernel

**Theorem A'.** Assume the following.

* `G` is a countable group.
* `N ◁ G` is infinite and has bounded action cost `K`.
* `M ◁ G` satisfies `N ≤ M` and `[G:M] = ∞`.
* `alpha` is a free p.m.p. action of `G` on `(X,mu)`.
* `phi : X -> Y` is a `G`-equivariant factor map onto `(Y,nu)`. `M` acts trivially on `Y`, and the induced action `sigma` of `Q = G/M` on `Y` is essentially free with `C(sigma) < ∞`.

Then `C(alpha) = 1`.

For `M = N` this is Theorem A of `research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md` (claim `fpbs-quotient-split-actions-have-cost-one`). The new point is that `M/N` may be infinite and `M` need not have bounded cost.

**Inputs.**

* (I1) *Small markers.* An aperiodic p.m.p. countable Borel equivalence relation has, for every `η > 0`, a Borel complete section of measure at most `η`. This is Gaboriau, lecture notes Exercise 1.17 (compare Kechris--Miller, *Topics in orbit equivalence*, Lemma 6.7), imported as `fpbs-small-marker-induction-input`.
* (I2) *Induction formula.* For a complete section `A` of an aperiodic p.m.p. relation `R`, the unnormalized cost of `R|A` equals `C(R) - 1 + nu(A)`. This is Gaboriau, lecture notes Proposition 2.33, imported as `fpbs-normalized-cost-induction-input`.
* (I3) *Pieces.* Every partial isomorphism contained in the orbit relation of a free action splits into countably many Borel pieces, and on each piece it agrees with one fixed group element (Feldman--Moore). Splitting does not change the measure of a graphing.

**Lemma 2.1 (normalizer trick).** Let `N ◁ L` with `N` infinite, and let `L` act freely p.m.p. on an `L`-invariant set `B`. Let `S` be a complete section of `R_N|B`, let `h ∈ L`, and let `Φ` be a graphing that generates `R_N|B`. Then `Φ ∪ {h|S}` generates a relation containing `(x, hx)` for every `x ∈ B`.

*Proof.* Choose `n ∈ N` with `nx ∈ S`. Then `hx = (h n^{-1} h^{-1}) · h(nx)`, and `h n^{-1} h^{-1} ∈ N`. So `x ~_N nx`, the piece `h|S` gives `nx ~ h(nx)`, and `h(nx) ~_N hx`. □

**Lemma 2.2 (fibres are `M`-orbits).** In the setting of Theorem A', first discard a null `G`-invariant set so that `sigma` is everywhere free. Take `x ∈ X` and `y` in the `sigma`-orbit of `phi(x)`. Then `Gx ∩ phi^{-1}(y)` is exactly one `M`-orbit.

*Proof.* Let `q : G -> Q` be the quotient map. If `hx` and `h'x` both lie over `y`, then `q(h)^{-1} q(h')` fixes `phi(x)`. So `h' = hm` for some `m ∈ M`, and `h'x = (h m h^{-1}) hx ∈ M hx`. Conversely, `M` acts trivially on `Y`, so all of `M hx` lies over `y`. □

**Proof of Theorem A'.** Fix `ε ∈ (0,1)` and `δ > 0`.

*Setup.*

* `Q` is infinite and `sigma` is free, so `R_sigma` is aperiodic. By (I1) there is a complete section `A` of `R_sigma` with `nu(A) ≤ δ`.
* Put `B = phi^{-1}(A)`. Then `B` is `M`-invariant, `mu(B) = nu(A) ≤ δ`, and `B` meets every `G`-orbit.
* `N` is infinite and acts freely, so `R_N` is aperiodic. By (I1), for every `η > 0` it has a complete section of measure at most `η`. Such a section meets every `N`-orbit, so it meets every `N`-invariant set in a complete section of the restricted relation.

*The four graphings.*

* **(Φ1)** `N` acts freely on `B`, and after rescaling `mu|B` that action has cost at most `K`. So `R_N|B` has a generating graphing `Φ1` of measure at most `(K+ε) mu(B) ≤ (K+ε)δ`.
* **(Φ1')** Choose `h_1, h_2, ... ∈ M` whose images generate `M/N`, and complete sections `T_i` of `R_N` with `mu(T_i) ≤ ε 2^{-i}`. `Φ1'` is the family of pieces `h_i|(T_i ∩ B)`, of total measure at most `ε`. Since `M = <N, h_i : i ≥ 1>`, Lemma 2.1 with `L = M` shows that `Φ1 ∪ Φ1'` generates `R_M|B`.
* **(Φ2)** Enumerate `G = {g_1, g_2, ...}`. Let `D_k` be the set of `x ∉ B` such that `g_k x ∈ B` and `g_j x ∉ B` for all `j < k`. `Φ2` is the family of pieces `g_k|D_k`. The `D_k` are disjoint and cover `X \ B` because `B` meets every orbit, so `Φ2` has measure at most `1 - mu(B)`.
* **(Φ3)** By (I2), `R_sigma|A` has a generating graphing of measure at most `C(sigma) - 1 + nu(A) + ε < ∞`. By (I3), refine it into pieces `(C_j, q_j)` with `C_j ⊆ A`, `q_j C_j ⊆ A` and `q_j ∈ Q`. Lift each `q_j` to some `g'_j ∈ G`, and choose complete sections `T'_j` of `R_N` with `mu(T'_j) ≤ ε 2^{-j}`. `Φ3` is the family of pieces `g'_j|(T'_j ∩ phi^{-1}(C_j))`, of total measure at most `ε`.

*Generation.* Let `x` and `x' = gx` lie in one `G`-orbit. Using `Φ2`, we may assume `x, x' ∈ B`. Then `phi(x), phi(x') ∈ A` lie in one `sigma`-orbit, so there is a path `y_0 = phi(x), ..., y_r = phi(x')` in which each step is one of:

* `y_{t+1} = q_j y_t` with `y_t ∈ C_j`;
* `y_t = q_j y_{t+1}` with `y_{t+1} ∈ C_j`.

By Lemma 2.2, `O_t = Gx ∩ phi^{-1}(y_t)` is a single `M`-orbit, and it lies inside `B`. Consider a step of the first kind. `O_t` contains an `N`-orbit, so it contains some `z ∈ T'_j`. Then `phi(z) = y_t ∈ C_j`, and `g'_j z ∈ Gx ∩ phi^{-1}(y_{t+1}) = O_{t+1}`. So `Φ3` joins `O_t` to `O_{t+1}`. A step of the second kind works the same way, starting from `O_{t+1}`. `Φ1 ∪ Φ1'` connects all points inside each `O_t`. Hence `x` and `x'` are joined.

*Total.* `C(alpha) ≤ (K+ε)δ + ε + (1 - mu(B)) + ε ≤ 1 + (K+1)δ + 2ε`. Letting `ε, δ -> 0` gives `C(alpha) ≤ 1`. Orbits are infinite, so `C(alpha) ≥ 1`. □

## 3. Corollary: quotient-unbounded chains have zero rank gradient

**Corollary 3.1.** Assume:

* `G` is finitely generated;
* `N ◁ G` is infinite with bounded action cost `K`;
* `(G_n)` is a descending chain of finite-index normal subgroups with `∩_n G_n = 1`, and `[G : G_n N]` is unbounded.

Then `RG(G,(G_n)) = 0`.

*Proof.*

1. **The spaces.** Let `X = lim G/G_n` and `Y = lim G/G_nN`, each with normalized Haar measure. `G` acts on both by left translation. The natural map `phi : X -> Y` is equivariant and pushes Haar measure to Haar measure.
2. **Freeness on `X`.** Suppose `g x = x`, where `x = (x_n G_n)_n`. Then `x_n^{-1} g x_n ∈ G_n` for every `n`. Since each `G_n` is normal, `g ∈ ∩ G_n = 1`. So `alpha` is free everywhere.
3. **The quotient action.** Put `M = ∩_n G_nN`, a normal subgroup containing `N`. The same computation shows that `g ∈ G` fixes a point of `Y` iff `g ∈ G_nN` for all `n`, iff `g ∈ M`. So `M` acts trivially on `Y`, and `Q = G/M` acts freely.
4. **Hypotheses of Theorem A'.** The subgroups `G_nN` decrease and have unbounded finite index, so `[G:M] = ∞`. The group `Q` is generated by `d(G)` elements, so `C(sigma) ≤ d(G) < ∞`.
5. **Conclusion.** Theorem A' gives `C(alpha) = 1`. The chain is Farber (normal, trivial intersection), so [AN, Theorem 1] gives `RG(G,(G_n)) = C(alpha) - 1 = 0`. □

## 4. The quotient-bounded case: the cost gap moves into `N`

**Lemma 4.1 (Gaboriau's normal subgroup monotonicity, reproved).** Suppose `N ◁ L` with `N` infinite, and `L` acts freely p.m.p. on `(Z,mu)`. Then `C(R_L) ≤ C(R_N)`, where `R_N` is the orbit relation of the restricted `N`-action on the same space.

*Proof.* Take a generating graphing of `R_N` of measure at most `C(R_N) + ε`. Add the pieces `h_i|T_i`, where the `h_i ∈ L` generate `L` modulo `N` and the `T_i` are complete sections of `R_N` with `mu(T_i) ≤ ε 2^{-i}`, as given by (I1). Lemma 2.1, with `B = Z`, shows that the result generates `R_L`. □

**Proposition 4.2.** Assume:

* `G` is finitely generated and `N ◁ G` is infinite;
* `(G_n)` is a descending chain of finite-index normal subgroups with `∩ G_n = 1`;
* `[G:G_nN]` is bounded, so `G_nN = M_0` and `[G:M_0] = a` for all `n ≥ n_0`.

Then the free, ergodic p.m.p. action `N ↷ lim N/(N ∩ G_n)` on the profinite completion of `N` along `(N∩G_n)` satisfies

    C(N ↷ lim N/(N∩G_n)) ≥ 1 + a · RG(G,(G_n)).

*Proof.* For `n ≥ n_0`, `M_0` is finitely generated, and the `G_n` are normal in `M_0` with trivial intersection. By [AN, Theorem 1], `M_0 ↷ X_0 = lim M_0/G_n` has cost `1 + RG(M_0,(G_n))`, and `RG(M_0,(G_n)) = a · RG(G,(G_n))`.

Since `N G_n = M_0`, the maps `N/(N∩G_n) -> M_0/G_n` are `N`-equivariant bijections compatible with the chain. They therefore induce a measure-preserving `N`-isomorphism `lim N/(N∩G_n) ≅ X_0`. This action is free (normal chain, trivial intersection) and ergodic (transitive at every level). Lemma 4.1 with `L = M_0` gives `1 + a · RG(G,(G_n)) = C(R_{M_0}) ≤ C(R_N)`. □

## 5. Where route R dies, and what survives

Let `(G, N, (G_n))` satisfy the hypotheses of Theorem R. Its conclusion forces `RG(G,(G_n)) > 0`. Sections 3 and 4 then show that one of the following holds.

* **(S1) `N` itself fails fixed price.** `N` does not have bounded action cost, while `cost(N) < ∞`. Then the free actions of `N` have costs that are finite and costs that are arbitrarily large, so `N` is already a counterexample to fixed price, and the question descends to `N`. For finitely generated `N` this case is empty, since every action of `N` has cost at most `d(N)`. If (S1) fails, `N` has bounded action cost, and Corollary 3.1 forces (S2).
* **(S2) The chain is quotient-bounded.** After passing to the finite-index subgroup `M_0`, the chain is `N`-surjective. Proposition 4.2 shows that the ergodic profinite action of `N` along `(N ∩ G_n)` costs more than one. So `N` does not have fixed price one, and neither Gaboriau's normal fixed-price-one criterion nor Theorem A' applies.

**Every other member of route R dies at one step:** the boundary action `lim G/G_n` factors onto a free action of the infinite quotient `G/∩(G_nN)`, and Theorem A' makes its cost one, contradicting `RG > 0` through [AN, Theorem 1].

In particular:

* (a) Every route-R counterexample over a normal subgroup `N` of bounded action cost (for instance, any finitely generated `N`) uses a chain with `[G:G_nN]` bounded. This is exactly the shape of the Abert--Nikolov 3-manifold alternative: a fibred hyperbolic 3-manifold with a chain surjecting onto the fibre quotient `Z` modulo finite index.
* (b) (S2) is the ergodic-restriction case of `fpbs-normal-subgroup-bounded-cost-fixed-price-one`. The obstruction there is that no small invariant set exists on which to pay the cost of `N`.
* (c) Tarski monsters, and every group with no finite quotients, are outside this machine entirely.
