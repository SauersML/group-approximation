# Calibration: what Bernoulli cost = 1 + beta_1 forces on finite quotients

Swarm worker b-p-fp5, 2026-09-17. This note derives necessary consequences of
the conclusion of the cycle-tails route
(`fpbs-bernoulli-lower-bound-from-cycle-tails`) for residually finite groups.
The deduction combines imported published results. It is not independently
validated. The quotes below come from the arXiv text of each paper, with
spacing reconstructed from a PDF text extraction.

## 0. Notation

- `Gamma` is an infinite, finitely generated, residually finite group. `b` is a
  nontrivial Bernoulli action of `Gamma`. `C(.)` is cost and `beta_1 =
  beta_1^(2)(Gamma)`.
- `d(H)` is the minimal number of generators of `H`. `b_1(H;K) =
  dim_K H_1(H;K)` and `b_1(H) = b_1(H;Q)`.
- A chain `Gamma = Gamma_0 >= Gamma_1 >= ...` of finite-index subgroups is a
  *Farber chain* if the action of `Gamma` on the boundary of its coset tree is
  essentially free. This is the Abert–Nikolov convention.
- The rank gradient along a chain is `RG(Gamma;(Gamma_n)) = lim_n (d(Gamma_n)-1)/[Gamma:Gamma_n]`.
  The sequence is non-increasing by the Schreier bound, so the limit exists.
- For a normal chain, stabilisers of boundary points are conjugates of
  `cap_n Gamma_n`. So a normal chain is Farber exactly when `cap_n Gamma_n = 1`.
- `g(b) = C(b) - 1 - beta_1 >= 0` is the excess of the Bernoulli action.

## 1. Imported results

**(AW)** Abert–Weiss, arXiv:1103.1063v2, Corollary 2, as recorded in
`fpbs-bernoulli-maximal-cost`: for every free p.m.p. action `a` of `Gamma`,
`C(a) <= C(b)`.

**(G)** Gaboriau, lecture notes Theorem 2.64, as recorded in
`fpbs-amen2-betti-cost-input`: for every free p.m.p. action `a` of an infinite
group, `C(a) >= 1 + beta_1`. The notes deal with free actions. An essentially
free action restricts to a free action on a conull invariant set, which has the
same cost.

**(AN)** Abert–Nikolov, *Rank gradient, cost of groups and the rank versus
Heegaard genus problem*, arXiv:math/0701361v3, Theorem 1:

> "Theorem 1 Let (Γ_n) be a Farber chain in Γ. Then RG(Γ, (Γ_n)) = cost(E) − 1
> where E denotes the orbit relation given by the action of Γ on the boundary
> of the coset tree T(Γ, (Γ_n))."

They also say, in the same paper:

> "Gaboriau [13] has introduced L² Betti numbers of a measurable equivalence
> relation E and asked whether β_1^(2)(E) = cost(E) − 1 in general. An
> affirmative answer to Gaboriau's question would imply the surprising result
> that the asymptotic growth of β_1(Γ_n) and d(Γ_n) are equal for arbitrary
> groups."

**(EL)** Ershov–Lück, *The first L²-Betti number and approximation in arbitrary
characteristic*, arXiv:1206.0474v3.

- Theorem 1.6:

  > "Let p be a prime number. Let G be a finitely generated group and
  > G = G_0 ⊇ G_1 ⊇ G_2 ⊇ ··· a descending chain of normal subgroups of G of
  > p-power index. Then (1) The sequence b_1(G_i;F_p)/[G:G_i] is monotone
  > decreasing and therefore converges; (2) Assume that ∩_i G_i = {1}. Then
  > b_1^(2)(G) ≤ lim_(i→∞) b_1(G_i;F_p)/[G:G_i]."

- Theorem 1.1, Lück approximation, as used in their introduction: for finitely
  presented `G` and a normal chain with trivial intersection,
  `lim b_1(G_i)/[G:G_i] = b_1^(2)(G)`.

- Question 1.5:

  > "For which finitely presented groups G and finite index normal chains
  > (G_i) with ∩ G_i = {1} do we have equality
  > lim b_1(G_i)/[G:G_i] = lim b_1(G_i;F_p)/[G:G_i]?"

- Question 1.10:

  > "Let G be an infinite finitely generated residually finite group and (G_i)
  > a descending chain of finite index normal subgroups of G with
  > ∩ G_i = {1}. Is it always true that RG(G,(G_i)) = b_1^(2)(G)?"

- Question 1.11 asks when `RG(G,(G_i)) = limsup b_1(G_i;K)/[G:G_i]`, which is
  their equation (1.12). They remark:

  > "If one can find a group G for which (1.12) fails with K = F_p and (G_i) a
  > p-chain, then in view of Theorem 1.6 such group G would answer
  > Question 1.10 in the negative."

- Question 1.14 asks when `lim b_1(G_i;K)/[G:G_i]` exists for every normal
  chain with trivial intersection and is independent of the chain. They say it
  "remains open if G is finitely presented and K = F_p".

## 2. The target forces zero excess

Suppose the Bernoulli action of `Gamma` has graphings `Phi_n` as in the
conclusion of `fpbs-bernoulli-cycle-tail-compactness`. Then `g(b) = 0`.

*Proof.* Put `eps_n = c(Phi_n) - C(b) -> 0`. By
`fpbs-graphing-cost-betti-cycle-dimension-identity`,
`z(Phi_n) = g(b) + eps_n`. By
`fpbs-short-cycle-edge-measure-vanishes-near-optimum`, the edges on cycles of
length at most `L` have measure at most `L eps_n`. A finite simple-cycle chain
of length at most `L` is supported on those edges, so the dimension `z_L` of
the span of such chains is bounded by the measure of that edge set:
`z_L(Phi_n) <= L eps_n`. This is the bound used in Section 9 of
`research/artifacts/fpbs/docs/cost-cycle-structure.md`, where it appears as
`g <= (L-1) eps_n + tau_L`, a slightly sharper constant. Hence
`g(b) <= L eps_n + tau_L(Phi_n)`. Let `n -> infinity` and then `L -> infinity`.
The hypothesis gives `g(b) = 0`. QED

This is exactly the first half of the existing route. It is restated here so
that the consequence below attaches to the target node itself.

## 3. Theorem (necessary consequences of zero excess)

Let `Gamma` be infinite, finitely generated and residually finite, with
`C(b) = 1 + beta_1`. Then:

- **(i)** `RG(Gamma;(Gamma_n)) = beta_1` for every Farber chain `(Gamma_n)`.
- **(ii)** `limsup_n b_1(Gamma_n;K)/[Gamma:Gamma_n] <= beta_1` for every Farber
  chain and every field `K`. For every prime `p` and every normal chain of
  `p`-power index with trivial intersection,
  `lim_n b_1(Gamma_n;F_p)/[Gamma:Gamma_n] = beta_1`.
- **(iii)** Suppose `Gamma` is finitely presented and `(Gamma_n)` is a normal
  chain with trivial intersection. Then `d(Gamma_n)/[Gamma:Gamma_n]`,
  `b_1(Gamma_n)/[Gamma:Gamma_n]` and `b_1(Gamma_n;F_p)/[Gamma:Gamma_n]`, for
  every prime `p`, all converge to `beta_1`. Moreover
  `d(tors H_1(Gamma_n;Z))/[Gamma:Gamma_n] -> 0`.

So, for such `Gamma`:

- Question 1.10 of EL has a positive answer.
- Question 1.11 has a positive answer for every `p`-chain with trivial
  intersection. For finitely presented `Gamma` it has a positive answer for
  every normal chain with trivial intersection and every field.
- Questions 1.5 and 1.14 (with `K = F_p`) have positive answers when `Gamma` is
  finitely presented.

*Proof of (i).* Let `a` be the boundary action of `Gamma` for the chain. It
preserves the inverse-limit probability measure and is essentially free. By
(G), `C(a) >= 1 + beta_1`. By (AW), `C(a) <= C(b) = 1 + beta_1`. So
`C(a) = 1 + beta_1`, and (AN) gives `RG = C(a) - 1 = beta_1`.

*Proof of (ii).* A generating set of `H` maps onto a spanning set of
`H_1(H;K) = H^ab ⊗ K`, so `b_1(H;K) <= d(H)`. The index tends to infinity,
because `Gamma` is infinite and the chain is Farber. So
`limsup b_1(Gamma_n;K)/[Gamma:Gamma_n] <= lim d(Gamma_n)/[Gamma:Gamma_n] = RG = beta_1`.
For a normal `p`-chain with trivial intersection, EL Theorem 1.6 gives
`beta_1 <= lim b_1(Gamma_n;F_p)/[Gamma:Gamma_n]`. The chain is Farber, so this
limit is at most `beta_1`, and equality follows.

*Proof of (iii).* By Lück approximation, `b_1(Gamma_n)/[Gamma:Gamma_n] -> beta_1`.
Write `H_1(Gamma_n;Z) = Z^(b_1) ⊕ T_n` with `T_n` finite.

- Universal coefficients give `b_1(Gamma_n;F_p) = b_1(Gamma_n) + d_p(T_n)`,
  where `d_p(T) = dim T/pT`.
- A finite abelian group has `d(T) = max_p d_p(T)`.
- `d(Z^b ⊕ T) = b + d(T)`, because it equals `max_p dim (Z^b ⊕ T)/p = b + max_p d_p(T)`.

The abelianisation is a quotient of `Gamma_n`, which gives

```text
b_1(Gamma_n) <= b_1(Gamma_n) + d_p(T_n) = b_1(Gamma_n;F_p)
             <= b_1(Gamma_n) + d(T_n) = d(H_1(Gamma_n;Z)) <= d(Gamma_n).
```

Divide by the index. The two outer terms tend to `beta_1`, by Lück
approximation and by (i). So every middle term tends to `beta_1`, and
`d(T_n)/[Gamma:Gamma_n] -> 0`, uniformly in `p`. QED

## 4. Contrapositive and consequences for the program

**Corollary.** Suppose some infinite, finitely generated, residually finite
group has a Farber chain with `RG > beta_1^(2)`. Then its Bernoulli action has
`C(b) > 1 + beta_1^(2)`, and it satisfies neither the conclusion of
`fpbs-bernoulli-cycle-tail-compactness` nor any other certificate of zero
excess. Two sufficient ways to produce such a chain:

- a prime `p` and a normal `p`-chain with trivial intersection whose mod-`p`
  gradient exceeds `beta_1^(2)`;
- for a finitely presented group, a normal chain with trivial intersection
  whose torsion `d(tors H_1)` grows linearly in the index.

Remarks.

1. This does not refute Fixed Price. A group with fixed price
   `C > 1 + beta_1` is compatible with every item above. The corollary kills
   only the cost = 1 + beta_1 family of routes. That family includes the
   cycle-tails route and any route that goes through the equality in
   `fpbs-graphing-cost-betti-cycle-dimension-identity`.
2. For Kazhdan groups, `beta_1 = 0`, and the counterexample corollary is the
   hole `fpbs-kazhdan-positive-rank-gradient`. That hole refutes Fixed Price
   itself, through Hutchcroft–Pete cost one. Outside property (T), a positive
   gradient above `beta_1` refutes only cost = 1 + beta_1.
3. The consequences in (ii) and (iii) are statements about all finite quotients
   of every finitely presented residually finite group, in positive
   characteristic. EL list them as open questions, and AN call the rank
   analogue "surprising". So the cycle-tails route is at least as hard as
   positive answers to those questions for the whole class. Any proof of the
   compactness target must contain a proof of (ii) and (iii) for every such
   group.

## 5. What finite computation can and cannot certify

- `(d(Gamma_n)-1)/[Gamma:Gamma_n]` is non-increasing along a chain. A finite
  computation along the chain therefore yields only upper bounds on `RG`.
- `beta_1^(2)(Gamma) <= (d(H)-1)/[Gamma:H]` holds for every finite-index `H`,
  by multiplicativity and `beta_1^(2)(H) <= C(H) - 1 <= d(H) - 1`. So the same
  finite data bound `beta_1` from above too.
- For `p`-chains, `b_1(Gamma_n;F_p)/[Gamma:Gamma_n]` is non-increasing, by EL
  Theorem 1.6(1). Finite levels again give upper bounds on the mod-`p`
  gradient, which is at least `beta_1`.

So no finite list of quotients separates `RG` from `beta_1`. A counterexample
needs an asymptotic lower bound on `RG` or on a mod-`p` gradient from a theorem,
for instance power `p`-deficiency (`fpbs-power-p-deficiency-schreier-bound`).
It also needs a structural upper bound on `beta_1`.

## 6. A filter for power p-deficiency certificates

Let `G = <X|R>` be an infinite finite presentation with no relator trivial in
`F(X)`. Write `r = u_r^(n_r)` with `u_r` not a proper power, and let `o_G(r)`
be the order of `u_r` in `G`. By root uniqueness in free groups, `r` is a
`p^k`-th power iff `p^k | n_r`, so `nu_p(r) = v_p(n_r)`. The node
`first-l2-betti-at-least-negative-orbifold-char` gives

```text
beta_1^(2)(G) >= |X| - 1 - sum_r 1/o_G(r).
```

Suppose the presentation's power-`p`-deficiency term exceeds `beta_1^(2)(G)`.
Then

```text
sum_r ( 1/o_G(r) - p^(-v_p(n_r)) ) > 0.
```

So some relator has `o_G(r) < p^(v_p(n_r))`: the root `u_r` already dies at a
power strictly below the `p`-part of the exponent. In the other cases,
`o_G(r) = n_r` for all `r`, or more generally `p^(v_p(n_r)) | o_G(r)` for all
`r`, the presentation's `p`-deficiency term is at most the orbifold lower bound
for `beta_1^(2)`. Its lower bound on the `p`-gradient then cannot certify
`RG > beta_1`.

This is a filter, not a kill:

- nothing above bounds `beta_1` from above;
- the supremum defining `def_p` runs over presentations with infinitely many
  relators, where the orbifold bound is not available.

A certificate of the form "positive power `p`-deficiency beats `beta_1`" must
come from presentations with collapsing `p`-power relators, or from infinite
presentations.
