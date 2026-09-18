# Fixed-position cutting dies on Bernoulli: a height-level spectral obstruction

Written 2026-09-18 by swarm-0917-w6-w6-fp-pull. This is a written deduction. It has not been checked in Lean or
reviewed independently.

## 0. What is being killed

Poulin--Wróbel (arXiv:2606.23506v1, Theorem 3.4) compute the cost of one-relator groups by cutting. On a special free
action they delete the `s`-edge at a fixed position of the relator cycle, at almost every point of a transversal.
They certify connectivity by a replacement operator `theta` whose iteration terminates. It terminates because of
their Lemma 3.3: every `P`-sequence of length `n^L` meets a window of coherent `Z/n` phases.

Their Remark 3.6 records that their action is not weakly contained in Bernoulli, so it gives no Bernoulli bound. That
remark leaves a transplant open: on the Bernoulli shift, replace the phases by some other Borel rule, for example
iid markers or local cutoffs.

This note closes that transplant for the whole class of fixed-position matchings. The data are an embedded relation
with `m = 1`, or more generally any relator with a designated letter position, and the Bernoulli shift (or any factor
of it). If `Lambda = <P>` is nonamenable, no Borel choice of cut set whatsoever reaches mass `1 - c`. The constant
`c` is explicit from the Kesten spectral radius of `Lambda`.

The invariant is the absence of `Lambda`-almost-invariant vectors in `L^2_0`. The step where every member dies is
the termination of `theta`, which is condition (M3) of `fpbs-bernoulli-morse-collapse-criterion`. Termination
forces the height level sets to be almost invariant under `P`.

## 1. Setting

- `Gamma` is a countable group with a finite generating set `S`.
- `a` is an essentially free p.m.p. action on `(X, mu)`, written `x -> g.x`.
- For `s in S` and `x in X`, the *`s`-edge at `x`* is `e_x = (x, s.x)` of the Cayley graphing `Phi_S`.
- `r = t_k ... t_1` is a word in `S^{+-1}` that is trivial in `Gamma`. The cell `(x, r)` has boundary path
  `x, t_1.x, t_2 t_1.x, ..., t_k ... t_1.x = x`.
- Put `g_j = t_(j-1) ... t_1`.
  - If `t_j = s`, step `j` traverses `e_(g_j.x)`.
  - If `t_j = s^-1`, step `j` traverses `e_(s^-1 g_j.x)`.
- Let `Q ⊆ Gamma` be the set of these elements (`g_j` or `s^-1 g_j`), over the positions where `s^{+-1}` occurs.
- **Designated position.** After rotating `r`, some `s`-occurrence has element `1`. Put `P = Q \ {1}`. Assume two
  things:
  - `s^2 != 1` in `Gamma`;
  - exactly one position yields `1`, so the boundary path of `(x, r)` traverses `e_x` exactly once.
- `Lambda = <P> <= Gamma`, and `T = P ∪ P^-1` is a finite symmetric generating set of `Lambda`.

**Fixed-position matchings.** For a Borel `A ⊆ X`, let `M_A` be the partial map `(x, r) -> e_x` for `x in A`.

- (M1) holds as noted.
- (M2) holds. If `e_x = e_y` with `x != y`, then `y = s.x` and `s.y = x`, so `s^2.x = x`. Freeness then gives
  `s^2 = 1`, which is excluded.
- The children of `e_x` in the sense of (M3) are exactly the edges `e_(g.x)` with `g in P` and `g.x in A`. Every
  other boundary edge either carries another label or is an `s`-edge at a point outside `A`, so it is not in
  `E_(M_A)`.

So `M_A` is a Morse matching exactly when the following holds.

**(WF)** For almost every `x in A`, there is no infinite sequence `x_0 = x`, `x_(j+1) = p_j.x_j` with `p_j in P` and
all `x_j in A`.

The mass of `M_A` is `mu(A)`. PW's Theorem 3.4 with `m = 1` says that (WF) holds with `mu(A) >= 1 - eps` on a free
extension of their coset process, where `A` is the complement of the phase window.

## 2. The height lemma (any action)

**Lemma 1 (heights).** Suppose (WF) holds for `A`, and put `W = X \ A` and `delta = mu(W)`. Then there are Borel sets
`W = X_(-1) ⊆ X_0 ⊆ X_1 ⊆ ...` with union conull, such that for every `k >= 0` and every `p in P`:

- (H1) `p.(X_k \ W) ⊆ X_(k-1)`;
- (H2) `mu(X_k) <= mu(X_(k-1)) + delta`;
- (H3) `mu(p.X_k Δ X_k) <= 2 delta`.

*Proof.*

1. **Height.** For `x in A`, let `h(x)` be the supremum of the lengths of finite sequences
   `x_0 = x, ..., x_n` with `x_(j+1) in P.x_j` and all `x_j in A`. The possible sequences from `x` form a rooted
   tree in which every node has at most `|P|` children. By (WF) it has no infinite branch. By König's lemma it is
   finite, so `h(x) < infinity` for a.e. `x in A`. `h` is Borel, being a supremum over countably many Borel
   conditions.
2. **Levels.** Put `X_k = W ∪ {x in A : h(x) <= k}`. These sets increase and their union is conull.
3. **(H1).** Let `x in X_k \ W` and `p in P`. If `p.x in W`, then `p.x in X_(k-1)`. Otherwise `p.x in A`, and any
   sequence from `p.x` extends by one step to a sequence from `x`. So `h(p.x) <= h(x) - 1 <= k - 1`.
4. **(H2).** By (H1), `mu(X_k) - delta <= mu(X_k \ W) = mu(p.(X_k \ W)) <= mu(X_(k-1))`.
5. **(H3).** By (H1) and `X_(k-1) ⊆ X_k`, `p.X_k ⊆ X_k ∪ p.W`, so `mu(p.X_k \ X_k) <= delta`. Since `p` preserves
   `mu`, `mu(X_k \ p.X_k) = mu(p.X_k \ X_k)`. Adding the two gives `2 delta`. QED.

**Reading.** A well-founded fixed-position cut set has a height function that strictly decreases along `P`. Its
sublevel sets then grow by at most `delta` per level and are `2 delta`-almost invariant under every `p in P`. In
PW's coset action these are unions of phase classes of `Lambda / Delta_(i,N)`. The lemma shows that some structure
of this kind is forced on every action.

**Theorem 2 (spectral obstruction).** Suppose the Koopman representation `pi` of `a`, restricted to `Lambda` on
real `L^2_0(X, mu)`, satisfies a gap

```text
sum over t in T of || pi(t) f - f ||^2  >=  kappa || f ||^2      for all real f in L^2_0.     (GAP)
```

Then every Borel `A` satisfying (WF) has

```text
mu(X \ A)  >=  min( 1/4 , 3 kappa / (64 |P|) ).
```

*Proof.*

1. Let `delta = mu(X \ A)` and assume `delta < 1/4`. Take the sets `X_k` of Lemma 1.
2. `mu(X_(-1)) = delta < 1/2`, and `mu(X_k) -> 1`. Let `k >= 0` be least with `mu(X_k) >= 1/2`. By (H2),
   `mu(X_k) < 1/2 + 1/4`.
3. Put `f = 1_(X_k) - mu(X_k)`. Then `||f||^2 = mu(X_k)(1 - mu(X_k)) >= 3/16`.
4. `pi(p) f - f = 1_(p.X_k) - 1_(X_k)`, so by (H3), `||pi(p) f - f||^2 <= 2 delta`.
5. For `p^-1`, `||pi(p^-1) f - f|| = ||f - pi(p) f||`. So the sum over `T` is at most
   `2 sum over p in P of ||pi(p) f - f||^2 <= 4 |P| delta`.
6. (GAP) gives `4 |P| delta >= 3 kappa / 16`, that is, `delta >= 3 kappa / (64 |P|)`. QED.

## 3. The gap holds on Bernoulli shifts and their factors

**Proposition 3.** Let `b` be the Bernoulli shift `Gamma ↷ (Y^Gamma, nu^Gamma)` with a standard base space, and let
`Lambda <= Gamma` be nonamenable with finite symmetric generating set `T`. Let `rho = rho(Lambda, T) < 1` be the
Kesten spectral radius. Then (GAP) holds with `kappa = 2 |T| (1 - rho)`, for `b` and for every factor of `b`.

*Proof.*

1. **Basis.** Choose a real orthonormal basis `{1} ∪ {u_i : i in I}` of real `L^2(Y, nu)`. For a finite nonempty
   `F ⊆ Gamma` and a map `sigma : F -> I`, put `U_sigma(omega) = prod over gamma in F of u_(sigma(gamma))(omega_gamma)`.
   These `U_sigma` form a real orthonormal basis of real `L^2_0`.
2. **Permutation.** With `(lambda.omega)_gamma = omega_(lambda^-1 gamma)`, we get
   `pi(lambda) U_sigma = U_(sigma')`, where `sigma'(lambda gamma) = sigma(gamma)` on `lambda F`. So `Lambda` permutes
   the basis.
3. **Finite stabilizers.** The stabilizer of `sigma` fixes `F` setwise, so it lies in the finite set `F F^-1`.
4. **Decomposition.** Real `L^2_0` is the orthogonal direct sum, over the `Lambda`-orbits on the basis, of real
   `l^2(Lambda / K_j)` with each `K_j` finite, and `Lambda` acts by left translation.
5. **Gap.** A finite `K_j` is amenable. `kesten-amenable-stabilizer-uniform-gap`, (KAG2), gives
   `sum over t in T of ||f - t f||^2 >= 2 |T| (1 - rho) ||f||^2` on each summand. Both sides are additive over
   orthogonal `Lambda`-invariant summands.
6. **Factors.** If `b -> c` is a factor map, `L^2_0` of `c` is a closed `Lambda`-invariant subspace of `L^2_0` of `b`,
   so (GAP) restricts to it. QED.

**Corollary 4 (fixed-position matchings on Bernoulli).** In the setting of Section 1, suppose `Lambda = <P>` is
nonamenable, and let `a` be the Bernoulli shift of `Gamma` or any factor of it. Then every well-founded
fixed-position matching `M_A` has mass

```text
mu(M_A) = mu(A)  <=  1 - min( 1/4 , 3 (1 - rho(Lambda, P ∪ P^-1)) / 32 ).
```

*Proof.* By Theorem 2 and Proposition 3, with `kappa = 2 |T| (1 - rho) >= 2 |P| (1 - rho)`. QED.

**Remark 5 (actions weakly contained in Bernoulli).** Suppose `a ≺ b`. By Kechris, *Global aspects of ergodic group
actions*, the Koopman representation of `a` on `L^2_0` is weakly contained in that of `b`. This is the import [K]
already used in `fpbs-hp-condensation-bernoulli-exit-proof`. It restricts to `Lambda`.

Weak containment gives spectral inclusion for the self-adjoint Markov element `(1/|T|) sum over t in T of t`. So
its top spectral value on `L^2_0(a)` is at most `rho`, and (GAP) holds with the same `kappa`. Corollary 4 therefore
extends to every action weakly contained in Bernoulli, the class that matters for upper bounds on the Bernoulli
cost via monotonicity of cost. This extension rests on [K] and is not part of the established core.

## 4. Consequences for one-relator groups

**Corollary 6 (torsion-free relator).** Let `Gamma = <S | w>`, with `w` cyclically reduced and not a proper power,
and let `s` occur in `w`. By Weinbaum (`weinbaum-proper-subwords-of-relator-nontrivial`), proper subwords of cyclic
permutations of `w` are nontrivial. So the boundary cycle is embedded: the `k_s` elements of `Q` are distinct and `1`
arises once. `Gamma` is torsion-free, so `s^2 != 1`.

Put `P = Q \ {1}`, which has `k_s - 1` elements. If `<P>` is nonamenable, every well-founded fixed-position matching
on the Bernoulli shift, or on any factor of it, leaves a deficit at least `min(1/4, 3(1 - rho)/32)` against the
ceiling `z(Phi_S) = |S| - 1 - beta_1^(2) = 1`.

This concerns only the single-relator list `{w}` and the class `M_A`. Longer trivial words may help, and so may
matchings that change position from cell to cell. See Section 6.

**Corollary 7 (proper powers, saturated windows).** Let `Gamma = <S | w^m>` with `m >= 2`, and let `P` be as in PW
Theorem 3.4 (`Q` minus `{1, w̄, ..., w̄^(m-1)}`).

Suppose `W` is `<w̄>`-invariant and every forward `P`-chain in `X \ W` is finite. Then for any Borel transversal `C`
of `<w̄>`, the set `A = C \ W` has `mu(A) = (1 - mu(W))/m`. So on Bernoulli with `<P>` nonamenable, its deficit
against `1/m` is at least `(1/m) min(1/4, 3(1 - rho)/32)`.

The saturation hypothesis matters. Without it, a transversal chosen to avoid `W` changes the count. Section 6 records
this case as open.

## 5. Calibration

- **Amenable `Lambda`: no obstruction, correctly.**
  - For `m = 1` and a letter used twice, `P = {q}` and `Lambda = <q>` is infinite cyclic, so (GAP) fails.
  - Indeed, iid markers `W` of density `eps` on Bernoulli meet every forward ray `x, q.x, q^2.x, ...` almost surely.
    So (WF) holds with mass `1 - eps`.
  - This agrees with `fpbs-one-relator-twice-used-letter-fixed-price`.
- **PW's coset action: no obstruction, correctly.** Its restriction to `Lambda` has the finite factor
  `Lambda / Delta_(1,N)`. So `L^2_0` contains `Lambda`-invariant vectors, (GAP) fails, and PW reach mass `1 - eps`.
  The sets `X_k` of Lemma 1 are there unions of phase classes.
- **The class fails even for a free group.** Take `r = c s b s a s` in `<s, a, b, c>`, which presents `F_3`.
  - Reading `r` right to left gives `t_1 = s`, `t_3 = s` and `t_5 = s`, so `Q = {1, a s, b s a s}`.
  - Then `Lambda = <a s, (b s)(a s)> = <a s, b s>`. It is free of rank 2, because `{a s, b s, s}` is a free basis of
    `F_3 = <s, a, b>`.
  - Corollary 4 applies: no well-founded fixed-position matching at this designated `s` has mass above
    `1 - 3(1 - rho)/32` on Bernoulli.
  - `F_3` has fixed price, so this obstruction is about the method and not the group.
- **Twice-used letter with `m >= 2`.** Here `P = {q w̄^j}`, so `Lambda` contains `q` and `w̄`, and it is typically
  nonamenable. The dual-forest matching nevertheless reaches `1/m` on Bernoulli. It does so by changing the matched
  position from cell to cell, which is outside the class of Corollary 7. So the obstruction does not overreach.

## 6. What survives, and where the argument stops

- **Variable positions.** Suppose each cell chooses its removed edge among several positions, Borel in the cell.
  Then the children of an edge depend on the choices of neighbouring cells. Inclusion (H1) is uniform in `p in P`
  only when the position is fixed, and that uniformity is what makes every `X_k` almost invariant under all of
  `Lambda`. The dual-forest matching lives here. Any Bernoulli route to `fpbs-morse-deficit-vanishes-for-full-presentations`
  for a one-relator group with every letter used at least three times, and with every `<P>` nonamenable, must use
  variable positions or longer trivial words.
- **Proper powers with transversal modulation.** For `m >= 2`, a transversal `C` may depend on `W`, or `A ⊆ C` may
  be arbitrary. Children then exist only when `p.x` is the chosen representative, and (H1) fails. This is the
  refined class, and it is open.
- **Generation without well-foundedness.** PW's graphing only needs `s.x` and `x` to remain connected. Connectivity
  may run through van Kampen diagrams other than the `theta`-tree, so it is not a Morse matching. Theorem 2 says
  nothing about such subgraphings. For the Morse deficit, however, (M3) is part of the definition.
