# Median matching has no Bernoulli entropy analogue; canonical hosts for deficit patterns

Lane `gk-rokhlin`, 2026-09-12. This artifact supports `median-matching-has-no-bernoulli-entropy-analogue`,
the refuted claim `median-matching-transfers-to-bernoulli-partitions`, the dead route
`leavitt-zero-supremum-via-median-matching`, and the canonical-host paragraph of
`bernoulli-rokhlin-deficit-has-a-finitary-witness`. The proofs are handwritten, with no computation.

## Summary

* **Target.** A finite configuration over `U = L_(F_2)(1,2)^x` with `Phi < log q`
  (`leavitt-units-have-zero-rokhlin-entropy-supremum`), built from the nine-leaf configuration and the
  median device of `openai-bounded-median-component-matching`, the one mechanism known to see the
  nonsoficity of `U`.
* **The device.** It has four steps:
  1. the component-size observable `M`, constant on `Gamma`-components;
  2. the median normalization `f = M/(M + m_A)`, bounded with median `1/2`;
  3. almost monotonicity under the compressors, together with the no-drift identity
     `sum_z (f(sz) - f(z)) = 0` for permutations of a finite set;
  4. coarea plus expansion, which gives `f ≈ 1/2` off a negligible set, hence equal component sizes and
     an injective matching.
* **Theorem 1 (the shift).** Let `Gamma <= G` be nonamenable. On the uniform Bernoulli shift over `G`,
  every `Gamma`-almost-invariant observable is within a fixed multiple of its defect of its mean, and
  every `Gamma`-invariant observable is constant. So step 1 yields only constants, and steps 2–4 hold
  trivially.
* **Proposition 2 (finite pieces).** On a finite `P` in `G`, the no-drift identity fails by a boundary
  term, and for nonamenable `Gamma` the boundary is at least a fixed fraction of `|P|`.
* **Where it dies (Section 3).** The device is a theorem about almost-actions on finite sets without
  boundary. Its only output that bears on a certificate is invisibility of the defect in finite models.
  The localization theorem already requires that, it is not sufficient for strictness, and it is not
  known to be sufficient for a deficit.
* **Proposition 3 (canonical hosts).** `Phi` is invariant under homomorphisms that are injective on the
  point set. Every pattern is realized exactly by its square presentation.

## 0. Setting

Conventions are those of `research/artifacts/bernoulli-deficit-witness-localization-2026-09-12.md`,
Section 0.
* `X = (A^k)^G` carries the uniform product measure `lambda` and the left shift
  `(g.x)(h) = x(g^-1 h)`. Observables transform by `(g.f)(x) = f(g^-1 . x)`.
* `S` is a finite symmetric generating set of a subgroup `Gamma <= G`. Put

  ```text
  kappa_S(Gamma)^2 = inf { sum_(s in S) || lambda_Gamma(s) xi - xi ||^2 : xi in l^2(Gamma), ||xi|| = 1 },
  h_S(Gamma)       = inf { |S Q \ Q| / |Q| : Q finite nonempty in Gamma }.
  ```

  Both are positive exactly when `Gamma` is nonamenable, by Kesten's criterion and Følner's criterion.
  Infinite Kazhdan groups are nonamenable. For the nine-leaf pair, `Gamma = EL_alpha(R) ≅ EL_3(R)`.

## 1. Theorem 1: ergodic degeneracy on the shift

**Theorem 1.** Let `Gamma <= G` be nonamenable, with finite symmetric generating set `S`. For every
`f in L^2(X, lambda)`,

```text
|| f - integral f d lambda ||_2^2  <=  kappa_S(Gamma)^-2  sum_(s in S) || s.f - f ||_2^2.
```

In particular, every `Gamma`-invariant `f` is a.e. constant.

*Proof.*
1. *Basis.* Choose an orthonormal basis `b_0 = 1, b_1, ..., b_r` of `L^2(A^k, uniform)`. For a finitely
   supported `omega: G -> {0, ..., r}`, put `b_omega(x) = prod_(h in supp omega) b_(omega(h))(x(h))`.
   These functions form an orthonormal basis of `L^2(X)`, and `omega = 0` gives the constants. The shift
   permutes them: `g.b_omega = b_(g.omega)` with `(g.omega)(h) = omega(g^-1 h)`, since
   `b_omega(g^-1 . x) = prod_h b_(omega(h))(x(g h))`.
2. *Koopman decomposition.* Hence `L^2_0(X)` is the direct sum, over the `G`-orbits of nonzero names
   `omega`, of the permutation representations `l^2(G/K_omega)`. Here `K_omega` fixes the finite
   nonempty set `supp omega`, so `K_omega` lies in `supp(omega) f_0^-1` for any `f_0` in the support, and
   is finite.
3. *Embedding in the regular representation.* For finite `K`, `xi -> |K|^-1/2 xi o p`, with
   `p: G -> G/K`, embeds `l^2(G/K)` isometrically and equivariantly in `l^2(G)`. Restricted to `Gamma`,
   `l^2(G)` is the direct sum over right cosets `Gamma c` of copies of `l^2(Gamma)`. So `L^2_0(X)`,
   restricted to `Gamma`, embeds in a direct sum of copies of `lambda_Gamma`.
4. *Gap.* On a direct sum `xi = (xi_i)`,
   `sum_s || s xi - xi ||^2 = sum_i sum_s || s xi_i - xi_i ||^2 >= kappa_S^2 sum_i ||xi_i||^2`.
   Apply this to `f - integral f`, which lies in `L^2_0`, and note `s.(f - c) - (f - c) = s.f - f`. QED.

**Consequence for step 1.** In the device, `M` and `f` are functions of the `Gamma`-component. Their
analogue on `X` is a bounded measurable observable that is `Gamma`-invariant, or almost invariant with
defect tending to zero. By Theorem 1 it is constant, or tends to its mean in `L^2`. The median
normalization is then `1/2` up to `o(1)`. Almost monotonicity, no drift and coarea concentration all hold
with no hypothesis on the compressors, and there is a single component, so no matching.

*Contrast.* When `Gamma` has a finite orbit on the index set of a generalized Bernoulli shift — for
example over `G/H` with `Gamma ∩ g H g^-1` of finite index in `Gamma` — the product of the coordinates on
that orbit is a nonconstant `Gamma`-invariant observable. That requires a non-free action, which is the
setting of `compressed-coset-shifts-carry-strict-equivariant-embeddings`.

## 2. Proposition 2: finite pieces carry proportional boundary

**Proposition 2.** Let `Gamma <= G` and `S` be as above, and let `P` be a finite nonempty subset of `G`.

1. `|S P \ P| >= h_S(Gamma) |P|`. So some `s in S` has `|s P \ P| >= h_S(Gamma) |P| / |S|`.
2. For every `f: P -> [0, 1]` and `s in S`,

   ```text
   sum_(z in P ∩ s^-1 P) ( f(s z) - f(z) )  =  sum_(z in P \ s^-1 P) f(z)  -  sum_(y in P \ s P) f(y),
   ```

   and both sums on the right lie in `[0, |s P \ P|]`.

*Proof.*
1. Split `P` into the pieces `P ∩ Gamma c = Q_c c` over right cosets, with `Q_c` finite in `Gamma`. Then
   `S (Q_c c) = (S Q_c) c` lies in `Gamma c`, so
   `|S P \ P| = sum_c |S Q_c \ Q_c| >= h_S sum_c |Q_c| = h_S |P|`.
2. `sum_(z in P ∩ s^-1 P) f(s z) = sum_(y in P ∩ s P) f(y) = sum_P f - sum_(P \ s P) f`, and
   `sum_(z in P ∩ s^-1 P) f(z) = sum_P f - sum_(P \ s^-1 P) f`. Subtract. Finally
   `s(P \ s^-1 P) = s P \ P`, and `|P \ s P| = |s P| - |P ∩ s P| = |s P \ P|`. QED.

**Consequence for step 3.** On a finite set that the generators permute, the no-drift identity is exact,
and the positive and negative variations of `f` along each generator are equal. On a finite piece of `G`
they can differ by up to `|s P \ P|`, which for nonamenable `Gamma` is at least `h_S |P| / |S|` for some
generator. That is the order of `|P|`, so the coarea step yields no concentration. The same holds after
adding the compressors to `S`.

## 3. Where the translation dies

A deficit certificate is an existence statement inside `G`: a code `psi` and translates whose partition
process decodes `x(1)` cheaply. The median device is a non-existence theorem about almost-actions on
finite sets that every generator permutes. Theorem 1 and Proposition 2 show that neither setting of a
certificate has such a set.
* On the shift there is one `Gamma`-component.
* On a finite piece, the boundary is proportional to size.

What survives is the device's output on models. Every almost-action on a finite set makes the defect
`[u z u^-1, gamma]` act almost trivially (`surjunctive-groups-carry-invisible-rigid-defects`, part 1; for
`U`, every element does).
* This is necessary for a deficit (`sofic-radical-localizes-bernoulli-deficit-witnesses`).
* For strict automata it is not sufficient: the surjunctive Kun–Thom wreaths carry nontrivial invisible
  rigid defects (part 2 of the same node).
* For deficits it is not known to be sufficient, since INF for those wreaths is open.

So the device supplies a hypothesis a certificate must satisfy. It does not construct a partition.

The exact missing step is `median-matching-transfers-to-bernoulli-partitions`. It asks for a nonconstant
`Gamma`-invariant observable on the shift over `U`, or a finite nonempty set in `U` preserved by a
generating set of `Gamma`. Theorem 1 and Proposition 2(1) refute both.

What a construction still needs is a mechanism with no finite-model counterpart, a code that uses the
infinite-index compression `u Gamma u^-1 < Gamma` inside `U` itself. The induced infinite-to-one map
`Gamma g -> Gamma u g` on `Gamma \ U` is well defined. On coset shifts it gives strict embeddings
(`compressed-coset-shifts-carry-strict-equivariant-embeddings`). On the free shift every coordinate
already carries an independent symbol, and no rearrangement along cosets stores it more cheaply. No code
is known.

## 4. Proposition 3: canonical hosts for deficit patterns

Let `(k, E, F, psi)` be a configuration over `G` with `E` and `F` nonempty, and put `P = FE ∪ {1}`.

**Proposition 3.**
1. Let `pi` be a homomorphism from `K = <E ∪ F>` to a group `G'` that is injective on `P`. Then `pi` is
   injective on `E` and on `F`, `(k, pi(E), pi(F), psi)` is a configuration over `G'` with the same
   incidence pattern, and `Phi` is unchanged.
2. Let `P_pat` be the group generated by letters `e~` (for `e in E`) and `f~` (for `f in F`), with
   relators `f~ e~ = f'~ e'~` whenever `f e = f' e'` in `G`, and `f~ e~ = 1` whenever `f e = 1`. The
   homomorphism `P_pat -> K` sending letters to elements is injective on the points `f~ e~` and `1`. So
   `P_pat` realizes the pattern exactly, with the same `Phi`.
3. Hence `G` has a deficit at `q` exactly when some square presentation carries a deficit pattern and
   maps to `G` injectively on its points.
4. Merging points is not monotone. The trivial group has no deficit, and a free group has none but
   surjects onto every finitely generated group. Deficits pass along homomorphisms injective on the
   points, and nothing more is claimed.
5. By Corollary 2 of the localization artifact, `P_pat` of a deficit pattern is nonsofic, and no
   homomorphism from `P_pat` to a sofic group is injective on its points.

*Proof.*
1. If `f != f'`, then `f e != f' e` for `e in E`, so injectivity on `P` forces injectivity on `F`.
   Likewise for `E`. Coincidences and equalities with `1` survive a homomorphism, and no new ones appear
   by injectivity on `P`, which contains `1`. `Phi` depends only on the pattern.
2. The relators hold in `K`, so the map is a homomorphism. If `f~ e~ = f'~ e'~` in `P_pat`, then
   `f e = f' e'` in `K`, and that relator was imposed. So distinct pattern points stay distinct in
   `P_pat`, and exactly the coincidences of `G` hold there. The same argument applies to `1`.
3. By (1) and (2) together.
4. The trivial group has one point, and the degenerate case of Theorem 1 of the localization artifact
   gives `Phi = log q`. Free groups are sofic.
5. Apply (1) to a sofic target and use Corollary 2 there. QED.

For a certificate over `U`, then, the object is one finitely presented group with relators of length 2
and 4, a code `psi`, and a homomorphism to `U` injective on the points. The last condition is checkable
through the decidable word problem of `U`.
