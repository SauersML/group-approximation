# Periodic quantum tilings obstruct finite presentation of derived full groups

Lane `ex2-labbe-relation-climbing`, 2026-09-13. Unreviewed. It backs:
- `zd-derived-full-group-fp-excludes-periodic-quantum-tilings` (established, unreviewed);
- `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale` (open);
- the route `labbe-not-fp-via-periodic-quantum-tilings`.

## 0. Summary

1. **Theorem 1.** Let `X ⊆ A^(Z^2)` be a free minimal SFT and `G = D([[Z^2 ~ X]])`. If `G` is
   finitely presented, there is `D_0` such that for every `D >= D_0` and every field `k` the local
   tiling algebra `A_D(X, k)` of the ring lane has no nonzero finite-dimensional module.
2. **Corollary 2.** A periodic quantum tiling of `X` at every scale refutes finite presentation of `G`.
   A classical periodic point is the case `W = k`; in dimension one this recovers the known
   obstruction (Remark 2.2).
3. **Shape for Labbé's shift.** Such a tiling has no one-dimensional composition factor, and none of
   dimension 2 if `Omega_U` is wall-rigid (`periodic-quantum-tilings-refute-quantum-rigidity`). Only
   contextual families can work.
4. **Positive side.** A proof that `D([[Omega_U]])` is finitely presented must exclude these
   tilings at large scale. That is a finite-dimensional piece of quantum rigidity, so the group
   problem contains part of `labbe-wang-shift-crossed-product-is-finitely-presented`.
5. **Negative side.** A new kind of approximant, independent of LEF as far as known: a nontrivial
   finite-dimensional linear quotient of the local presentation (finite over a finite field), built
   from operator-valued tilings instead of colourings.
6. **Section 4 (data, not a theorem).** Infinite-dimensional families also give representations of
   every local presentation. The operator form of ChJN's nested commutator keeps its 3-cycle form
   for the nilpotent-difference pairs tested and loses it for most random pairs. Whether finite
   presentation of `G` forces full quantum rigidity is open.

## 1. Setting and the unit map

- `X`, `R_1`, `R >= R_1 + 2` and the rule 3-cycles `S = {s(pi, e)}` are as in
  `zd-derived-full-group-fp-forces-finite-type-proof`. `S` generates `G`, which is finitely
  generated, infinite and simple (`minimal-z2-subshift-derived-full-groups-are-fg-simple`).
- `k` is a field and `R_X = LC(X, k) ⋊ Z^2`, with `u^g f u^(-g) = f o sigma^g`,
  `(sigma^g x)(z) = x(z + g)`, `e_a = chi[x(0) = a]` and `P_h^a = u^h e_a u^(-h) = chi[x(h) = a]`.
- `A_D` is the local presentation of `research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md`,
  Section 1. Its generators are `e_a` and `u_1^(±1)`, `u_2^(±1)`, and its relations are:
  - (R1) the `u_i` are invertible and commute;
  - (R2) the `e_a` are orthogonal idempotents summing to 1;
  - (R3) `e_a P_h^b = P_h^b e_a` for `|h| <= 2D`;
  - (R4) `prod_(h ∈ B_D) P_h^(pi(h)) = 0` for `pi ∉ L_(B_D)(X)`.
- **Lemma 1.2 of that artifact.** If `xi` is a linear combination of words of length `<= D` in the
  generators and `xi = 0` in `R_X`, then `xi = 0` in `A_D`.
- **Units of the full group.** For `g ∈ [[Z^2 ~ X]]` with `g(x) = sigma^(kappa_g(x)) x` put
  `U_g = sum_v chi[kappa_(g^(-1)) = v] u^v`.
  - Then `U_g U_h = U_(gh)`. The coefficient of `u^t` in `U_g U_h` is the sum over `v + w = t` of
    `chi[kappa_(g^(-1)) = v] · (chi[kappa_(h^(-1)) = w] o sigma^v)`. That is the indicator of
    `{kappa_((gh)^(-1)) = t}`, by the cocycle identity
    `kappa_(h^(-1) g^(-1))(x) = kappa_(g^(-1))(x) + kappa_(h^(-1))(g^(-1) x)`.
  - For `s ∈ S`, each `chi[kappa_s = v]` is a finite sum of cylinder indicators on `B(R + 2)`,
    each a product of `P_h^a`. Fix such an expression `Û_s`, a combination of words of length
    `<= l_0 = l_0(R)`.

## 2. Theorem 1

**Theorem 1.** Suppose `G = <S | ℛ>` with `ℛ` finite and every relator of length `<= L`. There is
`D_0 = D_0(L, R)` such that for every `D >= D_0` and every field `k`, every finite-dimensional
`A_D`-module is zero.

*Proof.*
1. **The constant.** Let `D_0 >= r` bound the lengths of the following combinations, all of which
   vanish in `R_X`:
   - (i) `Û_s Û_(s^(-1)) - 1` and `Û_(s^(-1)) Û_s - 1` for `s ∈ S` (the set `S` is symmetric,
     since `s(pi, -e) = s(pi, e)^(-1)`);
   - (ii) `Û_(s_1) ... Û_(s_m) - 1` for each relator `s_1 ... s_m ∈ ℛ`, letters in `S`;
   - (iii) identity (★) of step 4, for every legal `pi` on `B(R)`;
   - (iv) `sum_(pi ∈ L_(B(R))(X)) chi[pi] - 1`.
2. **`G` maps to the units of `A_D`.** By Lemma 1.2, (i) and (ii) vanish in `A_D`. So `s -> Û_s`
   defines a homomorphism from the free group on `S` to `A_D^×` that kills `ℛ`. It factors through
   a homomorphism `phi_D : G -> A_D^×`.
3. **Malcev.** Let `V` be a finite-dimensional `A_D`-module. The image `H` of `G` in `GL(V)` is
   finitely generated and linear, so it is residually finite
   (`finitely-generated-linear-groups-are-residually-finite`). `H` is a quotient of the simple group
   `G`, so `H = 1` or `H ≅ G`. An infinite simple group is not residually finite. Hence `H = 1`, and
   every `Û_s` acts on `V` as the identity.
4. **Identity (★).** Let `pi` be legal on `B(R)`, `C = [pi]` and `s = s(pi, e)`. The element `s`
   cycles three pairwise disjoint clopen sets `C, s(C), s^2(C)`, so `s^(-1)(C) ∩ C = ∅`. In `R_X`,
   `chi_C U_s chi_C = sum_v chi_C · chi[kappa_(s^(-1)) = v] · (chi_C o sigma^v) u^v`. If `x ∈ C` and
   `kappa_(s^(-1))(x) = v`, then `sigma^v x = s^(-1) x ∉ C`, so every coefficient vanishes pointwise.
   Hence
   `(★)   chi_C (U_s - 1) chi_C = -chi_C`,
   with `chi_C = prod_(h ∈ B(R)) P_h^(pi(h))`. It has bounded length, so it holds in `A_D`.
5. **Conclusion.** On `V`, `Û_s - 1 = 0`, so by (★) every `chi[pi]` acts as `0`. By (iv), `1` acts
   as `0`, and `V = 0`. ∎

**Remark 2.1.** Over a finite field `H` is finite, and Malcev's theorem is not needed.

**Remark 2.2 (calibration in dimension one; same proof, not written separately).** Replace `Z^2` by
`Z` and let `X` be an infinite minimal subshift. Legality at scale `D` is read in `L_(B_D)(X)`. A
periodic point `y` of the Markov approximation `X_N`, `N >= 2D + 1`, gives the one-dimensional family
`E_a(z) = [y(z) = a]` on `W = k`, hence a finite-dimensional module (Corollary 2 below). So
`D([[phi]])` is never finitely presented, which is Matui's theorem. In dimension two an aperiodic SFT
has no such classical family, and Theorem 1 says the only surviving finite-dimensional obstruction
of this kind is operator-valued.

## 3. Periodic quantum tilings

**Corollary 2.** Let `W != 0` be finite-dimensional, `Λ ≤ Z^2` of finite index, and `E_a(z) ∈ End_k(W)`
idempotents with `E_a(z + λ) = E_a(z)` for `λ ∈ Λ`, satisfying (Q1)–(Q3) of
`sft-crossed-product-fp-iff-quantum-rigid` at scale `D`.
- On `V = W ⊗ k[Z^2/Λ]` let `e_a` act on `W ⊗ δ_zbar` by `E_a(zbar)`, and put
  `(u^g xi)(zbar) = xi(zbar + g)`.
- Then `u^h e_a u^(-h)` acts at `zbar` by `E_a(zbar + h)`, so (R1)–(R4) hold sitewise, and `V` is a
  nonzero finite-dimensional `A_D`-module.
- By Theorem 1, if `G` is finitely presented, no such family exists once `D >= D_0`.

Over a finite field the converse holds too: every nonzero finite-dimensional `A_D`-module comes from
such a family (`periodic-quantum-tilings-refute-quantum-rigidity`, item 2). So over finite fields,
Theorem 1 says exactly that finite presentation of `G` forbids periodic quantum tilings at large
scale.

**What a refuting tiling must look like for `Omega_U`** (ring lane, established, unreviewed):
- it has no one-dimensional `C_D`-composition factor, since such a factor reads off a legal periodic
  configuration and `Omega_U` has none;
- if `Omega_U` is `D`-wall-rigid (`sft-wall-rigidity-iff-idempotent-commutator-ideal`), some
  composition factor has dimension `>= 3` and carries a noncommuting family.

**Relation to LEF.** A periodic quantum tiling over a finite field gives a nontrivial finite quotient
of `<S | relators of length <= L>` for `D >= D_0(L)` (step 5 shows nontriviality). An LEF
approximant needs injectivity on balls, which this does not provide. No implication between the two
mechanisms is known in either direction.

**Positive side.** Finite presentation of `D([[Omega_U]])` forces, for large `D` and every field,
that `A_D(Omega_U, k)` has no nonzero finite-dimensional module. `D`-quantum rigidity implies this
(item 1 of the ring node), but the converse is not known. So a proof of finite presentation must at
least prove this finite-dimensional rigidity for Labbé's tiles.

## 4. Infinite-dimensional families: first data (not a theorem)

- For any family (Q1)–(Q3) on any `W`, the ring lane's representation of `A_D` on `V = W^((Z^2))`
  composed with `phi_D` represents `<S | relators of length <= L>` for `D >= D_0(L)`. If `G` is
  finitely presented, this is a representation of `G`. Malcev does not apply. The question is
  whether relations of `G` of large radius force the observables to commute.
- Locally, `U_s` acts at a centre `w` as `1 + E_pi(w) ⊗ (c_w - 1)`, where `c_w` is the 3-cycle of
  sites and `E_pi(w)` the product of site observables. Noncommuting observables first meet in
  ChJN's Lemma A: two factors `a = 1 + P ⊗ (alpha - 1)` and `b = 1 + Q ⊗ (beta - 1)` whose site
  triples share one site.
- **Exact computation.** Script `experiments/labbe-relation-climbing/nclemma.py`, rational
  arithmetic, run on MSI in seconds.
  - Convention `[x, y] = x^(-1) y^(-1) x y`. With it `[[b^(-1), a^(-1)], [b, a]] = alpha` classically;
    the other convention gives `beta^(-1)`.
  - Common kernel, `P = [[1,0],[0,0]]`, `Q = [[1,0],[2,0]]`: the nested commutator is
    `1 + X ⊗ (alpha - 1)` with `X = PQ = PQP = P`, and the other order gives `1 + QP ⊗ (beta - 1)`.
  - Common image, `Q = [[1,2],[0,0]]`: `X = QP = PQP = P`.
  - Six random rational idempotent pairs (four of rank 1 in `k^2`; two of ranks 2 and 1 in `k^3`):
    four are not of the form `1 + X ⊗ (alpha - 1)` for any `X`. Two keep the form, with
    `X = QP = PQP`; I did not check whether those two are degenerate.
- **Reading.** The two degenerate pairs have `(P - Q)^2 = 0`. That is the local shape of the
  upper-triangular wall families of `sft-wall-rigidity-iff-idempotent-commutator-ideal`. So the
  relations of two-generator subgroups cannot see wall-type noncommutation; only relations of large
  radius could.
- **Open.** Does finite presentation of `G` force `D`-quantum rigidity of `X`, hence finite
  presentation of `R_X`? Not claimed.

## 5. Next targets

1. Search for small periodic quantum tilings of Labbé's tiles (`D = 1, 2`, over `F_2` and `F_3`,
   small `W` and `Λ`). This can only be evidence, since the route needs every large `D`.
2. The infinite-dimensional transfer of Section 4.
3. On the positive side, the finite-dimensional rigidity of Section 3 for Labbé's tiles.
