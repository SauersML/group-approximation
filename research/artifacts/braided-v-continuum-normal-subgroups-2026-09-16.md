# Braided V has continuum many normal subgroups, so some quotient is not finitely presented (Zaremsky Problem 2.10, second part)

Lane swarm-zaremsky-2-10-braided-v-hopfia, 2026-09-16. Status: complete argument. Refereed by the swarm landing
referee on 2026-09-16 (verdict and checks recorded in `notes/zaremsky-2-10-braided-v-hopfian-swarm-2026-09-16.md`,
section "Referee (2026-09-16)"); no independent human review yet.

Main result (§5): `V_br` has `2^aleph_0` normal subgroups, all inside `[P_br, P_br]`, and an infinite strictly
ascending chain of normal subgroups. Hence `V_br` fails max-n, and some quotient of `V_br` (for example
`V_br / N_infinity` in §5) is not finitely presented. Together with the ESTABLISHED claim
`braided-thompson-v-is-hopfian`, this answers Problem 2.10: `V_br` is Hopfian, but not every quotient is
finitely presented.

The method: every normal subgroup `M` of `B_3` inside `[PB_3, PB_3]` extends to a normal subgroup `N_M` of
`V_br` whose 3-strand stage is exactly `M` (§2, Theorem A). `B_3` has continuum many such `M`, because the
relative multiplier `PB_3'' / [PB_3, PB_3'']` is a free-metabelian Schur multiplier of infinite rank (§3–§4).

## 0. Setting and sources

Notation follows `research/artifacts/zp-braided-v-hopfian-2026-09-13.md` §0. `V_br` is the Brin–Dehornoy
braided Thompson group of triples `(T_-, b, T_+)` modulo expansion. `P_br = {(T, p, T)}` is the kernel of
`V_br -> V`. `PB_T = {(T, p, T) : p in PB_n}` for a tree `T` with `n = n(T)` leaves, and
`psi_T : PB_T -> PB_n` is `(T, p, T) -> p`. `clone_k = clone_k^n` is Zaremsky's `kappa_k^n`.

[Z] M. C. B. Zaremsky, *On normal subgroups of the braided Thompson groups*, arXiv:1403.8132v2
(Groups Geom. Dyn.). The LaTeX source was fetched from arXiv on 2026-09-16 and read verbatim. Theorem-like
environments share one counter numbered within sections, and §4 is "Normal subgroups under P_br".

- Introduction: `V_br` "is finitely presented"; `F_br` "is finitely presented" (citing Brady–Burillo–Cleary–Stein,
  arXiv:math/0603548).
- Cloning maps: "Let kappa_k^n: B_n -> B_{n+1} be the injective function that takes a braid and bifurcates the
  k-th strand into two parallel strands, where we number the strands at the bottom." Expansion rule:
  "(T_-,b,T_+) = (T_- ∪ lambda_{rho_b(k)}, kappa_k^n(b), T_+ ∪ lambda_k)". Also: "Restricted to PB_n, the cloning
  maps kappa_k^n: PB_n -> PB_{n+1} are group homomorphisms".
- Proposition 4.1: "The subgroups of P_br are in one-to-one correspondence with the complete coherent families
  of subgroups of the PB_T." After its proof: "given any subgroup G ≤ P_br, the unique complete coherent family
  that generates G is (PB_T ∩ G)_T."
- After Lemma 4.2: "the normal subgroups of F_br contained in P_br are obtained precisely by choosing a normal
  subgroup G_n ◁ PB_n for each n such that for every 1 ≤ k ≤ n, we have:
  kappa_k^n(PB_n) ∩ G_{n+1} = kappa_k^n(G_n)." Below, (CC) denotes this equation. Also:
  "Th(G_*) = {(T,p,T) | T has n leaves and p ∈ G_n}."
- Lemma 4.3: "Let (G_n) be a sequence satisfying Equation (CC), so Th(G_*) is normal in F_br. Then Th(G_*) is
  normal in V_br if and only if each G_n ≤ PB_n is normal in B_n." Its proof uses
  `(S,b,T)(T,p,T)(T,b^{-1},S) = (S, b p b^{-1}, S)`.
- Lemma 4.4 (m-loose sequences satisfy (CC)), from its proof: "Let pi_S: PB_n -> PB_m be the map that deletes
  all those strands not numbered by elements of S. Define S(k) := {i_1+eps_1, …, i_m+eps_m}, where eps_j is 0 if
  i_j ≤ k and is 1 if k < i_j. Then pi_{S(k)} ∘ kappa_k^n = pi_S."
- After Lemma 4.4: `Lambda_n(2) = [PB_n, PB_n]`, `Th(Lambda_*(2)) = [P_br, P_br]`, and the `Th(Lambda_*(m))` form a
  descending chain. Question 4.7: "Are F_br and/or V_br Hopfian?"

Classical inputs:

- Artin combing for `PB_3`;
- Hopf's formula `H_2(F/R) = (R ∩ [F,F]) / [F,R]`;
- the Lyndon–Hochschild–Serre spectral sequence;
- `H_p(Gamma; Z Gamma) = 0` for `p > 0`;
- `H_2(A) = Λ^2 A` for a free abelian group `A`;
- Maschke's theorem.

Neumann's lemma is proved in §5.

## 1. Strand deletion identities

For a geometric braid, deleting a set of strands gives a braid on the remaining strands. Deletion is compatible
with isotopy and with stacking, provided the kept strands of the factors match at each interface. For
`S ⊆ {1..n}`, `pi_S : PB_n -> PB_{|S|}` keeps the strands numbered by `S` and renumbers them in order. It is a
homomorphism.

- (D1) Conjugation. Let `p ∈ PB_n`, `b ∈ B_n` and `|S| = m`. In the stack `b p b^{-1}`, the strands that end at
  positions `S` pass through the middle factor `p` at a set of positions `S_1` with `|S_1| = m`. Keeping those
  strands in each factor gives `pi_S(b p b^{-1}) = beta · pi_{S_1}(p) · beta^{-1}`, with `beta ∈ B_m`. Here `beta`
  is `b` with the other strands deleted, and the `b^{-1}` factor with the same strands kept is `beta^{-1}`.
- (D2) Cloning, generic triples. Let `c_k : {1..n+1} -> {1..n}` be `c_k(i) = i` for `i ≤ k` and `c_k(i) = i-1`
  for `i > k`. If `S' ⊆ {1..n+1}` contains at most one of `k, k+1`, then `c_k` is injective on `S'` and
  `pi_{S'} ∘ clone_k = pi_{c_k(S')}` on `PB_n`. Keeping one clone of strand `k` is the same as keeping strand `k`.
  In particular, `S(k)` of [Z, Lemma 4.4] is such an `S'` with `c_k(S(k)) = S`.
- (D3) Cloning, degenerate triples. If `S' = {k, k+1, j'}` with `j' ∉ {k, k+1}`, then
  `pi_{S'} ∘ clone_k = clone_{k''}^2 ∘ pi_{{k, c_k(j')}}`, where `k''` is the position of `k` in `{k, c_k(j')}`.
  Both kept clones are parallel copies of strand `k`. This composite is a homomorphism `PB_n -> PB_3` that factors
  through `PB_2 ≅ Z`, so it kills `[PB_n, PB_n]`.
- (D4) Left inverse. `delta := pi_{{1..n+1} \ {k+1}}` satisfies `delta ∘ clone_k = id` on `PB_n`, by (D2). So
  `clone_k` is injective. If `clone_k(p) ∈ [PB_{n+1}, PB_{n+1}]`, then `p = delta(clone_k(p)) ∈ [PB_n, PB_n]`.

## 2. Theorem A: three-strand transfer

Let `M ◁ B_3` with `M ≤ [PB_3, PB_3]`. For `n ≥ 1` put

    G_n(M) := { p ∈ [PB_n, PB_n] : pi_S(p) ∈ M for every 3-element S ⊆ {1..n} }.

For `n ≤ 2`, `[PB_n, PB_n] = 1`, so `G_n(M) = 1`.

**Theorem A.**

1. `G_n(M) ◁ B_n` for every `n`.
2. `(G_n(M))_n` satisfies (CC) for all `1 ≤ k ≤ n`.
3. `N_M := Th(G_*(M))` is a normal subgroup of `V_br` with `N_M ≤ [P_br, P_br]`.
4. For every tree `T` with 3 leaves, `psi_T(N_M ∩ PB_T) = M`.

Consequently `M ≤ M'` if and only if `N_M ≤ N_{M'}`. In particular `M -> N_M` is injective, and a strictly
ascending chain of `M`'s gives a strictly ascending chain of `N_M`'s.

*Proof.*

1. `G_n(M)` is the intersection of `[PB_n, PB_n]` with the preimages `pi_S^{-1}(M)` under homomorphisms, so it
   is a subgroup. Let `p ∈ G_n(M)` and `b ∈ B_n`.
   - `b p b^{-1} ∈ [PB_n, PB_n]`, because `PB_n ◁ B_n` and the commutator subgroup is characteristic.
   - For each 3-subset `S`, (D1) gives `pi_S(b p b^{-1}) = beta · pi_{S_1}(p) · beta^{-1}` with `beta ∈ B_3`.
     Since `pi_{S_1}(p) ∈ M` and `M ◁ B_3`, this lies in `M`.
2. (⊇) Let `p ∈ G_n(M)`. Since `clone_k` is a homomorphism on `PB_n`, `clone_k(p) ∈ [PB_{n+1}, PB_{n+1}]`. Let
   `S' ⊆ {1..n+1}` be a 3-subset.
   - If `S'` contains at most one of `k, k+1`, then by (D2) `pi_{S'}(clone_k(p)) = pi_{c_k(S')}(p) ∈ M`.
   - If `S' ⊇ {k, k+1}`, then by (D3) `pi_{S'}(clone_k(p)) = 1 ∈ M`, because `p ∈ [PB_n, PB_n]`.

   So `clone_k(p) ∈ G_{n+1}(M)`.

   (⊆) Let `p ∈ PB_n` with `q := clone_k(p) ∈ G_{n+1}(M)`. By (D4), `p ∈ [PB_n, PB_n]`. For a 3-subset
   `S ⊆ {1..n}`, (D2) gives `pi_S(p) = pi_{S(k)}(q) ∈ M`. So `p ∈ G_n(M)`, and
   `clone_k(PB_n) ∩ G_{n+1}(M) = clone_k(G_n(M))`.
3. By 1, each `G_n(M)` is normal in `PB_n`. By 2 it satisfies (CC), so `Th(G_*(M))` is a normal subgroup of
   `F_br` [Z, §4 after Lemma 4.2]. By 1 and [Z, Lemma 4.3] it is normal in `V_br`. Since `G_n(M) ≤ [PB_n, PB_n]`,
   `N_M ≤ Th(Lambda_*(2)) = [P_br, P_br]`.

   Self-contained check of the parts used:
   - Every representative of an element of `P_br` has the form `(T, p, T)` with `p` pure. Expanding at leaf `k`
     gives `(T ∪ lambda_k, clone_k(p), T ∪ lambda_k)`, since `rho_p = id`.
   - Reductions of `(T, p, T)` are again of this form: if `clone_k(b)` is pure then `b` is pure, and then both
     trees agree.
   - Two equivalent triples have a common expansion. Because (CC) holds and `clone_k` is injective,
     `p ∈ G_{n(T)}` if and only if `clone_k(p) ∈ G_{n(T)+1}`.
   - So whether `p ∈ G_{n(T)}` does not depend on the chosen representative `(T, p, T)`, and
     `Th(G_*)` is a well-defined subset of `P_br`.
   - It is a subgroup: two elements can be written over a common tree `T`, and
     `(T,p,T)(T,p',T) = (T, p p', T)`.
   - Normality in `V_br` is the displayed computation of [Z, Lemma 4.3]. Given `h ∈ V_br` and `g ∈ N_M`, expand
     until `h = (S, b, T)` and `g = (T, p, T)`. Then `h g h^{-1} = (S, b p b^{-1}, S)` with
     `b p b^{-1} ∈ G_{n(T)}(M)` by 1.
4. By the well-definedness in 3, `(T, p, T) ∈ N_M` if and only if `p ∈ G_3(M)`. The only 3-subset of `{1,2,3}`
   is `{1,2,3}`, and `pi_{{1,2,3}} = id`. So `G_3(M) = M ∩ [PB_3, PB_3] = M`.

For the consequence: if `M ≤ M'`, then `G_n(M) ≤ G_n(M')` for all `n`, so `N_M ≤ N_{M'}`. If `N_M ≤ N_{M'}`, then
`M ≤ M'` by 4. QED.

*Examples.*

- `M = [PB_3, PB_3]`: the condition on `pi_S` is automatic, so `G_n = [PB_n, PB_n]` and `N_M = [P_br, P_br]`.
- `M = 1`: for `n ≥ 3`, `G_n(1) = Lambda_n(3)`, Zaremsky's 3-loose braids. A 3-loose braid has all two-strand
  deletions trivial, so it lies in `Lambda_n(2) = [PB_n, PB_n]`.

## 3. Lemma B: the relative multiplier of `PB_3` has infinite rank

Artin combing:

- `F := ker(pi_{{1,2}} : PB_3 -> PB_2)` is free on `A_13, A_23`.
- `Delta^2 = (sigma_1 sigma_2)^3` is central in `B_3`, and `pi_{{1,2}}(Delta^2) = A_12` generates `PB_2 ≅ Z`.

Hence `F ∩ <Delta^2> = 1` (since `pi_{{1,2}}` is injective on `<Delta^2>`) and `F <Delta^2> = PB_3`. So
`PB_3 = F × <Delta^2>`.

It follows that `PB_3' = F'`, `PB_3'' = F''` and `[PB_3, PB_3''] = [F, F'']`. Put

    Q_2 := PB_3'' / [PB_3, PB_3''] = F'' / [F, F''].

**Lemma B.** `Q_2` contains a free abelian subgroup of countably infinite rank. In particular `Q_2` is not
finitely generated, and `dim_Q (Q_2 ⊗ Q) = aleph_0`.

*Proof.*

1. Let `M_2 := F / F''`, the free metabelian group of rank 2. Since `F'' ≤ F'`, Hopf's formula gives
   `H_2(M_2; Z) ≅ (F'' ∩ F') / [F, F''] = Q_2`.
2. Put `A := F'/F'' = M_2'` and `Gamma := M_2 / A = F/F' ≅ Z^2`. As a `Z Gamma`-module, `A = H_1(F')` is `H_1(X)`,
   where `X` is the covering of the wedge of two circles with group `F'`.
   - `X` is the Cayley graph of `Z^2` for the standard basis, that is, the 1-skeleton of the square tiling of
     `R^2`. The deck action of `Gamma` corresponds to the conjugation action of `F/F'` on `F'/F''`.
   - The tiling is contractible, so its cellular chain complex `0 -> C_2 -> C_1 -> C_0 -> Z -> 0` is exact.
     Hence `H_1(X) = ker d_1 = im d_2 ≅ C_2`.
   - `Gamma` permutes the square 2-cells freely and transitively, so `C_2 ≅ Z Gamma`.

   So `A ≅ Z Gamma`.
3. Use the LHS spectral sequence of `1 -> A -> M_2 -> Gamma -> 1`, with `E^2_{p,q} = H_p(Gamma; H_q(A))`.
   - Differentials leaving `E_{0,2}` land in negative `p`, so they vanish.
   - Differentials entering `E_{0,2}` start at `E^2_{2,1} = H_2(Gamma; Z Gamma) = 0` or at
     `E^3_{3,0}`, a subquotient of `H_3(Z^2; Z) = 0` (the torus is a 2-dimensional `K(Z^2, 1)`).

   So `E^inf_{0,2} = E^2_{0,2} = H_2(A)_Gamma`. It is the bottom filtration term of `H_2(M_2)`, namely the image of
   `H_2(A) -> H_2(M_2)`, and so it is a subgroup of `H_2(M_2)`.
4. `A` is free abelian on the set `Gamma` (written additively). Fix a total order on `Gamma`. Then
   `H_2(A) = Λ^2 A` has basis `{g ∧ h : g < h}`, and `t ∈ Gamma` sends `g ∧ h` to `(t+g) ∧ (t+h)`, which is plus
   or minus a basis vector.
5. `Gamma` acts freely on 2-element subsets. If `t + {g, h} = {g, h}` with `t ≠ 0`, then `t+g = h` and `t+h = g`.
   So `2t = 0`, hence `t = 0` in `Z^2`, a contradiction.
   - The orbits are indexed by `R := (Gamma \ {0}) / ±`, via `{g, h} -> ±(h - g)`.
   - Fix a representative `r` of each class. Up to signs, `{t · (0 ∧ r) : t ∈ Gamma}` is the part of the basis in
     that orbit.
   - So `Λ^2 A ≅ ⊕_{r ∈ R} Z Gamma · (0 ∧ r)` is a free `Z Gamma`-module of rank `|R| = aleph_0`.
6. `(Z Gamma)_Gamma = Z`, so `H_2(A)_Gamma ≅ Z^{(R)}`, free abelian of countably infinite rank. By 1 and 3 it
   embeds in `Q_2`.
   - Subgroups of finitely generated abelian groups are finitely generated, so `Q_2` is not finitely generated.
   - `Q` is flat, so `Q^{(R)} ⊆ Q_2 ⊗ Q`, and `Q_2` is countable. QED.

## 4. Corollary C: continuum many normal subgroups of `B_3` inside `PB_3''`

`B_3` normalizes `PB_3`, hence normalizes `PB_3''` and `[PB_3, PB_3'']`, so it acts on `Q_2` by conjugation.
`PB_3` acts trivially: for `p ∈ PB_3` and `x ∈ PB_3''`, `p x p^{-1} x^{-1} ∈ [PB_3, PB_3'']`. So `Q_2` is a
`Z[S_3]`-module, with `S_3 = B_3 / PB_3`.

Subgroups `M` with `[PB_3, PB_3''] ≤ M ≤ PB_3''` correspond bijectively to subgroups of `Q_2`. Such an `M` is
normal in `B_3` if and only if its image is `B_3`-invariant, that is, `S_3`-invariant. Every such `M` satisfies
`M ≤ PB_3'' ≤ [PB_3, PB_3]`, so it is admissible in Theorem A.

**Corollary C.**

- (a) There is an infinite strictly ascending chain `M_1 < M_2 < …` of normal subgroups of `B_3` inside
  `PB_3''`.
- (b) There are `2^aleph_0` normal subgroups of `B_3` between `[PB_3, PB_3'']` and `PB_3''`.

*Proof.*

- (a) For `u_1, …, u_k ∈ Q_2`, `W(u_1..u_k) := Σ_i Z[S_3] u_i` is the smallest `S_3`-invariant subgroup containing
  them. As an abelian group it is generated by the at most `6k` elements `sigma u_i`, so by Lemma B it is not all
  of `Q_2`. Choose `u_{k+1} ∉ W(u_1..u_k)` inductively. The preimages in `PB_3''` of the `W(u_1..u_k)` form the
  chain.
- (b) `V := Q_2 ⊗ Q` is a `Q[S_3]`-module of dimension `aleph_0`. By Maschke's theorem `Q[S_3]` is semisimple, so
  `V = ⊕_{i ∈ I} V_i` with each `V_i` simple. Each `dim V_i ≤ 6`, so `I` is countably infinite.
  - For `J ⊆ I`, put `W_J := ⊕_{i ∈ J} V_i` and `P_J := {x ∈ Q_2 : x ⊗ 1 ∈ W_J}`. Each `P_J` is `S_3`-invariant.
  - Suppose `P_J = P_{J'}` and `w ∈ W_J`. Write `w = x ⊗ (1/m)` with `x ∈ Q_2`. Then `x ⊗ 1 = m w ∈ W_J`, so
    `x ∈ P_J = P_{J'}` and `m w ∈ W_{J'}`. Hence `w ∈ W_{J'}`.
  - By symmetry `W_J = W_{J'}`, so `J = J'`.

  There are `2^aleph_0` subsets `J`. QED.

## 5. Theorem D: `V_br` fails max-n, and some quotient is not finitely presented

**Lemma N (B. H. Neumann).** Let `G` be generated by a finite set `X` and let `N ◁ G`. If `G/N` is finitely
presented, then `N` is the normal closure in `G` of finitely many elements.

*Proof.*

1. Set up the maps.
   - `eps : F(X) -> G` is the natural surjection, and `nu : F(X) -> H := G/N` is its composite with the quotient
     map. Put `K := ker nu = eps^{-1}(N)`.
   - `<Y | U>` is a finite presentation of `H`, with `mu : F(Y) -> H`.
   - `alpha : F(Y) -> F(X)` and `beta : F(X) -> F(Y)` are homomorphisms with `nu ∘ alpha = mu` and
     `mu ∘ beta = nu`. They exist because `F(X)` and `F(Y)` are free and `nu`, `mu` are onto.
   - `J` is the normal closure of the finite set `alpha(U) ∪ {x^{-1} alpha(beta(x)) : x ∈ X}`.
2. `J ≤ K`: `nu(alpha(u)) = mu(u) = 1`, and `nu(x^{-1} alpha beta(x)) = nu(x)^{-1} mu(beta(x)) = 1`.
3. `K ≤ J`. Define `theta : H -> F(X)/J` by `theta(mu(w)) = alpha(w) J`. This is well defined because
   `ker mu = <<U>>` and `alpha(U) ⊆ J`. Let `nubar : F(X)/J -> H` be the induced map. Then
   `theta(nubar(xJ)) = alpha(beta(x)) J = xJ` for `x ∈ X`, so `theta ∘ nubar = id`. Hence `nubar` is injective,
   which means `K = J`.
4. `N = eps(K) = eps(J)`. Since `eps` is onto, this is the normal closure in `G` of the finite set
   `eps(alpha(U) ∪ {x^{-1} alpha beta(x)})`. QED.

**Theorem D.**

- (a) `V_br` has exactly `2^aleph_0` normal subgroups. Continuum many of them, `{N_M}`, lie in `[P_br, P_br]`.
- (b) `N_{M_1} < N_{M_2} < …` is a strictly ascending chain of normal subgroups of `V_br`. Its union `N_infinity`
  is a normal subgroup that is not the normal closure of any finite set, so `V_br` fails max-n.
- (c) `V_br / N_infinity` is not finitely presented. Of the continuum many quotients `V_br / N_M` from
  Corollary C(b), all but countably many are not finitely presented.

*Proof.*

- (a) Theorem A is injective on the `2^aleph_0` subgroups of Corollary C(b). `V_br` is countable, so it has at
  most `2^aleph_0` subgroups.
- (b) Strictness follows from Theorem A and Corollary C(a). Suppose `N_infinity = <<x_1, …, x_r>>`. Each `x_i`
  lies in some `N_{M_{k_i}}`. With `K := max k_i`, `N_infinity ≤ N_{M_K} < N_{M_{K+1}} ≤ N_infinity`, a
  contradiction.
- (c) `V_br` is finitely generated (indeed finitely presented, [Z, Introduction]). The first claim follows from
  (b) and Lemma N. For the second: `V_br` is countable, so it has countably many finite subsets, hence countably
  many normal subgroups that are normal closures of finite sets. By Lemma N, a finitely presented `V_br / N_M`
  forces `N_M` to be among them, and `M -> N_M` is injective. QED.

So the second question of Problem 2.10, "Is every quotient of braided V finitely presented?", has answer **no**.

## 6. Remarks

1. `F_br`: each `N_M ≤ P_br ≤ F_br` is normal in `V_br`, hence in `F_br`. `F_br` is finitely presented
   [Z, Introduction]. So `F_br` also has `2^aleph_0` normal subgroups inside `[P_br, P_br]` and fails max-n, and
   some quotient of `F_br` is not finitely presented. Whether `F_br` is Hopfian (the `F_br` half of Question 4.7)
   is not addressed here.
2. Consistency with `braided-v-max-n-above-lower-central-terms` (ACC above each `gamma_c(P_br)`): no `N_M`
   contains any `gamma_c(P_br)`.
   - Suppose `gamma_c(P_br) ≤ N_M`. Then `gamma_c(PB_3) ≤ psi_T(N_M ∩ PB_T) = M ≤ PB_3''`, so `PB_3 / PB_3''` would
     be nilpotent.
   - But `F` surjects onto the metabelian group `Z wr Z`, which is not nilpotent: `[x, t, …, t] = (t-1)^c x ≠ 0` in
     `Z[t^{±1}]`. So `F/F''` is not nilpotent.

   The chain of §5 mixes unboundedly many lower-central depths. This is exactly the escape route that the Attempts
   of `some-quotient-of-braided-v-is-not-finitely-presented` and `every-quotient-of-braided-v-is-finitely-presented`
   anticipated.
3. The case `M = 1` recovers Zaremsky's `Th(Lambda_*(3))`. The new ingredient is that a *nontrivial* normal
   subgroup of `B_3` can be prescribed at the 3-strand stage. Coherence at degenerate triples (D3) is what forces
   `G_n ≤ [PB_n, PB_n]`.
4. Still open, and not needed for the root:
   - Is `V_br / [P_br, P_br]` finitely presented?
   - Is `V_br / N_M` finitely presented for some specific `M`, for example `M = [PB_3, PB_3'']`?

## 7. Status and novelty (checked 2026-09-16)

- M. C. B. Zaremsky, *Some open problems*, version of July 12, 2026 (https://zaremsky.github.io/open_problems.pdf,
  fetched 2026-09-16). Section 2, Problem 10 reads "Is braided V Hopfian? Is every quotient of braided V finitely
  presented? (This would imply Hopfian.)" It carries no update note, so it is still listed as open.
- arXiv API queries on 2026-09-16, with the hits returned:
  - `all:"braided Thompson"` (40 newest): the newest hit is arXiv:2503.11594 (Ore categories, orderability). No
    hit concerns max-n or quotients.
  - `abs:"braided Thompson" AND abs:"normal subgroups"`: only arXiv:1403.8132.
  - `abs:"braided" AND abs:"Hopfian"`: only virtual, welded and surface braid papers.
  - `all:"braided V"` submitted 2024-01-01 to 2026-09-16: no hits.
  - `abs:"Thompson" AND abs:"max-n"`: no hits.
- Prior art inside [Z]: the m-loose subgroups give a descending chain, which is irrelevant to max-n. No ascending
  chain or uncountable family of normal subgroups of `V_br` was found there.

Novelty: NEW within these sources (referee rechecked the July 12, 2026 PDF and the arXiv API on 2026-09-16; no
change).
