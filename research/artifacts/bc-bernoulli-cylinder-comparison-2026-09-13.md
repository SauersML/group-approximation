# Bernoulli coefficients over a host: the host itself, plus one cylinder comparison in the support tail

Lane `ex-bc-measured-coefficient`, 2026-09-13. Supports `bernoulli-bc-splits-into-host-and-cylinder-comparison`
(proof route `-proof`) and the literature node `bernoulli-shift-weak-k-equivalence-and-going-down` (route `-citation`).

## 0. Setting

- `G` is a countable discrete group and `Z` a countable `G`-set with finite point stabilizers (for example `Z = G`).
- `Λ = {0, 1, ..., n}` with `n >= 1`, and `X = Λ^Z` with the shift action. The zero configuration `0` is fixed.
  For `x ∈ X`, `supp x = {z : x_z ≠ 0}`.
- For a prime `p` and `n = p - 1`, `X = (Z/p)^Z` is the Pontryagin dual of the permutation module `V = F_p[Z]`, and
  `C(X) ⋊_r G = C*_r(F_p wr_Z G)` (item 2 of `amenable-kernel-bc-transfer-and-ktop-half-exactness`).
- `S` is the `G`-set of pairs `s = (F, a)` with `F ⊆ Z` finite and nonempty and `a : F -> Λ \ {0}`. Its cylinder is
  `C_s = {x : x|_F = a}`, a compact open subset of `X \ {0}`. `S_k ⊆ S` is the set of pairs with `|F| = k`, and
  `S_(>=k)` those with `|F| >= k`. Stabilizers `G_s` are finite.
- `O_k = {x : |supp x| >= k}` is open and invariant, `I_k = C_0(O_k)`, so `I_1 = C_0(X \ {0})`. The stratum
  `O_k \ O_(k+1) = {x : |supp x| = k}` is closed in `O_k`, discrete (the cylinder `C_s` meets it in one point), and
  `G`-isomorphic to `S_k` by sending `s = (F, a)` to the configuration equal to `a` on `F` and `0` elsewhere.
- `c_0(S)` is the commutative `G`-algebra of the discrete `G`-set `S`.

## 1. Theorem

**(1) Host splitting.** `C(X) ≅ C ⊕ I_1` in `KK^G`, and in each degree
`mu_(G, C(X)) = mu_(G, C) ⊕ mu_(G, I_1)`. So `mu_(G, C(X))` is surjective (resp. injective) iff both summands are.
This part uses only the fixed point `0`. Every module dual `V^` has one, the trivial character.

**(2) Going-down, no hypothesis on `G`.** There is a weak K-equivalence `T ∈ KK^G(c_0(S), I_1)`: its restriction to
every finite subgroup `H` induces isomorphisms `K_*(c_0(S) ⋊ H) -> K_*(I_1 ⋊ H)`. Consequently `K^top_*(G; T)` is an
isomorphism, and `K^top_*(G; I_1) ≅ ⊕_([s] ∈ G\S) K_*(C*(G_s))`.

**(3) Reduction.** Put `T_r = K_*(T ⋊_r G) : K_*(c_0(S) ⋊_r G) -> K_*(I_1 ⋊_r G)`. Then `mu_(G, I_1)` is surjective
(resp. injective) iff `T_r` is surjective (resp. injective).

**(4) Cylinder form.** If `G` is torsion-free, `T` can be taken to be the class `Θ` of the equivariant *-homomorphism
`rho : c_0(S) -> K(l^2 S) ⊗ I_1`, `delta_s ↦ e_(ss) ⊗ 1_(C_s)`, followed by the stabilization isomorphism. Then
`K_0(c_0(S) ⋊_r G) = ⊕_([s]) Z`, `K_1 = 0`, and `T_r` sends the generator of `[s]` to `[1_(C_s)]`. So `mu_(G, I_1)` is
an isomorphism iff the cylinder classes `{[1_(C_s)] : [s] ∈ G\S}` form a `Z`-basis of `K_0(I_1 ⋊_r G)` and
`K_1(I_1 ⋊_r G) = 0`.

**(5) The comparison lives in the support tail.** For torsion-free `G` and every `k >= 1`, `T_r` is an isomorphism iff
its restriction `T_r^(k) : K_*(c_0(S_(>=k)) ⋊_r G) -> K_*(I_k ⋊_r G)` is. Modulo any finite support level the
comparison is always an isomorphism.

**(6) Group form.** Let `p` be prime, `n = p - 1`, `G` torsion-free. Reduced assembly for `F_p wr_Z G` (trivial
coefficients) is surjective (resp. injective) iff reduced assembly for `G` is and `T_r` is.

**(7) Trace detector.** For torsion-free `G`, the finite subgroups of `F_p wr_Z G` are elementary abelian `p`-groups,
so `Λ^(F_p wr_Z G) = Z[1/p]`. The Haar trace gives `τ[1_(C_s)] = p^(-|F|)`. A projection over `C*_r(F_p wr_Z G)` with
trace outside `Z[1/p]` refutes surjectivity for `F_p wr_Z G` (`lueck-surjective-assembly-traces-lie-in-lambda-g`),
hence, by (6), for `G` or for `T_r`.

## 2. Proofs

**Lemma E (quotients with equal crossed products give exact reduced sequences).** Let `0 -> I -> A -> B -> 0` be exact
`G`-algebras with `lambda_B : B ⋊_max G -> B ⋊_r G` injective. Then `0 -> I ⋊_r G -> A ⋊_r G -> B ⋊_r G -> 0` is exact.
*Proof.* Let `x ∈ A ⋊_r G` map to `0` in `B ⋊_r G`, and lift `x = lambda_A(y)`. Then
`lambda_B(q_max(y)) = q_r(x) = 0`, so `q_max(y) = 0`. The maximal crossed product is exact, so `y ∈ I ⋊_max G`. The
image of `I ⋊_max G` in `A ⋊_r G` is the closure of `C_c(G, I)`, which is `I ⋊_r G` because the reduced crossed
product preserves injectivity of `I -> A`. So `x ∈ I ⋊_r G`. QED.
It applies to `B = c_0(Y)` for a discrete `G`-set `Y` with finite stabilizers: by Green imprimitivity each orbit
contributes `K(l^2(G/G_y)) ⊗ C*(G_y)` to both crossed products.

**(1).** `ev_0 : C(X) -> C` is equivariant because `0` is fixed, the unit `ι : C -> C(X)` is equivariant, and
`ev_0 ∘ ι = id`. The split extension `0 -> I_1 -> C(X) -> C -> 0` gives `C(X) ≅ I_1 ⊕ C` in `KK^G`, with inclusion
`j` of `I_1`, retraction `r ∈ KK^G(C(X), I_1)`, `r ∘ j = 1`, `r ∘ ι = 0`. `K^top_*(G; -)` and `K_*(- ⋊_r G)` are
additive functors on `KK^G`, and assembly is natural for *-homomorphisms, so both sides and `mu` decompose. A direct
sum of two homomorphisms is surjective (injective) iff both are.

**(2).** Take `A = C(Λ) = C^(n+1)`, `A_0 = C`, `B = C(Λ \ {0})`, `ι` the unit and `φ : B -> A` extension by zero, as
in CEKN Corollary 2.11. On `K_0` the class `ι ⊕ φ : Z^(n+1) -> Z^(n+1)` is `(c, b_1, ..., b_n) ↦ (c, c+b_1, ..., c+b_n)`,
unipotent over `Z`; all algebras are finite-dimensional, so `ι ⊕ φ` is a KK-equivalence. CEKN Theorem 2.8 (first
sentence, no Baum--Connes hypothesis) gives a weak K-equivalence `Φ ∈ KK^G(J, C(X))` with
`J = ⊕_(F ∈ FIN(Z)) B^(⊗F) = C ⊕ c_0(S)` and with `∅`-component the unit `ι` (CEKN, proof of Theorem 2.8). Put
`T = r ∘ Φ ∘ incl`. For a finite `H <= G` write `K^H(D) = K_*(D ⋊ H)`. The isomorphism `K^H(Φ)`, in the
decompositions `K^H(J) = K^H(C) ⊕ K^H(c_0(S))` and `K^H(C(X)) = K^H(C) ⊕ K^H(I_1)`, has matrix
`[[id, c], [0, K^H(T)]]`: the `C -> C` entry is `K^H(ev_0 ∘ ι) = id` and the `C -> I_1` entry is `K^H(r ∘ ι) = 0`.
If `K^H(T) y = 0` then `(-c y, y) ↦ 0`, so `y = 0`; every `(0, z)` has a preimage, so `K^H(T)` is onto. Hence `T` is a
weak K-equivalence. Bönicke--Dell'Aiera Theorem 4.6 with Example 4.5 (a countable discrete group is an ample groupoid
whose compact open subgroupoids are the finite subgroups, and `KK^H(C, D) = K_*(D ⋊ H)`) gives that `K^top_*(G; T)`
is an isomorphism. `c_0(S)` is a proper `G`-algebra (central `C_0(S)`, `S` discrete with finite stabilizers), so
`mu_(G, c_0(S))` is an isomorphism by the generalized Green--Julg theorem recorded in the introduction of
Chabert--Echterhoff (2001), and Green imprimitivity gives `K_*(c_0(S) ⋊_r G) = ⊕_([s]) K_*(C*(G_s))`.

**(3).** Descent is functorial for Kasparov products (Kasparov 1988; context, not re-read; it is the naturality behind
CEKN Theorem 2.3). So `mu_(G, I_1) ∘ K^top_*(G; T) = T_r ∘ mu_(G, c_0(S))`. The two maps `K^top_*(G; T)` and
`mu_(G, c_0(S))` are bijective by (2), which proves (3) for each half.

**(4).** For torsion-free `G` the only finite subgroup is trivial, so a weak K-equivalence is a class inducing an
isomorphism on ordinary K-theory, and the proof of (3) used nothing else about `T`. The projections
`e_(ss) ⊗ 1_(C_s)` are pairwise orthogonal and `1_(C_s) ∈ I_1` since `C_s` is compact open and misses `0`, so `rho`
is an equivariant *-homomorphism for the action `Ad(lambda_S) ⊗ α`; composing with the equivariant Morita isomorphism
`K(l^2 S) ⊗ I_1 ~ I_1` (the permutation representation implements the first factor) gives `Θ`. On `K_0`,
`K_0(c_0(S)) = ⊕_S Z` and `K_0(I_1) = C_c(X \ {0}, Z)`, and `Θ` sends `delta_s ↦ 1_(C_s)`. These cylinder functions
form a `Z`-basis of `C_c(X \ {0}, Z)`: `Z^Λ` has basis `1, 1_(x_z = 1), ..., 1_(x_z = n)`, so the products
`1_(C_(F,a))` over all finite `F` (with `C_∅ = X`) form a basis of `C(X, Z)`, and `f(0) = 0` forces the coefficient of
`1_X` to vanish. Both `K_1` groups vanish (totally disconnected spaces). So `Θ` is a weak K-equivalence. Free orbits
give `c_0(Gs) ⋊_r G ≅ K(l^2 G)`, whose `K_0 = Z` is generated by `delta_s`, and `T_r[delta_s] = [1_(C_s)]`.

**(5).** `rho` maps `c_0(S_(>=k))` into `K ⊗ I_k`, because `C_s ⊆ O_(|F|)`. On the quotients
`c_0(S_(>=k))/c_0(S_(>=k+1)) = c_0(S_k)` and `I_k / I_(k+1) = C_0(O_k \ O_(k+1)) ≅ c_0(S_k)`, `rho` induces
`delta_s ↦ e_(ss) ⊗ delta_s`, a corner embedding, an isomorphism on `K_*(- ⋊_r G)`. So `rho` is a morphism of
extensions of `G`-algebras. Both quotients are `c_0` of discrete sets with finite stabilizers, so Lemma E makes both
reduced crossed-product sequences exact, with natural six-term sequences. The five lemma gives: `T_r^(k)` is an
isomorphism iff `T_r^(k+1)` is. Induction from `k = 1` proves (5).

**(6).** Item 2 of `amenable-kernel-bc-transfer-and-ktop-half-exactness` identifies reduced assembly for
`F_p wr_Z G = V ⋊ G` with `mu_(G, C(X))`, each half separately. Combine with (1) and (3).

**(7).** A finite subgroup maps to a finite, hence trivial, subgroup of `G`, so it lies in `V = ⊕_Z F_p`. The canonical
trace of `C*_r(V ⋊ G)` is Haar measure composed with the conditional expectation
(`module-dual-actions-have-no-wandering-open-sets`, item 2), so `τ(1_(C_(F,a))) = p^(-|F|)`.

## 3. What this does to the crux

- **(a) One comparison map.** Over a torsion-free host and the Bernoulli coefficient `F_p[Z]` with free `Z`, question
  (Q) of `monster-bc-failure-at-measured-coefficient-is-the-module-crux` splits exactly. Either the host fails
  trivial-coefficient Baum--Connes, whose status is recorded there as open for expander monsters, or `T_r` fails to
  be an isomorphism. The second alternative is a statement about the reduced K-theory of the single ideal
  `C_0((Z/p)^Z \ {0}) ⋊_r G`: its cylinder projections should be a free basis and its `K_1` should vanish.
- **(b) Tail.** By (5), a failure of `T_r` survives in `I_k ⋊_r G` for every `k`. It is carried by configurations of
  unbounded support. The expander markings of a monster (indicator configurations of the embedded graphs) are of this
  kind; the finite-support part of the Bernoulli shift, where the proper strata live, is always fine.
- **(c) Detectors.** The crux node calls invariant-measure traces dead. That holds for separating `ker q_*` from
  `im i_*` in a module triple. For (Q) itself at the Bernoulli coefficient, the Haar trace detects surjectivity
  failures through Lück's ring `Z[1/p]` (item (7)). What the trace cannot see is a failure of `T_r` with traces in
  `Z[1/p]`, for instance an integral relation `Σ n_s [1_(C_s)] = 0` with `Σ n_s p^(-|F_s|) = 0`.
- **(d) Survivor triples.** For `F_p[G] -> F_p[G/H]` with `H` infinite, the quotient coefficient `C((Z/p)^(G/H))` has
  infinite stabilizers `G_s`. Parts (2)--(3) should extend when `H` is amenable, using Chabert--Echterhoff Theorem 2.5
  and Baum--Connes for amenable groups. That extension is not written here.

## 4. Model tests

- `n = 0`: `X` is a point, `S = ∅`, `I_1 = 0`, and (1) returns `mu_(G, C(X)) = mu_G`.
- `G = Z = Z`, `p = 2`. As a `Z[Z]`-module `C(X, Z) = Z ⊕ ⊕_([s]) Z[Z]` (constants, then free orbits of cylinders).
  Pimsner--Voiculescu gives `K_0(C(X) ⋊ Z) = coker(1 - σ) = Z ⊕ ⊕_([s]) Z` and `K_1 = ker(1 - σ) = Z`. With
  `K_*(C*(Z)) = (Z, Z)` this leaves `K_0(I_1 ⋊ Z) = ⊕_([s]) Z` on the cylinder classes and `K_1(I_1 ⋊ Z) = 0`: `T_r` is
  an isomorphism, as Baum--Connes for the amenable group `F_2 wr Z` requires. The tail pieces are
  `K_0(I_k ⋊ Z) = ⊕_(|F| >= k) Z`.
- Exact hosts satisfying Baum--Connes with coefficients give `T_r` an isomorphism by (3), matching CEKN Theorem 2.8.

## 5. Scope and novelty

- (2) and (3) read CEKN Theorem 2.8 one coefficient at a time. CEKN state their K-theory formula under Baum--Connes
  with coefficients for `G`. The point here is what survives without it: at a Bernoulli coefficient, the reduced side
  splits into the host at trivial coefficients plus one comparison map, which is an isomorphism modulo every finite
  support level. Bounded check: CEKN Sections 1--2 read from the text extraction; not found stated there.
- Lemma E and (1) are elementary and very likely known.
- Groups with torsion: (1)--(3) hold as stated (the proof of (2) uses CEKN's `Φ`). The cylinder description (4) and the
  tail statement (5) are written only for torsion-free `G`.
