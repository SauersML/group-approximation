# Commensurators of strictly compressed subgroups of Kazhdan groups

2026-09-16, swarm attack on `left-orderable-group-with-rigid-compression-pair`.
This is a mathematical proof. It has not been formalized in Lean and was not checked
by a repository build.

The main result is an elementary obstruction for rigid compression pairs. A
compression of finite index is detected by the relative index of commensurable
subgroups, which is a homomorphism to `Q^x_{>0}`. Property (T) of the ambient
group kills every such homomorphism on finite-index subgroups. So in a rigid
pair the rigid subgroup is never commensurated, and some compressor has infinite
index. Section 4 records the finite-index descent of rigid pairs, which was
already proved inline elsewhere in the graph, and credits it there.

## 0. Conventions and elementary facts

All groups are discrete. `G` is a group and `Gamma <= G`. Cosets are left cosets.

- `P_Gamma = { g in G : g Gamma g^-1 <= Gamma }`, the compressors.
- `t` is a *strict compressor* when `t Gamma t^-1 <= Gamma` and `t Gamma t^-1 != Gamma`.
- `Gamma` is *infranormal* when `P_Gamma` generates `G` as a group.
- `Hom(H, Z)` is the set of group homomorphisms `H -> Z`.

**Lemma 0.1.**

1. `P_Gamma` is a monoid.
2. If `Gamma` is infranormal and not normal, a strict compressor exists.
3. If `t` is a strict compressor, then so is `t^k` for every `k >= 1`.
4. (Tower law) If `C <= B <= A`, then `[A:C] = [A:B][B:C]`. In particular
   `[A:C]` is finite exactly when both factors are finite.
5. For subgroups `A, B, C` of `G`, `[A cap B : A cap B cap C] <= [B : B cap C]`.

*Proof.*

1. `1 in P_Gamma`. If `g, h in P_Gamma`, then
   `gh Gamma h^-1 g^-1 <= g Gamma g^-1 <= Gamma`.
2. Otherwise every `g in P_Gamma` has `g Gamma g^-1 = Gamma`. Then
   `P_Gamma <= N_G(Gamma)`, so `G = <P_Gamma> <= N_G(Gamma)` and `Gamma` is normal.
3. For `i >= 0`,
   `t^(i+1) Gamma t^-(i+1) = t^i (t Gamma t^-1) t^-i <= t^i Gamma t^-i`.
   This gives the chain `Gamma >= t Gamma t^-1 >= ... >= t^k Gamma t^-k`, so
   `t^k in P_Gamma`. If `t^k Gamma t^-k = Gamma`, every inclusion in the chain is an
   equality, and in particular `t Gamma t^-1 = Gamma`, a contradiction.
4. This is standard: a transversal of `B` in `A` times a transversal of `C` in `B`
   is a transversal of `C` in `A`.
5. Define `x (A cap B cap C) |-> x (B cap C)` for `x in A cap B`.
   - It is well defined, because `x^-1 y in A cap B cap C` implies `x^-1 y in B cap C`.
   - It is injective, because `x, y in A cap B` and `x^-1 y in B cap C` give
     `x^-1 y in A cap B cap C`.  ∎

## 1. Relative index and the modular homomorphism

**Definition.** Subgroups `A, B` are *commensurable*, written `A ~ B`, when
`[A : A cap B]` and `[B : A cap B]` are finite. For `A ~ B` put

```text
rho(A, B) = [A : A cap B] / [B : A cap B]   in Q_{>0}.
```

**Lemma 1.1.**

- **(a)** Let `A ~ B` and `D <= A cap B` with `[A cap B : D]` finite. Then
  `rho(A,B) = [A:D] / [B:D]`, with both indices finite.
- **(b)** `~` is an equivalence relation. If `A ~ B ~ C`, then `D = A cap B cap C`
  has finite index in each of `A`, `B`, `C`, `A cap B`, `B cap C` and `A cap C`.
- **(c)** If `A ~ B ~ C`, then `rho(A, C) = rho(A, B) rho(B, C)`.
- **(d)** For `g in G`, `A ~ B` holds exactly when `gAg^-1 ~ gBg^-1` holds, and
  `rho(gAg^-1, gBg^-1) = rho(A, B)`.
- **(e)** `rho(A, A) = 1`.

*Proof.*

- **(a)** By the tower law, `[A:D] = [A : A cap B][A cap B : D]` and
  `[B:D] = [B : A cap B][A cap B : D]`. The common positive integer factor cancels.
- **(b)** Reflexivity and symmetry are clear. Let `A ~ B` and `B ~ C`.
  - By Lemma 0.1(5), `[A cap B : D] <= [B : B cap C]`, which is finite.
  - The same argument with the roles of `A` and `C` exchanged gives
    `[B cap C : D] <= [B : A cap B]`, also finite.
  - By the tower law, `[A:D] = [A : A cap B][A cap B : D]`,
    `[B:D] = [B : A cap B][A cap B : D]` and `[C:D] = [C : B cap C][B cap C : D]`
    are all finite.
  - Since `D <= A cap C <= A`, the tower law gives `[A : A cap C] <= [A:D]` and
    `[A cap C : D] <= [A:D]`. Likewise `[C : A cap C] <= [C:D]`.
  - All these indices are finite, so `A ~ C`.
- **(c)** Let `D = A cap B cap C`. By (b) it has finite index in `A cap B`, `B cap C`
  and `A cap C`. Apply (a) three times:
  - `rho(A,B) = [A:D]/[B:D]`;
  - `rho(B,C) = [B:D]/[C:D]`;
  - `rho(A,C) = [A:D]/[C:D]`.
- **(d)** Conjugation by `g` is an automorphism of `G`. It carries `A`, `B` and
  `A cap B` to `gAg^-1`, `gBg^-1` and `gAg^-1 cap gBg^-1`, and it preserves indices.
- **(e)** Both indices are 1.  ∎

**Lemma 1.2 (modular homomorphism).** The set
`Comm_G(Gamma) = { g in G : g Gamma g^-1 ~ Gamma }` is a subgroup of `G`, and

```text
Delta : Comm_G(Gamma) -> Q^x_{>0},     Delta(g) = rho(Gamma, g Gamma g^-1)
```

is a homomorphism.

*Proof.* `1 in Comm_G(Gamma)`. Let `g, h in Comm_G(Gamma)`.

- *Products.* Conjugating `h Gamma h^-1 ~ Gamma` by `g` gives
  `gh Gamma h^-1 g^-1 ~ g Gamma g^-1` by Lemma 1.1(d). Together with
  `g Gamma g^-1 ~ Gamma` and transitivity (Lemma 1.1(b)), `gh in Comm_G(Gamma)`.
- *Inverses.* Conjugating `g Gamma g^-1 ~ Gamma` by `g^-1` gives
  `Gamma ~ g^-1 Gamma g`, so `g^-1 in Comm_G(Gamma)`.
- *Homomorphism.* Put `A = Gamma`, `B = g Gamma g^-1` and `C = gh Gamma h^-1 g^-1`, so
  that `A ~ B ~ C`. By Lemma 1.1(c) and (d),

  ```text
  Delta(gh) = rho(A, C) = rho(A, B) rho(B, C)
            = Delta(g) rho(g Gamma g^-1, g (h Gamma h^-1) g^-1)
            = Delta(g) rho(Gamma, h Gamma h^-1) = Delta(g) Delta(h).  ∎
  ```

**Lemma 1.3.** Let `g in P_Gamma`.

- `g in Comm_G(Gamma)` exactly when `[Gamma : g Gamma g^-1]` is finite.
- In that case `Delta(g) = [Gamma : g Gamma g^-1]`.
- If moreover `g` is a strict compressor, then `Delta(g) >= 2`.

*Proof.* `Gamma cap g Gamma g^-1 = g Gamma g^-1`, so
`[g Gamma g^-1 : Gamma cap g Gamma g^-1] = 1` and
`[Gamma : Gamma cap g Gamma g^-1] = [Gamma : g Gamma g^-1]`. A strict compressor
has index different from 1.  ∎

## 2. The obstruction

**Proposition 2.1.** Let `t` be a strict compressor of `Gamma` in `G`.

- **(a)** If `[Gamma : t Gamma t^-1]` is finite, then `Comm_G(Gamma)` maps onto `Z`.
- **(b)** If `[G : Comm_G(Gamma)]` is finite, then `Comm_G(Gamma)` maps onto `Z`.

*Proof.*

- **(a)**
  - By Lemma 1.3, `t in Comm_G(Gamma)` and `m = Delta(t) = [Gamma : t Gamma t^-1] >= 2`.
    Choose a prime `p` dividing `m`.
  - The `p`-adic valuation `v_p : Q^x_{>0} -> Z`, with `v_p(p^k a / b) = k` for
    integers `a, b` prime to `p`, is a homomorphism.
  - So `psi = v_p o Delta : Comm_G(Gamma) -> Z` is a homomorphism with
    `psi(t) = v_p(m) >= 1`.
  - Its image is a nonzero subgroup `dZ` with `d >= 1`, and `psi / d` is onto `Z`.
- **(b)**
  - Let `n = [G : Comm_G(Gamma)]`. Left multiplication by `t` permutes the finite set
    `G / Comm_G(Gamma)`.
  - Among the `n + 1` cosets `t^i Comm_G(Gamma)`, `0 <= i <= n`, two coincide:
    `t^i Comm_G(Gamma) = t^j Comm_G(Gamma)` with `0 <= i < j <= n`.
  - So `e = j - i >= 1` satisfies `t^e in Comm_G(Gamma)`.
  - By Lemma 0.1(3), `t^e` is a strict compressor. It lies in
    `P_Gamma cap Comm_G(Gamma)`, so `[Gamma : t^e Gamma t^-e]` is finite by Lemma 1.3.
  - Apply (a) to `t^e`.  ∎

**Theorem 2.2.** Let `Gamma <= G`.

- **(a)** Suppose `Gamma` is infranormal and not normal in `G`, and `Hom(G, Z) = 0`.
  - Some `g in P_Gamma` has `[Gamma : g Gamma g^-1]` infinite.
  - Hence `Comm_G(Gamma) != G`.
  - The compressors of infinite index generate `G`.
- **(b)** Suppose `Gamma` has a strict compressor in `G`, and `Hom(H, Z) = 0` for
  every subgroup `H` of finite index in `G`. Then `[G : Comm_G(Gamma)]` is infinite.
- **(c)** If `G` has property (T), the hypotheses on `G` in (a) and (b) hold.

In particular, in a rigid compression pair (`Gamma`, `G` Kazhdan, `Gamma` infranormal
and not normal) three things hold:

- the commensurator of `Gamma` has infinite index in `G`;
- some compressor has infinite index in `Gamma`;
- the compressors of infinite index generate `G`.

*Proof of (a).*

- By Lemma 0.1(2) there is a strict compressor `t`.
- Suppose every `g in P_Gamma` has finite index `[Gamma : g Gamma g^-1]`.
  - Then `P_Gamma <= Comm_G(Gamma)` by Lemma 1.3.
  - `Comm_G(Gamma)` is a subgroup containing a generating set of `G`, so it equals `G`.
  - Proposition 2.1(a), applied to `t`, gives a surjection `G -> Z`. This contradicts
    `Hom(G, Z) = 0`.
- By Lemma 1.3, a compressor `g` of infinite index is not in `Comm_G(Gamma)`, so
  `Comm_G(Gamma) != G`.
- *Generation.* Let `S = P_Gamma \ Comm_G(Gamma)`. It is nonempty, so fix `p in S`.
  - Let `q in P_Gamma cap Comm_G(Gamma)`. Then `pq in P_Gamma` by Lemma 0.1(1).
  - `pq` is not in `Comm_G(Gamma)`: otherwise `p = (pq) q^-1` would be.
  - So `pq in S`, and `q = p^-1 (pq) in <S>`.
  - Hence `P_Gamma <= <S>`, and `G = <P_Gamma> = <S>`.
  - By Lemma 1.3, `S` is exactly the set of compressors of infinite index.

*Proof of (b).* If `[G : Comm_G(Gamma)]` were finite, Proposition 2.1(b) would give
a surjection onto `Z` from the finite-index subgroup `Comm_G(Gamma)`.

*Proof of (c).* The inputs are three statements from B. Bekka, P. de la Harpe and
A. Valette, *Kazhdan's Property (T)*, preprint version dated February 23, 2007
(cited below as BHV). They are transcribed from the text:

- Introduction, definition: "a topological group G has Property (T) if there exist a
  compact subset Q and a real number ε > 0 such that, whenever π is a continuous
  unitary representation of G on a Hilbert space H for which there exists a vector
  ξ ∈ H of norm 1 with sup_{q∈Q} ‖π(q)ξ − ξ‖ < ε, then there exists an invariant
  vector, namely a vector η ≠ 0 in H such that π(g)η = η for all g ∈ G."
- Theorem 1.7.1: "Let G be a locally compact group, and let H be a closed subgroup of
  G such that G/H has a finite invariant regular Borel measure. The following are
  equivalent: (i) G has Property (T); (ii) H has Property (T)."
- Corollary 1.3.6: "Let G be a locally compact group with Property (T). Then: (i) the
  Hausdorff abelianized group G/[G, G] is compact; (ii) G is unimodular. In
  particular, if Γ is a discrete group with Property (T), then its abelianization
  Γ/[Γ, Γ] is finite."

Now the proof.

- Let `H <= G` with `[G:H]` finite.
  - `H` is closed in the discrete group `G`.
  - Counting measure on the finite set `G/H` is a finite `G`-invariant regular Borel
    measure.
  - So `H` has property (T) by BHV Theorem 1.7.1.
- By BHV Corollary 1.3.6, `H/[H,H]` is finite.
- A homomorphism `H -> Z` factors through `H/[H,H]`. So its image is a finite subgroup
  of `Z`, hence 0.
- Taking `H = G` gives `Hom(G, Z) = 0`.  ∎

BHV state this combination themselves as Corollary 1.7.2: "Let Γ be a discrete group with
Property (T), and let Λ be a subgroup of Γ of finite index. Then the abelianization
Λ/[Λ, Λ] of Λ is finite." (Checked by the referee against the text of the preprint on
2026-09-16.)

**Remark 2.3 (a direct check of `Hom(G,Z) = 0`).** Corollary 1.3.6 can be replaced by
the definition. Suppose `G` has (T) with Kazhdan pair `(Q, eps)`, where `Q` is finite
because `G` is discrete, and suppose `psi : G -> Z` is onto.

- Let `G` act on `l^2(Z)` by `(pi(s) f)(n) = f(n - psi(s))`.
- *No invariant vector.* An invariant `eta` satisfies `eta(n - 1) = eta(n)` for all `n`,
  because `psi` is onto. So `eta` is constant, and a constant `l^2` function is 0.
- *Almost invariant vectors.* Put `f_k = k^(-1/2) 1_{0,...,k-1}`, a unit vector.
  - `pi(s) f_k - f_k` is `k^(-1/2)` times the signed indicator of the symmetric
    difference of `{0,...,k-1}` and its translate by `psi(s)`.
  - So `‖pi(s) f_k - f_k‖^2 = 2 min(|psi(s)|, k) / k <= 2 |psi(s)| / k`.
  - For `k > 2 max_{q in Q} |psi(q)| / eps^2`, the vector `f_k` is `(Q, eps)`-invariant.
- This contradicts (T).

**Remark 2.4 (the hypotheses are needed).**

- **Property (T) must be assumed of `G`, not only of `Gamma`.**
  - Let `G = (SL_3(Z) x Z) x| Z[1/2]^3`, with multiplication
    `(A, k, v)(B, l, w) = (AB, k + l, v + 2^k A w)`.
  - Let `Gamma = { (A, 0, v) : v in Z^3 }`, which is `SL_3(Z) x| Z^3`. It has (T):
    BHV Example 1.7.4(i) reads "SLn(Z) and SLn(Z) n Zn have Property (T) for n ≥ 3".
  - Put `t = (I, 1, 0)`. Then `t (A, 0, v) t^-1 = (A, 0, 2v)`. So
    `t Gamma t^-1 = SL_3(Z) x| 2Z^3`, of index 8, and `t^-1 Gamma t` is not contained
    in `Gamma`. So `Gamma` is not normal.
  - `t^-k (I, 0, w) t^k = (I, 0, 2^-k w)`. So `<Gamma, t>` contains `Z[1/2]^3`,
    `SL_3(Z)` and `t`, hence equals `G`. Thus `Gamma` is infranormal.
  - `Gamma` and `t` lie in `Comm_G(Gamma)`, so `Comm_G(Gamma) = G`, and by Lemma 1.3
    every compressor has finite index.
  - The conclusions of (a) and (b) both fail. The hypothesis that fails is
    `Hom(G, Z) = 0`: the map `(A, k, v) |-> k` is onto `Z`.
- **Infranormality is needed in (a).**
  - Let `G = SL_3(Z[1/2]) x| Z[1/2]^3`, with `(A, v)(B, w) = (AB, v + Aw)`, and let
    `Gamma = { (I, n e_1) : n in Z }`.
  - BHV Remark 2.8.4 reads: "SL3(Z[1/p])n(Z[1/p])3 has Property (FH) since it is a
    lattice in the Kazhdan group (SL3(R) n R3) × (SL3(Qp) n Q3p)".
  - BHV's introduction reads: "a σ-compact locally compact group has Property (T) if
    and only if it has Property (FH)". A countable discrete group is σ-compact, so `G`
    has (T).
  - Here `(A, v)(I, w)(A, v)^-1 = (I, Aw)`. So `P_Gamma = { (A, v) : A e_1 in Z e_1 }`.
  - `t = (diag(2, 1/2, 1), 0)` is a strict compressor of index 2.
  - Every compressor has finite index `|lambda|`, where `A e_1 = lambda e_1` and
    `lambda` is a nonzero integer.
  - The conclusion of (a) fails. The hypothesis that fails is infranormality: `P_Gamma`
    lies in the proper subgroup `{ (A, v) : A e_1 in Q e_1 }`.
  - (b) is consistent. `Comm_G(Gamma) = { (A, v) : A e_1 in Q e_1 }` has infinite
    index, since the orbit of the line `Q e_1` under `SL_3(Z[1/2])` is infinite. For
    instance, the elementary matrices `I + n E_21` send it to the distinct lines
    `Q(e_1 + n e_2)`.
- The one-dimensional model of the first example is `BS(1,2) = Z x| Z[1/2]` with
  `Gamma = Z`, where `Delta` is the map onto `2^Z`.

## 3. Consequences for `left-orderable-group-with-rigid-compression-pair`

Let `Gamma <= G` witness the target: `G` left-orderable, both Kazhdan, `Gamma`
infranormal and not normal. By Theorem 2.2:

1. Some `g in G` has `g Gamma g^-1 < Gamma` of infinite index. Conjugation by `g` is an
   isomorphism `Gamma -> g Gamma g^-1`. So `Gamma` is an infinite left-orderable
   Kazhdan group isomorphic to a subgroup of itself of infinite index.
2. `[G : Comm_G(Gamma)]` is infinite. So no witness is a commensurated pair. This rules
   out Hecke-pair constructions in which the host virtually commensurates the rigid
   subgroup, for example a lattice sitting inside a Kazhdan group of its commensurator
   elements. For such pairs the relative index is an honest homomorphism on a
   finite-index subgroup, and (T) forces it to be trivial.
3. The compressors of infinite index generate `G`.

None of these conditions involves the order, so none of them obstructs the target. They
constrain how any construction has to look. The rigid subgroup must be compressed
"infinitely", as in the Theorem E pair, where substitutions of monomials shrink the
coordinate ring. It cannot be compressed through a scaling of finite index, as in the
affine example of Remark 2.4.

## 4. Descent to finite index (credited; not new)

**Lemma 4.1.** Let `Gamma <= G` be infranormal and not normal, let `N` be a normal
subgroup of finite index in `G`, and put `Gamma_N = Gamma cap N`. Then:

- `Gamma_N` is infranormal and not normal in `N`;
- if `Gamma` and `G` have (T), so do `Gamma_N` and `N`;
- if `G` is left-orderable, so is `N`.

*Proof.* The combinatorial part is step 2 of
`rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group-proof` (Lemma, "Infranormality",
"Non-normality"), with `E = G` and `G_k = N`. Here is the outline.

- *Generation.* `P_Gamma cap N` generates `N`, by the exponent argument given there.
- *Infranormality.* For `g in P_Gamma cap N`, `g Gamma_N g^-1 <= Gamma cap N = Gamma_N`.
- *Non-normality.*
  - Let `u` be a strict compressor and `j` a multiple of the exponent of `G/N` with
    `2^j > [G:N]`. Then `u^j in N`.
  - `u^j Gamma_N u^-j <= u^j Gamma u^-j`, which has index at least `2^j` in `Gamma`,
    while `[Gamma : Gamma_N] <= [G : N]`.
  - So `u^j Gamma_N u^-j != Gamma_N`.
- *Property (T).* It passes to `N` and `Gamma_N` by BHV Theorem 1.7.1.
- *Left-orderability.* It passes to subgroups.  ∎

**Corollary 4.2.** The target holds exactly when some rigid compression pair
`Gamma <= G` has a host `G` with a left-orderable subgroup `H` of finite index.

*Proof.* One direction is `H = G`. For the other:

- The normal core `N = intersection_g g H g^-1` is the kernel of the action on the
  finite set `G/H`. So it has finite index.
- `N` is left-orderable as a subgroup of `H`.
- Lemma 4.1 gives the witness `Gamma cap N <= N`.  ∎

This only reformulates the target, so it is not recorded as a node. Its use is
diagnostic. The known rigid pairs with torsion are not merely non-orderable: their hosts
have no torsion-free subgroup of finite index. The notes file gives the sketch.

## 5. Literature and novelty audit

- **BHV**, the preprint text dated February 23, 2007, was read locally. Every quoted
  statement above was transcribed from that text: the definition, Theorem 1.7.1,
  Corollary 1.3.6, Example 1.7.4(i), Remark 2.8.4 and the Delorme--Guichardet sentence
  of the introduction. Numbering is that of the preprint. In the extracted text the
  semidirect-product sign renders as the letter `n`, so "SLn(Z) n Zn" means
  `SL_n(Z) x| Z^n`; the quotes keep that rendering.
- **arXiv API searches on 2026-09-16:**
  - `abs:"Hecke pair" AND abs:"property (T)"` returned 1405.1540v2 and 1509.06654v2,
    about C*-completions and planar algebras;
  - `abs:commensurated AND abs:unimodular AND abs:"property (T)"` returned nothing;
  - `abs:commensurated AND abs:Kazhdan` returned 2507.16677v3, 1811.12226v3,
    1803.08572v2, 1311.0538v2 and math/0306259v1;
  - `abs:infranormal` returned nothing.
  - No returned abstract states the compression consequence.
- **Novelty.** `Delta` is the modular function of the pair `(Comm_G(Gamma), Gamma)`
  restricted to the discrete group. In the language of Schlichting completions, which
  was not re-read here, Theorem 2.2(b) with `Comm_G(Gamma) = G` would follow from
  unimodularity of Kazhdan locally compact groups (BHV Corollary 1.3.6(ii)). So the
  statement is plausibly folklore. No primary source stating it for compressions was
  located. The proof above is self-contained and does not use completions.
- **Certificate boundary.**
  - Only discrete groups are treated.
  - The results constrain rigid compression pairs in every host. They say nothing about
    left-orderability and do not bear on Navas's Question 3 itself.
