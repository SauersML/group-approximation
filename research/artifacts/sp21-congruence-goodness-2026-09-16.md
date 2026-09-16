# A finite congruence kernel forces profinite cohomology above the virtual cohomological dimension (Sp(2,1) lattices)

Artifact for `sp21-finite-congruence-kernel-forbids-p-goodness` and its proof route
`sp21-finite-congruence-kernel-forbids-p-goodness-proof`. Written 2026-09-16 by a swarm
agent working on `sp21-lattice-has-congruence-subgroup-property`.

**No novelty is claimed.** This is the Sp(2,1) instance of a folklore mechanism. For
`SL_n(Z)`, `n >= 3`, the congruence subgroup property and Lazard's theorem are the usual
reason given for `SL_n(Z)` not being good. We recall that remark from Grunewald,
Jaikin-Zapirain and Zalesskii, *Cohomological goodness and the profinite completion of
Bianchi groups*, Duke Math. J. 144 (2008), no. 1, 53–72, DOI 10.1215/00127094-2008-031.
The referee confirmed these bibliographic data on Crossref and Project Euclid on 2026-09-16.
The abstract does not mention `SL_n(Z)` and the body was **not read**, so the attribution
of the remark is unverified. The repository already uses the same mechanism for `SL_3(Z)` in
`research/artifacts/review-swarm4-2026-09-12.md` §41.3. What is new here is only the
bookkeeping for cocompact arithmetic `Sp(2,1)` lattices: the full profinite kernel, the
trivial-coefficient form, and the pro-p form that matches
`sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`.

## 0. Setting and notation

- `k` is a number field with ring of integers `O`.
- `G` is a simply connected, absolutely almost simple `k`-group with a fixed faithful
  `k`-embedding `G <= GL_m`. We set `G(O) = G(k) ∩ GL_m(O)` and
  `G(O_𝔭) = G(k_𝔭) ∩ GL_m(O_𝔭)`.
- `G(k_{v_0}) ≅ Sp(2,1)` at one archimedean place `v_0`. `G(k_v)` is compact at the other
  archimedean places, and `G` is `k`-anisotropic. This is the setting of
  `sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel` with `n = 2`.
- `Γ <= G(O)` is torsion-free of finite index.
- `Γ^` is the profinite completion of `Γ`.
- `G(O^) = ∏_𝔭 G(O_𝔭)` runs over the finite places. `Γ̄` is the closure of `Γ` in
  `G(O^)`.
- `π : Γ^ ->> Γ̄` is the natural map, and `C = ker π` is the congruence kernel.
- `D = 21·[k:Q]`, where `21 = dim Sp_6 = dim G`.
- `p` is a prime and `P = {𝔭 : 𝔭 | p}`. Write `G_p = ∏_{𝔭 ∈ P} G(O_𝔭)`.
- For a finite-index `Δ <= Γ(p) = Γ ∩ G(O, pO)`:
  - `Δ^_p` is the pro-p completion of `Δ`;
  - `Δ̄_p` is the closure of `Δ` in `G_p`;
  - `π_Δ : Δ^_p ->> Δ̄_p` is the natural map, and `N_Δ = ker π_Δ`.
- A group `H` is **good** (Serre) if inflation `H^q(H^;M) -> H^q(H;M)` is an isomorphism
  for every finite `H`-module `M` and every `q`. It is **p-good** if this holds for every
  finite `M` of p-power order.

## 1. Imported inputs

All of these are standard. Theorem and proposition numbers are quoted from memory and were
**not re-verified against the sources in this session**. Each input is used only in the
form stated here.

- **(I1) Cartan.** The symmetric space `X = Sp(2,1)/(Sp(2)×Sp(1))` is a Riemannian
  symmetric space of noncompact type, and it is diffeomorphic to `R^8`. Here
  `8 = 21 - (10 + 3)`, and `X` is the quaternionic hyperbolic plane.
- **(I2) Strong approximation.** Let `G` be simply connected and absolutely almost simple
  over `k`, and let `S` be the set of archimedean places. If `∏_{v ∈ S} G(k_v)` is
  noncompact, then `G(k)` is dense in `G(A_f)`. Source: Platonov–Rapinchuk, *Algebraic
  Groups and Number Theory*, Theorem 7.12.
- **(I3) Open uniform subgroups.** Every compact p-adic analytic group has an open
  uniform pro-p subgroup. A uniform pro-p group is torsion-free, and its dimension equals
  the dimension of the analytic group it is open in. Sources: Lazard, *Groupes analytiques
  p-adiques*, Publ. IHES 26 (1965); Dixon–du Sautoy–Mann–Segal, *Analytic pro-p groups*,
  2nd ed., Corollary 8.34 and Theorem 4.5.
- **(I4) Lazard's cohomological dimension.** A torsion-free compact p-adic analytic group of
  dimension `d` has `cd_p = d`. Sources: Lazard, loc. cit.; J.-P. Serre, *Sur la dimension
  cohomologique des groupes profinis*, Topology 3 (1965), 413–420.
- **(I5) Subgroups.** For a closed subgroup `H` of a profinite group `G`,
  `cd_p(H) <= cd_p(G)`. Source: Serre, *Galois Cohomology*, Chapter I, §3.3,
  Proposition 14.
- **(I6) Simple-module test.** For a profinite `G`, `cd_p(G) <= n` iff
  `H^{n+1}(G;A) = 0` for every discrete simple `G`-module `A` with `pA = 0`. For a pro-p
  group `G`, `cd_p(G) <= n` iff `H^{n+1}(G;Z/p) = 0`. Source: Serre, *Galois
  Cohomology*, I §3.1, Proposition 11, and I §4.1, Proposition 21.
- **(I7) Closed subgroups as limits.** If `H` is a closed subgroup of a profinite group
  `G` and `A` is a discrete `G`-module, then restriction induces an isomorphism
  `lim→_{V ⊇ H, V open} H^q(V;A) -> H^q(H;A)`. Source: Serre, *Galois Cohomology*,
  I §2.2, Proposition 8.

## 2. Lemmas

**Lemma 1 (discrete side).** Let `Γ_1 <= Γ` have finite index. Then `H^q(Γ_1;A) = 0` for
every `Γ_1`-module `A` and every `q >= 9`.

*Proof.*
1. `Γ` is discrete in `G_∞ = ∏_{v | ∞} G(k_v)`, because `O` is discrete in
   `O ⊗ R`.
2. The projection `G_∞ -> G(k_{v_0})` has compact kernel, so it is proper. Hence
   `Γ_1 -> Sp(2,1)` has finite kernel and discrete image. The kernel is trivial because
   `Γ` is torsion-free.
3. `Γ_1` acts properly discontinuously on `X`. Point stabilizers are discrete subgroups
   of compact groups, hence finite, hence trivial. So the action is free.
4. `Γ_1\X` is a Hausdorff 8-manifold, and it is compact because `Γ`, and so `Γ_1`, is
   cocompact. That is the standing hypothesis of the target claim; it also follows from
   `k`-anisotropy by Godement's criterion.
5. By (I1), `X` is contractible. So `M_1 = Γ_1\X` is a closed aspherical smooth
   8-manifold with `π_1 = Γ_1`.
6. A closed smooth 8-manifold has a finite CW structure of dimension 8, from a smooth
   triangulation. Hence `H^q(Γ_1;A) = H^q(M_1; A) = 0` for `q > 8`, where `A` is the
   corresponding local system. ∎

**Lemma 2 (congruence completion is open).** For finite-index `Γ_1 <= Γ`, the closure
`Γ̄_1` of `Γ_1` in `G(O^)` is an open subgroup. Also, for every prime `p` and every
finite-index `Δ <= Γ`, the closure `Δ̄_p` of `Δ` in `G_p` is open.

*Proof.*
1. `G_∞ ⊇ G(k_{v_0}) ≅ Sp(2,1)` is noncompact. By (I2), `G(k)` is dense in `G(A_f)`.
2. `G(O^)` is open in `G(A_f)` and `G(k) ∩ G(O^) = G(O)`. Hence `G(O)` is dense in
   `G(O^)`: every nonempty open subset of `G(O^)` is open in `G(A_f)` and meets `G(k)`
   inside `G(O^)`.
3. Write `G(O) = ⋃_{i=1}^r g_i Γ_1`, which is possible since `Γ_1` has finite index in
   `G(O)`. Taking closures gives `G(O^) = ⋃ g_i Γ̄_1`. So the closed subgroup `Γ̄_1` has
   finite index, and it is open.
4. By step 3 applied to `Δ`, the closure `Δ̄` of `Δ` in `G(O^)` is open. The projection
   `G(O^) -> G_p` is an open map, so the image of `Δ̄` is open in `G_p`. That image is
   compact, hence closed. It contains `Δ` and, by continuity, lies in the closure of `Δ`.
   So it equals `Δ̄_p`, which is therefore open. ∎

**Lemma 3 (splitting off a finite kernel).** Let `φ : A ->> B` be a continuous surjection
of profinite groups with finite kernel `K`. Then there is an open normal `M <= A` with
`M ∩ K = 1`. For such `M`:
- `φ|_M : M -> φ(M)` is an isomorphism of topological groups;
- `φ(M)` is open in `B`.

*Proof.*
1. Open normal subgroups of `A` form a base at `1` with trivial intersection. For each of
   the finitely many `c ∈ K \ {1}`, choose an open normal `M_c` with `c ∉ M_c`. Set
   `M = ⋂_c M_c`, which is open normal with `M ∩ K = 1`.
2. `φ|_M` is a continuous bijection from a compact space onto a Hausdorff space. So it is
   a homeomorphism.
3. `φ(M)` is compact, hence closed. It has finite index in `B = φ(A)`, because
   `[A:M] < ∞`. So it is open. ∎

**Lemma 4 (a D-dimensional p-adic analytic subgroup in every open subgroup).** Let
`W <= G(O^)` be an open subgroup and `p` a prime. Then `W` contains a closed subgroup `U`
such that:
- `U` is uniform pro-p;
- `U` is open in a closed subgroup `L ≅ ∏_{𝔭 ∈ P} W'_𝔭`, where each `W'_𝔭` is an open
  subgroup of `G(O_𝔭)`;
- `cd_p(U) = D`.

The same holds for an open subgroup `W <= G_p`, and there `L = W` may be taken.

*Proof.*
1. `G(O^)` carries the product topology. So `W` contains a basic open neighbourhood of
   `1` of the form `B = ∏_{𝔭 ∈ S} W_𝔭 × ∏_{𝔭 ∉ S} G(O_𝔭)`, with `S` finite and each
   `W_𝔭` an open neighbourhood of `1` in `G(O_𝔭)`.
2. Each `G(O_𝔭)` is profinite, so each `W_𝔭` may be shrunk to an open subgroup. Then `B`
   is a subgroup.
3. Put `W'_𝔭 = W_𝔭` for `𝔭 ∈ P ∩ S`, and `W'_𝔭 = G(O_𝔭)` for `𝔭 ∈ P \ S`.
4. Let `L` be the set of `x ∈ G(O^)` with `x_𝔭 ∈ W'_𝔭` for `𝔭 ∈ P` and `x_𝔭 = 1` for
   `𝔭 ∉ P`. It is a closed subgroup, `L ⊆ B ⊆ W`, and `L ≅ ∏_{𝔭 ∈ P} W'_𝔭` as
   topological groups.
5. `G(k_𝔭)` is a `k_𝔭`-analytic group of dimension `dim G = 21`. As a `Q_p`-analytic group
   its dimension is `21·[k_𝔭:Q_p]`. So `L` is a compact p-adic analytic group of dimension
   `Σ_{𝔭 ∈ P} 21·[k_𝔭:Q_p] = 21·[k:Q] = D`.
6. By (I3), `L` has an open uniform subgroup `U`, which is torsion-free of dimension `D`.
   By (I4), `cd_p(U) = D`.
7. For `W <= G_p` open, `W` is itself a compact p-adic analytic group of dimension `D`.
   Apply (I3) and (I4) directly. ∎

## 3. The theorems

**Step 0 (profinite completions of finite-index subgroups).** Let `Γ_1 <= Γ` have finite
index and let `V_1` be the closure of `Γ_1` in `Γ^`. Then:
- `V_1` is open, and `V_1 ∩ Γ = Γ_1`;
- the inclusion induces `Γ_1^ ≅ V_1`;
- `π(V_1) = Γ̄_1`;
- `ker(π|_{V_1}) = C ∩ V_1`, which is finite if `C` is finite.

Conversely, every open `V <= Γ^` is the closure of the finite-index subgroup `V ∩ Γ`.

*Proof.*
1. Every finite-index subgroup of `Γ_1` has finite index in `Γ` and contains its normal
   core in `Γ`. So the normal finite-index subgroups `N` of `Γ` with `N <= Γ_1` are
   cofinal among the finite-index subgroups of `Γ_1`. Hence
   `V_1 = lim← Γ_1/N ≅ Γ_1^`.
2. `V_1` is open, because it is the preimage of `Γ_1 N/N` for one such `N`. It meets `Γ`
   in `Γ_1 N = Γ_1`.
3. `π(V_1)` is compact and contains `Γ_1` as a dense subset. So `π(V_1) = Γ̄_1`.
4. The kernel statement is immediate.
5. For open `V`, `Γ` is dense in `Γ^`. Hence `V ∩ Γ` is dense in `V`, and it has index
   `[Γ^:V]` in `Γ`. ∎

**Theorem 1 (full congruence kernel).** Assume `C` is finite. Then for every prime `p` and
every finite-index `Γ_1 <= Γ`:
- (a) `cd_p(Γ_1^) >= D >= 21`;
- (b) there is a finite simple discrete `Γ_1^`-module `A` with `pA = 0` and
  `H^9(Γ_1^;A) != 0`, while `H^9(Γ_1;A) = 0`.

So inflation `H^9(Γ_1^;A) -> H^9(Γ_1;A)` is not injective, and `Γ_1` is neither good nor
p-good.

*Proof.*
1. By Step 0, `π|_{V_1} : Γ_1^ ≅ V_1 ->> Γ̄_1` is a continuous surjection with finite
   kernel. By Lemma 2, `Γ̄_1` is open in `G(O^)`.
2. By Lemma 3 there is an open normal `M <= Γ_1^` such that:
   - `π|_M` is a topological isomorphism onto `π(M)`;
   - `π(M)` is open in `Γ̄_1`, hence open in `G(O^)`.
3. Apply Lemma 4 to `W = π(M)`. This gives a uniform closed subgroup `U <= π(M)` with
   `cd_p(U) = D`.
4. `U' = (π|_M)^{-1}(U)` is closed in `M`, since `π|_M` is a homeomorphism. It is closed
   in `Γ_1^`, since `M` is open and so closed, and `U' ≅ U`.
5. By (I5), `cd_p(Γ_1^) >= cd_p(U') = D`. This is (a).
6. `D >= 21 > 8`, so `cd_p(Γ_1^) <= 8` fails. By (I6) with `n = 8`, there is a discrete
   simple `Γ_1^`-module `A` with `pA = 0` and `H^9(Γ_1^;A) != 0`.
7. `A` is finite. Take `0 != a ∈ A`. Its stabilizer is open, so the orbit of `a` is
   finite. The `F_p`-span of the orbit is then a nonzero finite submodule, which equals `A`
   by simplicity.
8. Through `Γ_1 -> Γ_1^`, `A` is a finite `Γ_1`-module of p-power order. Lemma 1 gives
   `H^9(Γ_1;A) = 0`. ∎

**Theorem 2 (trivial coefficients).** Assume `C` is finite, and let `p` be a prime. Then
there is a finite-index `Γ_1 <= Γ` with

```text
H^9(Γ_1^; F_p) != 0   and   H^9(Γ_1; F_p) = 0     (F_p trivial).
```

More precisely, `Γ^` contains a closed uniform subgroup `U'` with `cd_p(U') = D`, and there
is a class `β ∈ H^9(Γ_1^;F_p)` whose restriction to `U'` is nonzero. Therefore `β`
restricts nontrivially to `Γ_2^` for every finite-index `Γ_2 <= Γ_1` whose closure in
`Γ^` contains `U'`.

*Proof.*
1. Steps 1–4 of Theorem 1 with `Γ_1 = Γ` give a closed subgroup `U' <= Γ^` isomorphic to
   a uniform group of dimension `D`, with `cd_p(U') = D`.
2. `U'` is pro-p, and `D > 8`. By the pro-p form of (I6), `H^9(U';F_p) != 0`.
3. By (I7) applied to the trivial discrete `Γ^`-module `F_p`,
   `H^9(U';F_p) = lim→_{V ⊇ U' open} H^9(V;F_p)`. Hence there are an open `V ⊇ U'` and a
   class `β ∈ H^9(V;F_p)` with `res_{U'} β != 0`.
4. Put `Γ_1 = V ∩ Γ`. By Step 0, `Γ_1` has finite index and `V ≅ Γ_1^`.
5. Lemma 1 gives `H^9(Γ_1;F_p) = 0`.
6. The last assertion holds because restriction to `U'` factors through every open
   `V' <= V` containing `U'`. ∎

**Theorem 3 (pro-p form).** Let `p` be a prime and `Δ <= Γ(p)` of finite index. If
`N_Δ = ker(π_Δ : Δ^_p ->> Δ̄_p)` is finite, then

```text
cd_p(Δ^_p) >= D,   H^9(Δ^_p; F_p) != 0,   H^9(Δ; F_p) = 0.
```

So inflation from the pro-p completion is not injective in degree 9.

*Proof.*
1. **The map `π_Δ` exists.** The kernel `GL_m(O_𝔭, 𝔭)` of `GL_m(O_𝔭) -> GL_m(O/𝔭)` is
   pro-p. Its successive congruence quotients are the additive groups
   `M_m(𝔭^j/𝔭^{j+1})`, which are elementary abelian p-groups.
2. Since `pO_𝔭 ⊆ 𝔭`, `Δ̄_p` is a closed subgroup of
   `∏_{𝔭 | p} (G(O_𝔭) ∩ GL_m(O_𝔭, 𝔭))`. So `Δ̄_p` is pro-p.
3. The universal property of the pro-p completion gives a continuous `π_Δ`. Its image is
   compact and contains `Δ` densely, so `π_Δ` is onto.
4. By Lemma 2, `Δ̄_p` is open in `G_p`.
5. By Lemma 3 there is an open normal `M <= Δ^_p` with `M ∩ N_Δ = 1` and `π_Δ(M)` open in
   `G_p`.
6. Lemma 4, in its `G_p` form, gives a uniform open `U <= π_Δ(M)` with `cd_p(U) = D`.
7. As in Theorem 1, `U' = (π_Δ|_M)^{-1}(U)` is a closed subgroup of `Δ^_p`. By (I5),
   `cd_p(Δ^_p) >= D > 8`.
8. `Δ^_p` is pro-p, so the pro-p form of (I6) gives `H^9(Δ^_p;F_p) != 0`.
9. `Δ` has finite index in `Γ`, so Lemma 1 gives `H^9(Δ;F_p) = 0`. ∎

## 4. Consequences for the graph

**(C1) The congruence kernel is a commensurability invariant.** For finite-index
`Γ_1 <= Γ`, Step 0 gives `C(Γ_1) = C ∩ V_1`, a subgroup of index at most `[Γ^:V_1]` in
`C`. So `C` is finite iff `C(Γ_1)` is. Any two arithmetic subgroups of `G(k)` are
commensurable, so finiteness of the congruence kernel depends only on `G/k`.

**(C2) The target claim would give a non-good hyperbolic group.** Suppose
`sp21-lattice-has-congruence-subgroup-property` holds for `Γ`. Then:
- `Γ` is torsion-free, non-elementary word-hyperbolic (Švarc–Milnor), residually finite
  (it is linear) and Kazhdan;
- by Theorem 1, no finite-index subgroup of `Γ` is good or p-good, for any prime `p`.

So the target claim produces an explicit counterexample to `every-hyperbolic-group-is-good`
among residually finite hyperbolic groups. The graph already implies the weaker universal
incompatibility:
- `every-hyperbolic-group-is-good` gives universal residual finiteness, through
  `good-cocompact-proper-groups-are-virtually-torsion-free`;
- universal residual finiteness gives the negation of the target claim, through the
  contrapositive recorded on that claim.

What is new is the lattice-local form. Goodness of **one** torsion-free arithmetic
`Sp(2,1)` lattice, or even of one of its finite-index subgroups, refutes the congruence
subgroup property for its `G`. That uses no other hyperbolic group.

**(C3) Contrapositive tests.** Each of the following would prove that `C` is infinite.
- There are a prime `p` and a finite-index `Γ_1 <= Γ` with `cd_p(Γ_1^) <= 8`. By (I6),
  equivalently, `H^9(Γ_1^;A) = 0` for every finite simple `A` with `pA = 0`
  (Theorem 1).
- There is a prime `p` with `H^9(Γ_1^;F_p) = 0` for every finite-index `Γ_1 <= Γ`
  (Theorem 2).
- There are a prime `p` and a finite-index `Δ <= Γ(p)` with `H^9(Δ^_p;F_p) = 0`. That
  makes `N_Δ` infinite (Theorem 3). By
  `sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`, it also makes
  `rank(Δ^_p) = ∞`.

**(C4) What this does not give.**
- **It decides nothing.** No goodness result is known for any Kazhdan hyperbolic group.
  The Kropholler–Wilkes route through virtually special groups dies at property (T), as
  recorded on `every-hyperbolic-group-is-good`. Residual finiteness of `Γ` is not in
  question.
- **The tests are not finite certificates.** `H^9(Γ^;A)` is the direct limit of
  `H^9(Γ/N;A)` over finite quotients through which `A` factors. Finite groups of order
  divisible by `p` typically carry nonzero degree-9 mod-p classes; for example `Z/p`
  has `H^9(Z/p;F_p) = F_p`. So vanishing in the limit, or survival in it, is a statement
  about all levels at once. No bounded computation verifies it, and a nonzero class on
  one finite quotient says nothing by itself.
- **It is not a route into the target.** Non-goodness is necessary for a finite kernel,
  not sufficient.
- **The cup-product picture is consistent.** Under a finite kernel, deep-level pro-p
  completions are uniform of dimension `D`. Their mod-p cohomology is expected to be the
  exterior algebra `Λ^*(F_p^D)`; that is Lazard for `p` odd, an unverified import that is
  not used above. The comparison map
  `Λ^* H^1(Δ;F_p) -> H^*(Δ;F_p)`, with `H^1(Δ;F_p) ≅ F_p^D`, then behaves as follows:
  - it is an isomorphism in degree 1;
  - it is injective in degree 2, since inflation `H^2(Δ^_p;F_p) -> H^2(Δ;F_p)` is always
    injective;
  - it is forced to be zero in degrees `>= 9`.

  Poincaré duality in degree 8 imposes nothing on products of 9 classes. So truncation at
  degree 8 is compatible with everything recorded here, and no contradiction arises this
  way.

## 5. Generality

Only Lemma 1 used the type of `G(k_{v_0})`, and only through `dim X = 8 < 21 <= D`. The
same proof applies in every case of
`sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`:
- for `Sp(n,1)`, `n >= 2`: `dim X = 4n` and `D = (n+1)(2n+3)·[k:Q] > 4n`, and the degree
  is `4n+1`;
- for `F_4^(-20)`: `dim X = 16` and `D = 52·[k:Q]`, and the degree is `17`.

More generally, let `Γ` be a torsion-free cocompact arithmetic subgroup of a simply
connected absolutely almost simple `G` with `G_∞` noncompact. Then:
- `D = Σ_{v | ∞} dim_R G(k_v) = [k:Q]·dim G`;
- the symmetric space has dimension `Σ_v (dim_R G(k_v) - dim K_v) < D`, because every
  maximal compact `K_v` has positive dimension.

Hence a finite congruence kernel always makes `Γ` fail goodness in degree
`dim X + 1`.

## 6. Verification status

- **Checked in this session.** The deductions in §§2–4: Lemmas 1–4, Step 0 and
  Theorems 1–3. Each step uses only (I1)–(I7) and elementary facts about profinite groups.
- **Not re-read.** The sources of (I1)–(I7), and the GJZ attribution. The numbering of
  the Serre propositions and the Platonov–Rapinchuk theorem is from memory.
- **The step a referee should attack first.** (I4) applied to a uniform group, and (I5)
  for a closed but not open subgroup. Both are textbook statements. (I5) for arbitrary
  closed subgroups is the version in Serre I §3.3.
