# Pure braid characters that survive on Dehn twists: Sigma^{n-3} and twist depth

Swarm lane `pure-braid-bnsr-complements-are-real-resonance-varieties`, 2026-09-16. Status: UNREVIEWED.

## 0. Notation

- `P_n = PMod(D_n)`: pure mapping classes of the disk with `n` punctures, acting on the curve complex
  `C = C(D_n)`. Its vertices are isotopy classes of essential simple closed curves: curves bounding a disk that
  contains a set `A` of punctures with `2 <= |A| <= n-1`. Collapsing the boundary to a puncture identifies `C`
  with `C(S_{0,n+1})`, and `P_n` acts through `H_n = P_n / Z(P_n) = PMod(S_{0,n+1})`.
- `chi = sum_{i<j} a_ij omega_ij`, where `omega_ij` is the winding number of strands `i` and `j`
  (arXiv:1507.08597, Section 3.1).
- Type of a curve `c`: the set `A(c)` of punctures inside `c`. The twist value of `chi` on `A` is
  `c_A(chi) = sum_{i<j in A} a_ij`. Zero types: `Z(chi) = {A : 2 <= |A| <= n-1, c_A = 0}`.
- A family of subsets of `[n]` is laminar if any two members are nested or disjoint. The twist depth `d(chi)` is
  the largest size of a laminar subfamily of `Z(chi)`. The depth is 0 iff no `c_A` vanishes.
- A multicurve (simplex of `C`) is zero if every curve in it has a zero type.
- `Stab(sigma)` is the setwise stabilizer in `P_n` of a simplex `sigma`.

## 1. Tools

(T1), (T2), (T3) are quoted verbatim from Zaremsky arXiv:1803.02717, Citations 1.8, 1.12 and 1.9. They were
re-read on 2026-09-16; the same quotations are in `zp-pure-braided-bht-sigma-2026-09-13.md`, Section 1.

- (T1) [MMV01, Theorem 2.4]: "Let G be a group acting cocompactly on an (m−1)-connected complex X. Let
  χ ∈ Hom(G,ℝ) be a character such that for any cell σ in X with dimension dim(σ) ≤ m, the restriction
  χ|Stab_G(σ) is non-trivial. If for all σ with dim(σ) < m, we have that Stab_G(σ) is of type F_{m−dim(σ)} and
  [χ|Stab_G(σ)] ∈ Σ^{m−dim(σ)}(G_σ), then [χ] ∈ Σ^m(G)."
- (T2) [MMV01, Theorem 2.1]: "Let G be a group of type F_m and let χ ∈ Hom(G,ℝ). If χ(Z(G)) ≠ 0 then
  [χ] ∈ Σ^m(G)."
- (T3) [Mei97, Corollary 2.8]: "Let π: G → H be a split epimorphism of groups. Let χ be a character of H, so
  χ∘π is a character of G. For any m ≥ 1, if [χ∘π] ∈ Σ^m(G) then [χ] ∈ Σ^m(H)."
- (H) Connectivity of curve complexes of spheres. Davis–Huang, *Bordifications of hyperplane arrangements and
  their curve complexes*, arXiv:2003.13553v2 (read 2026-09-16). Main Theorem (= Theorem 5.12), for the
  complexification in `C^N` of a real simplicial arrangement with `l` irreducible factors:
  "(ii) … The faces of Y are indexed by C and the group G = π_1(X) acts on C with quotient space I_0.
  (iii) The simplicial complex C is homotopy equivalent to a wedge of (N − l − 1)-spheres (where
  dim C = N − l − 1). … (vi) The stabilizer of each simplex of C is the fundamental group of M(A_0) where A_0
  is also the complexification of some real simplicial arrangement." Their remarks on `A_{n-1}` state that the
  algebraic curve complex of `M(A_{n-1})` "is canonically isomorphic to the curve complex" of `S_{0,n+1}`.
  With `N = n-1` and `l = 1`, `C(S_{0,n+1}) ≃ ∨ S^{n-3}`, so it is `(n-4)`-connected. This is Harer's theorem
  (Invent. Math. 84, 1986); Harer's original was not re-read.
- (FM) Standard mapping class group facts (Farb–Margalit, *A primer on mapping class groups*; not re-read):
  `f T_c f^{-1} = T_{f(c)}`; the change of coordinates principle; the cutting homomorphism for the stabilizer of
  a multicurve.

## 2. Lemmas on the action

**Lemma 1 (types).** (a) `A(f(c)) = A(c)` for every `f` in `P_n`. (b) Distinct curves of a multicurve have
distinct types, and the types of a multicurve form a laminar family. (c) `Stab(sigma)` fixes every vertex of
`sigma`, so `Stab(sigma)` is the intersection of the vertex stabilizers.

*Proof.* (a) `f` fixes every puncture and maps the disk bounded by `c` to the disk bounded by `f(c)`.
(b) Represent the curves disjointly. Disjoint Jordan curves in the plane bound disks that are nested or
disjoint, so the types are nested or disjoint. If the disks are disjoint the types differ, because types are
nonempty. If `c` lies inside `c'` and the types agree, the region between them is an annulus without punctures,
so `c` and `c'` are isotopic. (c) follows from (a) and (b). ∎

**Lemma 2 (central twists).** For `c` in `sigma`, the Dehn twist `T_c` lies in the center of `Stab(sigma)`, and
`chi(T_c) = c_{A(c)}`.

*Proof.* `T_c` is supported in an annulus around `c`, disjoint from the other curves of `sigma`, so
`T_c` is in `Stab(sigma)`. For `f` in `Stab(sigma)`, `f T_c f^{-1} = T_{f(c)} = T_c` by (FM) and Lemma 1(c).
Let `A = A(c)` and let `c_A` be a round curve around `A`. Both `c` and `c_A` cut `D_n` into a disk with punctures
`A` and an annulus with punctures `[n] \ A`. Gluing label-preserving homeomorphisms of the two pieces (change of
coordinates, (FM)) gives `g` in `P_n` with `g(c_A) = c`. Then `T_c = g T_{c_A} g^{-1}` and
`chi(T_c) = chi(T_{c_A})`. As a braid, `T_{c_A}` is the full twist on the strands `A`. Forgetting all strands
except `i` and `j` maps it to the full twist of `P_2` if `i, j` are both in `A`, and to the identity otherwise.
So `omega_ij(T_{c_A})` is 1 or 0 accordingly, and `chi(T_c) = sum_{i<j in A} a_ij`. (The normalization
`omega_ij(Delta^2) = 1` agrees with `omega_ij(Delta) = 1/2` in arXiv:1507.08597, proof of Lemma 3.7.) ∎

**Lemma 3 (cocompactness).** (a) `P_n` has finitely many orbits of simplices of `C`. (b) For every simplex
`sigma`, `Stab(sigma)` has finitely many orbits of simplices of the link `L(sigma)`.

*Proof.* (a) By Lemma 1(b), the types of a multicurve form a laminar family of distinct sets. Two multicurves with
the same family of types cut `D_n` into pieces that match with labels. Gluing label-preserving homeomorphisms of
the pieces (change of coordinates, (FM)) gives an element of `P_n` carrying one to the other. There are finitely
many laminar families. (b) Suppose the pairs `(sigma, sigma ∪ tau)` and `(sigma, sigma ∪ tau')` are in one
`P_n`-orbit, via `g`. Then `g sigma = sigma`, so `g` is in `Stab(sigma)`, and `g tau = tau'`. Hence the
`Stab(sigma)`-orbits of simplices `tau` of `L(sigma)` inject into the `P_n`-orbits of nested pairs of
multicurves. By Lemma 1 and the argument of (a), such an orbit is determined by a laminar family with a marked
subfamily, and there are finitely many of those. ∎

**Lemma 4 (stabilizers have type F).** `Stab(sigma)` is of type `F` for every simplex `sigma`.

*Proof.* Pass to `H_n = P_n / <T_∂>`, where `T_∂` is the boundary twist, which is central. The cutting
homomorphism (FM) maps `Stab_{H_n}(sigma)` onto `prod_P PMod(P)`, over the pieces `P` of `S_{0,n+1} \ sigma`
(spheres with `k_P >= 3` marked points). Its kernel is the free abelian group on the twists about the curves of
`sigma`. The map is onto `prod PMod(P)`: an element fixes every marked point and every curve with its sides
(Lemma 1), and pure classes of the pieces glue. `PMod(S_{0,k}) = H_{k-1}` has a finite `K(pi,1)`
(`zp-pure-braid-bnsr-top-range-2026-09-13.md`, Lemma L, for `k >= 4`; trivial for `k = 3`). Extensions of type `F`
groups by type `F` groups are of type `F`. So `Stab_{H_n}(sigma)` has type `F`, and so does its preimage
`Stab(sigma)`, an extension by `<T_∂> = Z` (the boundary twist acts trivially on `C`). Cross-check: Davis–Huang (vi) gives
`pi_1(M(A_0))` with `A_0` complexified simplicial, which is of type `F` by Deligne's asphericity theorem and a
finite Salvetti complex. Those originals were not re-read. ∎

**Lemma 5 (links).** If `sigma` has `s` curves, then `L(sigma)` is `(n - 4 - s)`-connected.

*Proof.* A curve of `D_n` that is disjoint from `sigma` and not in `sigma` is an essential, non-peripheral curve
in exactly one piece `P`. Hence `L(sigma)` is the join of the curve complexes `C(P)` over the `s + 1` pieces,
where `P` is a sphere with `k_P` marked points: punctures, the boundary, and the two sides of each curve. So
`sum_P k_P = n + 1 + 2s`. By (H) applied to `S_{0,k}` (`N = k - 2`), `C(S_{0,k})` is `(k-5)`-connected for
`k >= 4`. For `k = 3` it is empty, that is `(-2)`-connected. A join of an `a`-connected and a `b`-connected
complex is `(a + b + 2)`-connected (Milnor). So `L(sigma)` is
`(sum_P (k_P - 5) + 2s) = (n - 4 - s)`-connected. ∎

## 3. Theorem M

**Theorem M.** Let `n >= 4` and let `chi = sum a_ij omega_ij` satisfy `c_A(chi) != 0` for every `A <= [n]` with
`2 <= |A| <= n-1`. Then `[chi]` is in `Sigma^{n-3}(P_n)`.

*Proof.* Apply (T1) with `G = P_n`, `X = C` and `m = n - 3`. `C` is `(n-4)`-connected (Lemma 5 with `s = 0`), and
the action is cocompact (Lemma 3(a)). Let `sigma` be any simplex and `c` a curve in `sigma`. By Lemma 2, `T_c` is
central in `Stab(sigma)` with `chi(T_c) = c_{A(c)} != 0`. So `chi|Stab(sigma)` is nontrivial. `Stab(sigma)` has
type `F` (Lemma 4), and (T2) puts `[chi|Stab(sigma)]` in `Sigma^k(Stab(sigma))` for every `k`. All hypotheses
of (T1) hold, so `[chi]` is in `Sigma^{n-3}(P_n)`. ∎

**Remarks.**
1. For `n = 4`, Theorem M says that the complement of `Sigma^1(P_4)` lies in the union of the twist hyperplanes
   `c_A = 0`. That agrees with Koban–McCammond–Meier. A triple circle (supported on `{i,j,k}` with total zero)
   lies in `c_ijk = 0`. A 4-strand circle (`a_ij = a_kl`, `a_ik = a_jl`, `a_il = a_jk`, `a_ij + a_ik + a_il = 0`)
   also lies in `c_ijk = 0`.
2. Zaremsky, arXiv:1507.08597, Proposition 5.6 (re-read 2026-09-16) takes `sum a_ij = 0` with exactly one
   `a_ij` positive (or exactly one negative) and gives `[chi]` not in `Sigma^{n-2}(P_n)`, and "If moreover none
   of the a_{i,j} are zero, then [chi] ∈ Σ^{n−3}(P_n)". Theorem M contains that positive half. If `a_kl > 0` is the
   only positive coefficient and all the others are negative, then a sum over a proper nonempty set of pairs is
   nonzero: with `a_kl` it exceeds the full sum 0, and without it it is negative. Each `c_A` with
   `2 <= |A| <= n-1` is such a sum. Theorem M also covers characters with several positive coefficients, such as
   `a_12 = a_34 = 1`, `a_13 = a_24 = -1`, other `a_ij` generic with total zero, where every `c_A` is nonzero.
3. With Theorem T (`pure-braid-top-bnsr-invariants-are-center-nonvanishing`): if `sum a_ij = 0` and every `c_A`
   is nonzero, then `[chi]` is in `Sigma^{n-3}(P_n) \ Sigma^{n-2}(P_n)`.

## 4. Theorem M_d (twist depth)

**Theorem M_d.** Let `n >= 4`, `chi != 0` and `d = d(chi) <= n - 4`. Then `[chi]` is in
`Sigma^{n-3-d}(P_n)`. Theorem M is the case `d = 0`.

**Lemma 6 (nontriviality).** If `d(chi) <= n - 3`, then `chi|Stab(sigma)` is nontrivial for every simplex
`sigma` of `C`.

*Proof.* Extend `sigma` to a maximal multicurve `tau` with `n - 2` curves. By Lemma 1(b) its types form a laminar
family of size `n - 2 > d`, so some `c` in `tau` has `c_{A(c)} != 0`. `T_c` is disjoint from every curve of
`sigma`, so it lies in `Stab(sigma)`, and `chi(T_c) != 0` (Lemma 2). ∎

**Lemma 7 (zero multicurves).** Let `d = d(chi) <= n - 4`, `l = n - 3 - d`, and let `sigma` be a zero multicurve
with `s >= 1` curves. Then `[chi|Stab(sigma)]` is in `Sigma^l(Stab(sigma))`.

*Proof.* The types of `sigma` form a laminar zero family, so `s <= d`. Induct downward on `s`. Apply (T1) with
`G = Stab(sigma)`, `X = L(sigma)` and `m = l`.

- Connectivity: `L(sigma)` is `(n-4-s)`-connected (Lemma 5), and `n - 4 - s >= n - 4 - d = l - 1`.
- Cocompactness: Lemma 3(b).
- A simplex `rho` of `L(sigma)` with `t >= 1` curves has `Stab_G(rho) = Stab(sigma ∪ rho)` by Lemma 1(c).
  This restriction is nontrivial by Lemma 6, and it has type `F` by Lemma 4.
- Let `dim rho = t - 1 < l`. If `sigma ∪ rho` contains a curve of nonzero type, (T2) gives `Sigma^infinity`
  (Lemma 2). Otherwise `sigma ∪ rho` is a zero multicurve with `s + t > s` curves, and by induction the
  restriction is in `Sigma^l`. That contains `Sigma^{l - dim rho}`, since `dim rho >= 0`.
- Base: if `s = d`, no zero multicurve properly contains `sigma`, so only the (T2) case occurs.

(T1) gives the claim. ∎

*Proof of Theorem M_d.* Apply (T1) with `G = P_n`, `X = C` and `m = l = n - 3 - d >= 1`. `C` is
`(n-4)`-connected, which contains `(l-1)`-connected, and the action is cocompact. Every cell stabilizer has type
`F` and a nontrivial restriction (Lemmas 4 and 6). Let `dim sigma < l`. If `sigma` contains a curve of nonzero
type, (T2) applies. Otherwise Lemma 7 gives `Sigma^l`, which contains `Sigma^{l - dim sigma}`. ∎

**The recursion, explicitly.** Let `f(s)` be the level provable for a zero multicurve with `s` curves. The
constraints are `f(s) <= n - 3 - s` (connectivity of `L(sigma)`) and `f(s) <= f(s+t) + t - 1` for `t >= 1`
(the cells), with `f(d) = n - 3 - d`. The largest solution is `f(s) = n - 3 - d` for all `s`, which is the level
used above. The loss comes from the `t = 1` constraint `f(s) <= f(s+1)`.

## 5. Consequences and sharpness

**5.1 The resonance conjecture off the twist hyperplanes.** Let `2 <= m <= n-3`. For every character with no
vanishing twist value, Theorem M gives `Sigma^{n-3}`, which contains `Sigma^m`. So the "non-resonant implies
`Sigma^m`" direction of `pure-braid-bnsr-complements-are-real-resonance-varieties` holds on the complement of the
finitely many hyperplanes `c_A = 0`. With the upper bound `arrangement-bnsr-invariants-avoid-real-resonance`,
this forces `R^{<=n-3}(P_n; R)` into the union of these hyperplanes. The `c_A` are the sums of the weights over
the dense edges of the braid arrangement, and the symmetric form on `[n+1]` covers the edge at infinity. So this
consequence is the classical non-resonance vanishing of Aomoto cohomology below the top degree (Yuzvinsky;
Schechtman–Terao–Varchenko; not re-read). The experiment in Section 6 confirms `H^{<=n-3} = 0` at random such
characters for `n = 5, 6`.

**5.2 Sharp for one strand block.** Let `A <= [n]` with `|A| = n - f >= 3`, and let `chi` be a generic character
supported on the pairs inside `A` with total zero. By `pure-braid-product-projections-obstruct-bnsr-invariants`
(`r = 1`, `D = |A| - 2`), `[chi]` is not in `Sigma^{|A|-2}(P_n)`.

*Claim.* `d(chi) = f`, so Theorem M_d gives `[chi]` in `Sigma^{|A|-3}(P_n)`. Hence `[chi]` is in
`Sigma^{|A|-3} \ Sigma^{|A|-2}`, and the level of M_d is exact on this family.

*Proof.* For generic parameters, `c_B = 0` iff `|B ∩ A|` is 0, 1 or `|A|`. A proper subset `S` of `A` with
`|S| >= 2` has a nonzero sum over its pairs, for generic zero-sum weights.
- Lower bound. Pick `x` in `A` and the free strands `y_1, ..., y_f`. The chain `{x, y_1} <= {x, y_1, y_2} <= ...`
  has `f` zero types, with sizes from 2 to `f + 1 <= n - 2`.
- Upper bound. Let `L` be a laminar family of zero types. Add all singletons and `[n]`, and view the result as a
  rooted tree with `n` leaves. Every internal node has at least 2 children, and
  `sum_v (c_v - 1) = n - 1` over internal nodes `v`. Let `B` be the smallest node containing `A`. A child of `B`
  meets `A` in at most one point: it is a zero type that cannot contain `A`, or it is a singleton. So `B` has at
  least `|A|` children. Hence the number of internal nodes is at most `n - 1 - (|A| - 2)`, and
  `|L| <= n - 2 - (|A| - 2) = f`. ∎

By the `S_{n+1}`-symmetry of zero-sum characters, this also covers the one-petal sunflower characters of
`pure-braid-sunflower-characters-obstruct-bnsr-invariants`. There `c_B = c_{B^c}`, and laminarity of splits of
`[n+1]` is symmetric.

**5.3 Not sharp in general.**
- `n = 5`, generic with `c_12 = c_34 = 0` and total zero: `d = 2`, so M_d gives nothing. But `H^1 = 0` (Section 6),
  so the character is on no Koban–McCammond–Meier circle and lies in `Sigma^1(P_5)`.
- Two disjoint triples in `P_6`: the transversal pairs `{1,4}, {2,5}, {3,6}` are zero types, so `d = 3` and M_d
  gives nothing. The product-projection claim records these characters in `Sigma^1(P_6)`.

So twist depth is not the right invariant beyond one block. The level loss comes from the `t = 1` step of the
recursion, where a zero vertex is handled by the stabilizer of a larger zero multicurve at the same level.

## 6. What remains: twist hyperplanes

**6.1 Reduction.** Let `2 <= m <= n - 3`, which is only possible for `n >= 5`. By 5.1, the conjecture in degree
`m` is equivalent to the upper bound plus the following statement.

(Hole) A character with `sum a_ij = 0`, some `c_A = 0`, and `H^i(A(P_n), chi /\) = 0` for all `i <= m` lies in
`Sigma^m(P_n)`.

Degree 1 is Koban–McCammond–Meier, and degrees `>= n - 2` are Theorem T. For `sum a_ij != 0` everything is known
(Theorem T). The smallest open case is `n = 5`, `m = 2`. Up to `S_6`, the twist hyperplanes there are `c_12 = 0`
and `c_123 = 0`. The hyperplane `c_1234 = 0` is of pair type on `[6]`.

**6.2 Computation** (`experiments/pure-braid-bnsr-complements-are-real-res-2026-09-16/`). The script is
`twist_hyperplane_aomoto.py`; its output is in `results.json` and `run.log`. It computes `dim H^i` of the Aomoto
complex for `i <= n - 3` over `F_p` for two primes, reusing the Orlik–Solomon code of
`experiments/zp-bf-n-r-first-leaf-star-resonance-2026-09-16/os_resonance_bf.py`. A zero dimension over `F_p` is
exact over `Q`.

- Positive controls:
  - `chi` on `{1,2,3}` in `P_5`: `H^1 = 1`.
  - `L_[5]` (all rows zero): `H^2 = 2`.
  - Two triples in `P_6`: `H^2 = 1`.
- Generic zero-sum characters: `H^{<=2} = 0` for `n = 5` and `H^{<=3} = 0` for `n = 6`, three samples each.
- Integer characters, generic apart from the stated conditions (entries up to `10^4`), three samples each unless
  noted. Every sample has `H^{<=n-3} = 0`.
  - `n = 5`: `c_12 = 0` (`d = 1`), `c_123 = 0` (`d = 1`), `c_1234 = 0` (`d = 1`), `c_12 = c_34 = 0` (`d = 2`),
    `c_12 = c_123 = 0` (`d = 2`), `c_12 = c_345 = 0` (`d = 2`), `c_123 = c_345 = 0` (`d = 1`).
  - `n = 6`: `c_12 = 0`, `c_123 = 0`, `c_1234 = 0` (`d = 1`), `c_12 = c_34 = 0`, `c_12 = c_123 = 0`,
    `c_123 = c_456 = 0` (`d = 2`), `c_12 = c_34 = c_56 = 0` (`d = 3`).
  - `n = 7`: `c_12 = 0`, one sample (`d = 1`).

So the resonance upper bound gives no obstruction at generic points of these twist hyperplanes and
intersections. The conjecture predicts, for example, `Sigma^2(P_5)` membership on `c_12 = 0` and on `c_123 = 0`,
where M_d gives only `Sigma^1`.

**6.3 Why the curve complex criterion stops here.** Let `c` be a curve of pair type `{1,2}` and let
`sum a_ij = 0 = a_12`. Cutting along `c` gives `Stab(c) = <T_c> x P_{n-1}`, where `P_{n-1}` acts on the strands
`{*, 3, ..., n}` with `*` the disk around 1 and 2, and the splitting is by cabling (FM; not re-derived in detail).
Since `chi(T_c) = 0`, `chi|Stab(c) = psi o pi` for the projection `pi` onto `P_{n-1}`, with `psi(Delta^2) =
chi(T_∂) = 0` and `psi != 0` for generic `chi` (for example `psi(omega_34) = a_34`). By Theorem T, `[psi]` is not
in `Sigma^{n-3}(P_{n-1})`. By (T3), `[chi|Stab(c)]` is not in `Sigma^{n-3}(Stab(c))`. So the vertex condition of
(T1) on `C` fails at level `n - 3` at every zero pair-type vertex. A proof of (Hole) needs another complex (for example `C` with the zero vertices
removed, whose links `C(S_{0,n})` are only `(n-5)`-connected), or Morse theory with `chi` directly, as in
Zaremsky's proof of Proposition 5.6.

**6.4 Novelty (bounded).** arXiv listing searches on 2026-09-16 (2024–2026: higher BNSR invariants, pure braid
groups, resonance) found no statement of Theorem M or M_d. Checked:
- arXiv:2502.16026 (tropical integral jump loci, 2025-02): abstract only, upper bounds; not re-fetched today because
  the API connection was reset.
- Zaremsky arXiv:1507.08597 and arXiv:1803.02717.
- Davis–Huang arXiv:2003.13553v2.

The argument is a direct application of the Meier–Meinert–VanWyk criterion to the curve complex, so an unnoticed
earlier statement is possible.

**6.5 Lead for bF_{n,r} (evidence only).** For
`bf-n-r-twist-invisible-braid-characters-in-sigma-infinity`, Lemma 5 of `zp-pure-braided-bht-sigma-2026-09-13.md`
asks for `[Phi_k]` in `Sigma^j(P_k)` for all large `k`. By Theorem M_d it suffices that `k - d(Phi_k) -> infinity`.

- Intervals of `td + 1` strands are zero types on all of `W_0`. In the rooted tree of a laminar family of such
  intervals, each node has a number of children `≡ 1 mod (n-1)`, hence at least `n`. So they force only
  `d >= floor((k-2)/(n-1))`.
- The script `bf_twist_depth.py` in the experiment folder, with output `bf_twist_depth.json`, computed the depth
  exactly at two random integer points of `W_0` for `n = 3, 4` and `k <= 13`. In every case
  `d(Phi_k) = floor((k-2)/(n-1))`, even where non-interval zero types occur.
- First-leaf characters have `a_pq = 0` for `2 <= p < q <= k`, so `d(Phi_k) >= k - 2`. Twist depth cannot
  give the whole claim.

What is open for that lane: an upper bound on the depth at very generic `phi`, for all `k`.
