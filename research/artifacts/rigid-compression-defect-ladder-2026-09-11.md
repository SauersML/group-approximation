# The rigid compression defect across approximation metrics

Date: 2026-09-11. Lane `approximation-ladder`. Everything marked THEOREM has a
complete proof here. The two OPEN statements are the hinges that remain.

## 0. What this file does

The repository's operator-norm non-MF theorem, OpenAI's nonsoficity criterion
and Kun--Thom's Theorem A share one shape: one-sided compression, property (T),
and a witness that would have to stay put. This file isolates the invariant
behind all three and classifies it across metrics.

The invariant is the **rigid compression defect**. The criterion for an
approximation class `C` is

```text
DD(C):  every C-approximable group has trivial rigid defect.
```

Results:

1. **Dichotomy (Theorem 1).** `DD(C)` is equivalent to centralizer
   normalization in every `C`-ultraproduct representation of every
   infranormal Kazhdan pair. When it fails, the failure produces a
   `C`-approximable group with a nontrivial rigid defect.
2. **Sofic row (Theorem 2).** `DD(sofic)` holds; it is Kun--Thom Theorem 4.1
   read at group level. It contains Kun--Thom Theorems A and B, and it gives
   the OpenAI criterion with a stronger conclusion: the commuting factor is
   conjugated into the **center** of the compressed group, so it is abelian
   (Corollary 3).
3. **Hyperlinear row (Theorem 8).** `DD(hyperlinear)` is equivalent to
   `kt-centralizer-normalization-hs`, and it is a win--win. If it holds, the
   Kun--Thom wreath, the free-lamp amalgams and the Leavitt configuration are
   not hyperlinear. If it fails, a hyperlinear nonsofic group exists, so
   Question 3.4 is answered negatively. This corrects the remark in
   `kt-centralizer-normalization-hs` that refuting normalization is
   consistent with either answer to Q3.4.
4. **Rank row (Theorem 9).** If `DD(C-linear sofic)` holds, the weakly sofic
   wreath `W` is not linear sofic. If it fails, some linear sofic group is
   nonsofic, answering the converse that Arzhantseva--Paunescu leave open.
5. **Negative rows.** `DD` fails for weakly sofic groups (Theorem 5), for
   weak MF groups (Theorem 6), and for sofic groups when property (T) is
   asked only of the compressed subgroup (Theorem 4).
6. **Exact rows without (T).** The defect of an arbitrary compression dies in
   every LEF group (Theorem 7), extending the finite-dimensional and
   locally-residually-finite theorems already in the graph.
7. **Conservation criterion (Theorem 10).** A faithful conjugation-invariant
   size on a centralizer-capturing object forces the defect into the null set
   of the capture metric. The table in Section 10 records, row by row, which
   axiom each metric has and which it lacks.

## 1. Definitions

**Approximation classes.** Each class is given by a family of groups with
bi-invariant metrics, and a countable group is approximable when it embeds, as
a group, into a metric ultraproduct of the family:

| class | model groups and metric | ultraproduct |
| --- | --- | --- |
| sofic | `Sym(n)`, normalized Hamming | `S_U` |
| hyperlinear | `U(n)`, normalized Hilbert--Schmidt | `U(prod_U M_n)` |
| `k`-linear sofic | `GL_n(k)`, `rho(a-b)=rank(a-b)/n` | `prod_U GL_n(k)/d_U` |
| weakly sofic | all finite groups, all bi-invariant metrics | metric ultraproduct |
| weak MF | `U(n)`, operator norm | `U` of the norm matrix corona |

Standing property **(U)**: a countable group is `C`-approximable if and only
if it is isomorphic to a subgroup of a `C`-ultraproduct.

- **Weakly sofic, weak MF, linear sofic:** by definition. For linear
  soficity see Arzhantseva--Paunescu arXiv:1212.6780, Definition 4.1:
  "A countable group G is linear sofic if there exist an injective morphism
  Θ : G → Π_{k→ω} GL_{n_k}(C)/d_ω."
- **Sofic:** Arzhantseva--Paunescu, Definition 1.1, states the ultraproduct
  form as the definition.
- **Hyperlinear, with separation:** a countable subgroup `Lambda` of
  `U(prod_U M_n)` is hyperlinear. Replace the inclusion `pi` by
  `pi' = pi (+) 1`, still valued in a tracial ultraproduct of matrix algebras.
  Then `|tau(pi'(lambda))| < 1` for `lambda != 1`: equality would force
  `pi(lambda)` scalar and `(tau(pi(lambda))+1)/2` of modulus one, hence
  `pi(lambda)=1`. Tensor powers `pi'^(tensor m)` push every nontrivial trace
  to `0`, and a diagonal choice along the ultrafilter gives an embedding with
  canonical trace, i.e. normalized-HS separation `sqrt 2`.

**Rigid pairs.** A rigid pair in a group `H` is a chain `Gamma <= G <= H` with:

- `Gamma` and `G` having property (T);
- `Gamma` infranormal in `G`: the compression semigroup
  `P_Gamma = {g in G : g Gamma g^-1 <= Gamma}` generates `G`.

**Rigid defect.**

```text
D_H(G,Gamma) = << [g z g^-1, gamma] : g in G, z in C_H(Gamma), gamma in Gamma >>_H .
```

**Criteria.**

```text
DD(C):   for every countable C-approximable H and every rigid pair
         Gamma <= G <= H, one has D_H(G,Gamma) = 1.

NORM(C): for every infranormal Kazhdan pair Gamma <= G, every C-ultraproduct U
         and every homomorphism sigma : G -> U, sigma(G) normalizes
         C_U(sigma(Gamma)).
```

If `Gamma` is normal in `G`, compressors normalize `Gamma` and hence its
centralizer, so every rigid defect is trivial; only non-normal pairs matter.
A finite infranormal subgroup is normal (`finite-infranormal-subgroup-is-normal`),
so only infinite `Gamma` matter.

## 2. The dichotomy

**THEOREM 1.** Assume (U) for `C`. Then `DD(C)` holds if and only if
`NORM(C)` holds. More precisely:

- if `NORM(C)` holds for restrictions of injective `C`-representations, then
  `DD(C)` holds;
- if `NORM(C)` fails for some `(Gamma <= G, sigma, U)`, then for a witnessing
  centralizer element `z`, the countable group `H = <sigma(G), z> <= U` is
  `C`-approximable, contains the rigid pair `sigma(Gamma) <= sigma(G)`, and
  has a nontrivial rigid defect.

*Proof.*

(`NORM => DD`.) Let `H` be `C`-approximable with a rigid pair
`Gamma <= G <= H`. By (U) choose an injective `rho : H -> U`. Apply `NORM` to
`sigma = rho|G`. For `z in C_H(Gamma)` we have `rho(z) in C_U(rho(Gamma))`, so
`rho(g) rho(z) rho(g)^-1 in C_U(rho(Gamma))`, and `rho([g z g^-1, gamma]) = 1`.
Injectivity kills every generator of `D_H(G,Gamma)`.

(`not NORM => not DD`.) Suppose `sigma : G -> U` does not normalize
`C = C_U(sigma(Gamma))`. If `sigma(g) C sigma(g)^-1 <= C` for every `g in G`,
applying this to `g^-1` would give equality. So there are `g in G` and
`z in C` with `sigma(g) z sigma(g)^-1` outside `C`, i.e. some `gamma in Gamma`
with

```text
d = [sigma(g) z sigma(g)^-1, sigma(gamma)] != 1.
```

Put `H = <sigma(G), z> <= U`. It is countable (Kazhdan groups are finitely
generated) and `C`-approximable by (U). Check the pair:

- `Gamma' = sigma(Gamma)` and `G' = sigma(G)` are quotients of Kazhdan groups,
  hence Kazhdan;
- `sigma(P_Gamma) <= P_(Gamma')` and `sigma(P_Gamma)` generates `G'`, so
  `Gamma'` is infranormal in `G'`;
- `z in C_H(Gamma')` and `sigma(g) in G'`, so `d in D_H(G',Gamma')` and
  `d != 1`. ∎

*Remark.* `NORM(C)` for arbitrary homomorphisms and `NORM(C)` for
trace-preserving ones are therefore equivalent: the first half of the proof
uses only injective representations with canonical trace, and the second half
then yields normalization for every homomorphism.

**COROLLARY 1 (monotonicity).** If `C <= C'` as classes of countable groups,
then `DD(C')` implies `DD(C)`.

**COROLLARY 2 (separation forcing).**

- If `DD(C)` holds, no group with a nontrivial rigid defect is
  `C`-approximable.
- If `DD(C)` fails and `DD(C_0)` holds, then some `C`-approximable group lies
  outside `C_0`, witnessed by a group with a nontrivial rigid defect.

## 3. The sofic row

Kun--Thom, arXiv:2608.06222v1, Theorem 4.1, verbatim from
`research/artifacts/kun-thom-2608-06222-verified.md`:

> Let Γ be an infranormal subgroup of G, and suppose that both Γ and G have
> Kazhdan's property (T). If σ:G→𝒮_𝒰 is a sofic representation, then
> C_{𝒮_𝒰}(σ(Γ)) is normalized by σ(G).

**THEOREM 2.** `DD(sofic)` holds: a sofic group containing a rigid pair has
trivial rigid defect.

*Proof.* The first half of Theorem 1 uses `NORM` only for `rho|G`, where `rho`
is an injective sofic representation of `H`. Then `rho|G` is an injective
sofic representation of `G` with canonical trace, which is Theorem 4.1's
hypothesis under any reading of "sofic representation". ∎

Consequences:

- **Kun--Thom Theorem A:** the wreath `W` carries a nontrivial rigid defect
  (Section 5).
- **Kun--Thom Theorem B:** take `H = G`.
- The group double and the finite-lamp amalgams of Section 6 are nonsofic.

**COROLLARY 3 (the OpenAI criterion, strengthened).** Let `Gamma <= G` be
Kazhdan groups with `G = <Gamma, t_1, ..., t_m>` and
`t_i Gamma t_i^-1 <= Gamma`. Let `J <= G` satisfy `[Gamma, J] = 1` and
`t_1 J t_1^-1 <= Gamma`. If `G` is sofic, then

```text
t_1 J t_1^-1 <= Z(Gamma),                                          (ABEL)
```

so `J` is abelian.

*Proof.* `Gamma` is infranormal in `G`, and `J <= C_G(Gamma)`. By Theorem 2
with `H = G`, `g = t_1`, `z = j`: `[t_1 j t_1^-1, gamma] = 1` for every
`gamma in Gamma`. So `t_1 J t_1^-1 <= Gamma cap C_G(Gamma) = Z(Gamma)`. ∎

Since finitely generated abelian groups are residually finite, hence LEF,
(ABEL) contains Proposition 2.3 of the OpenAI chapter (original version, (T) of
both groups). It does not use `Gamma cap J = {1}` or finite generation of `J`.
With `J` nonabelian, e.g. Thompson's `V` in the Leavitt configuration, (ABEL)
fails outright.

## 4. The compressor group must be Kazhdan

**THEOREM 4.** `DD(sofic)` becomes false if property (T) is required only of
the compressed subgroup.

*Witness.* The literal finitely presented group `E` of `non_mf_groups_exist.tex`:

- `E` is sofic (`literal-group-sofic`);
- its affine base `Gamma` has property (T), the doubling compressor `t`
  satisfies `t Gamma t^-1 <= Gamma`, and the marked translation `v_1` lies in
  `Gamma` (`literal-kazhdan-clifford-inputs`);
- `c` centralizes `Gamma`, and `u = [t c t^-1, v_1]` normally generates
  `Rad_MF(E)`, which contains the nontrivial central involution `w`
  (`literal-mf-radical-is-unsquared-defect`, `literal-group-fails-mf-conventions`).

So `u != 1` is a compression defect of a Kazhdan subgroup inside a sofic
group. By Theorem 2, no Kazhdan group generated by `Gamma` and compressors can
contain `t` inside `E`. ∎

## 5. Weak soficity

**THEOREM 5.** The Kun--Thom wreath

```text
W = (direct_sum_(G/Gamma) Z/2) semidirect G
```

over the Theorem E pair is weakly sofic (`weakly-sofic-not-sofic`) and carries
a nontrivial rigid defect. Hence `DD(weakly sofic)` fails, and by Theorem 1
normalization fails in some metric ultraproduct of finite groups.

*Defect computation.* Let `e_x` be the lamp at coset `x`.

1. A strict compressor exists: if every element of `P_Gamma` normalized
   `Gamma`, then `G = <P_Gamma>` would normalize `Gamma`, but `Gamma` is not
   normal. So some `t in P_Gamma` has `t Gamma t^-1 < Gamma`.
2. `Gamma` fixes the coset `Gamma`, so `a = e_Gamma in C_W(Gamma)`.
3. `t a t^-1 = e_(t Gamma)`.
4. For `gamma in Gamma \ t Gamma t^-1`, `gamma t Gamma = t Gamma` would mean
   `t^-1 gamma t in Gamma`, i.e. `gamma in t Gamma t^-1`. So
   `gamma e_(t Gamma) gamma^-1 = e_(gamma t Gamma)` is a different lamp.
5. Therefore `[t a t^-1, gamma] = e_(t Gamma) e_(gamma t Gamma) != 1`. ∎

## 6. Weak MF

**THEOREM 6.** For a finite nontrivial group `K`, the amalgam

```text
H_K = G *_Gamma (Gamma x K)
```

over the Theorem E pair is weak MF (`symmetric-double-weak-mf`) and carries a
nontrivial rigid defect. Hence `DD(weak MF)` fails, and by Theorem 2 `H_K` is
nonsofic.

*Defect computation.* Let `k in K \ {1}`, so `k in C_(H_K)(Gamma)`. Take `t`
strict as in Section 5 and `gamma in Gamma \ t Gamma t^-1`.

- `t k t^-1` is a reduced alternating word `(A\C)(B\C)(A\C)` of length three,
  where `A = G`, `B = Gamma x K`, `C = Gamma`.
- Two reduced words `a_1 b a_2` and `a'_1 b' a'_2` are equal only if
  `a'_1 = a_1 c_1` for some `c_1 in C`.
- For `gamma (t k t^-1) gamma^-1 = (gamma t) k (t^-1 gamma^-1)` this requires
  `t^-1 gamma t in Gamma`, which is false.
- So `[t k t^-1, gamma] != 1`. ∎

The same data, with integer lamps over a residually finite ambient, gives a
defect that survives in the norm-corona MF radical
(`infinite-cyclic-compression-lamp-mf`, `mf-vs-tracial-radical-strict-gap`),
and `corona-commutant-growth-witness` shows normalization failing in matrix
coronas. So the operator-norm row fails in exact form. It holds in its
Hilbert--Schmidt shadow (`kazhdan-asymptotic-commutant-transport`), with only
the compressed subgroup Kazhdan.

## 7. Exact rows without property (T)

**THEOREM 7.** Let `H` be LEF, `Gamma <= H` finitely generated,
`G_comp = < s : s Gamma s^-1 <= Gamma >`. Then

```text
[g z g^-1, gamma] = 1    for all g in G_comp, z in C_H(Gamma), gamma in Gamma.
```

No property (T) enters.

*Proof.*

1. Fix `g = s_1^(e_1) ... s_r^(e_r)`, `z`, `gamma`, and a finite generating
   set `S` of `Gamma`. For each compressor `s_i` and `x in S`, choose a word
   `w_(i,x)` in `S` with `s_i x s_i^-1 = w_(i,x)`, and a word for `gamma`.
2. Let `F` be the finite set of all prefixes of all words involved, closed
   under the products that occur. LEF gives a finite group `Q` and an
   injective partial homomorphism `phi : F -> Q`.
3. In `Q` put `Gamma_Q = <phi(S)>`. Each `phi(s_i)` conjugates `phi(S)` into
   `Gamma_Q`, so `phi(s_i) Gamma_Q phi(s_i)^-1 <= Gamma_Q`, and finiteness makes
   this an equality. So `phi(s_i)` normalizes `C_Q(Gamma_Q)`, and so does
   `phi(g)`.
4. `phi(z)` commutes with `phi(S)`, so `phi(z) in C_Q(Gamma_Q)`. Then
   `phi(g) phi(z) phi(g)^-1 in C_Q(Gamma_Q)` commutes with
   `phi(gamma) in Gamma_Q`, so `phi` sends the commutator to `1`.
5. Injectivity on `F` gives the claim. ∎

This complements `locally-residually-finite-targets-kill-compression-defects`
(homomorphisms into locally residually finite targets) and
`compression-defect-dies-in-finite-dimensions` (finite-dimensional linear
representations).

## 8. The hyperlinear row

**THEOREM 8 (win--win).** Exactly one of the following holds.

- **(a)** `DD(hyperlinear)` holds. Then every group with a nontrivial rigid
  defect is non-hyperlinear: `W` (Section 5), every `H_K` (Section 6), and the
  Leavitt configuration with nonabelian commuting factor (Section 3). So
  `non-hyperlinear-group` is established.
- **(b)** `DD(hyperlinear)` fails. Then some countable hyperlinear group
  contains a rigid pair with a nontrivial rigid defect. By Theorem 2 it is not
  sofic, so `hyperlinear-nonsofic-group` is established and Question 3.4 has
  a negative answer.

By Theorem 1 and its remark, (a) is equivalent to `NORM(hyperlinear)`: for
every infranormal Kazhdan pair and every (equivalently, every trace-preserving)
homomorphism `sigma : G -> U(prod_U M_n)`, `sigma(G)` normalizes the relative
commutant `sigma(Gamma)' cap prod_U M_n`. Unitaries span a von Neumann algebra,
so normalizing the unitary centralizer normalizes the commutant. This is
exactly `kt-centralizer-normalization-hs`.

**Correction to `kt-centralizer-normalization-hs`.** That node records that
both it and `invariant-cartan-completion`, if refuted, "are consistent with
either answer to Q3.4". For the normalization claim this is not right. A
single trace-preserving `sigma` failing normalization produces, by Theorem 1,
a countable subgroup `H` of the tracial ultraproduct's unitary group with a
nontrivial rigid defect. `H` is hyperlinear by (U), and nonsofic by Theorem 2.
Refuting the normalization claim answers Q3.4 negatively. Nothing here says
which branch holds.

## 9. The rank row

**THEOREM 9.** Arzhantseva--Paunescu prove sofic `<=` complex-linear sofic
`<=` weakly sofic (arXiv:1212.6780, Theorem 1.3: "Sofic groups are linear
sofic, while linear sofic groups are weakly sofic"). They note after
Proposition 4.5 that the converse of the first inclusion is open. Then:

- if `DD(C-linear sofic)` holds, `W` is weakly sofic but not linear sofic, so
  the second inclusion is strict;
- if it fails, some linear sofic group has a nontrivial rigid defect and is
  therefore nonsofic, so the first inclusion is strict.

*Proof.* (U) holds by their Definition 4.1. Apply Theorem 1, Theorem 2,
Theorem 5 and Corollary 2. ∎

Soficity is already known to be strictly stronger than weak soficity (`W`), so
one of the two inclusions is strict in any case. Theorem 9 says which one in
terms of `DD`.

## 10. The conservation criterion and the table

**THEOREM 10.** Let `U` be a group with a bi-invariant pseudometric `delta`,
and `N_delta = {x : delta(x,1) = 0}`, a normal subgroup. Let `K` be a class of
subgroups of `U`, closed under conjugation. Suppose each `L in K` carries a
set `A(L)` in some ambient on which `U` acts by conjugation, together with a
size `s(A(L)) in [0, infinity)`, such that:

- **(A1)** `A(u L u^-1) = u A(L) u^-1` and `s` is conjugation invariant;
- **(A2)** `L' <= L` in `K` implies `A(L) <= A(L')`;
- **(A3)** `X <= Y` and `s(X) = s(Y)` imply `X = Y`;
- **(A4)** `C_U(L) <= A(L)`, and `[x, l] in N_delta` for every `x in A(L)`,
  `l in L`.

Then for every homomorphism `sigma : H -> U` with `sigma(Gamma) in K`, every
`g in G_comp(Gamma)`, `z in C_H(Gamma)` and `gamma in Gamma`,

```text
sigma([g z g^-1, gamma]) in N_delta.
```

*Proof.*

1. For a compressor `s`, (A2) and (A1) give
   `A(sigma(Gamma)) <= A(sigma(s Gamma s^-1)) = sigma(s) A(sigma(Gamma)) sigma(s)^-1`.
2. The sizes are equal, so (A3) makes this an equality. So compressors, and
   hence `G_comp`, normalize `A(sigma(Gamma))`.
3. `sigma(z) in C_U(sigma(Gamma)) <= A`, so `sigma(g z g^-1) in A`.
4. (A4) gives `[sigma(g z g^-1), sigma(gamma)] in N_delta`. ∎

Instances and failures:

- **Finite groups:** `A = C_U(L)`, `s` = cardinality, `delta` discrete. This
  gives Theorem 7 and the locally residually finite theorem.
- **`GL_n(k)`:** `A(L)` = commutant algebra, `s` = dimension. This gives
  `compression-defect-dies-in-finite-dimensions`.
- **Norm matrix corona:** `K` = images of Kazhdan groups. `A(L)` is the
  ultraproduct of the ranges of the rounded Kazhdan projections of the adjoint
  action on `L^2(M_n)`, and `s` is their rank germ. Op-norm closeness makes
  the ranks exact, and `delta` = normalized HS. This gives
  `kazhdan-asymptotic-commutant-transport`.
- **Tracial ultraproduct (HS):** `A(L) = sigma(L)' cap prod_U M_n` satisfies
  (A1), (A2) and (A4) with `delta = 0`. Property (T) supplies rounding: a
  spectral gap on `L^2(M)` minus `L^2(M^Gamma)`. What is missing is (A3): there
  is no faithful conjugation-invariant size on von Neumann subalgebras of
  infinite index (`invariant-size-collapse`: the trace is refinement-blind).
- **Symmetric-group ultraproduct (Hamming):** (A3) is absent at the
  ultraproduct level too; invariant sigma-algebras admit strict
  shift-compressions. Kun--Thom obtain normalization anyway, by finite-stage
  median arguments on vertex masses and isotropy orders of the cluster
  groupoid of expander components, which is a finite-stage size.
- **Rank ultraproduct:** (A3) is absent, and property (T) gives no rounding.
- **Metric ultraproducts of finite groups (weak sofic):** no Hilbert structure,
  no size, and `DD` fails (Theorem 5).

| class | (T) rounding | faithful size | `DD` | evidence |
| --- | --- | --- | --- | --- |
| locally RF targets, f.d. linear | not needed | cardinality / dimension | holds, no (T) | LRF node; Lean f.d. sterility |
| LEF | not needed | cardinality at finite stages | holds, no (T) | Theorem 7 |
| sofic | Kun decomposition | finite-stage medians | holds | Theorem 2 (Kun--Thom 4.1) |
| sofic, (T) of `Gamma` only | -- | -- | fails | Theorem 4, literal `E` |
| weakly sofic | none | none | fails | Theorem 5, `W` |
| weak MF, exact | adjoint corona | rank germ (shadow only) | fails | Theorem 6, `H_K` |
| weak MF, HS shadow | adjoint corona | rank germ | holds, (T) of `Gamma` only | asymptotic-commutant transport |
| hyperlinear | spectral gap on `L^2(M)` | missing | OPEN, win--win | Theorem 8 |
| `C`-linear sofic | missing | missing | OPEN, win--win | Theorem 9 |

## 11. What a proof of the hyperlinear row must contain

Theorem 10 shows that (T)-rounding is available in the tracial ultraproduct
and only a size is missing. Four routes are already excluded or reduced:

1. **A universal size on relative commutants.** Excluded: refinement-blind
   trace, infinite index.
2. **A compressor clause attached to an abstract Kazhdan block decomposition.**
   Excluded by `nonmonomial-multiplicity-obstructs-hs-compressor-transport`.
3. **Exactifying the actor restriction along one compressor.** Excluded by
   `kt-single-compressor-canonical-lamps-do-not-exactify-actor`.
4. **Flexibly exactifiable actor restrictions.** Such models do kill the
   defect: round `z` into the exact finite-dimensional commutant of the
   rounded actor, then apply commutant no-growth. So `DD(hyperlinear)`
   reduces to multi-compressor exactification, which is where
   `kt-wreath-relative-canonical-actor-exactification` sits.

The positive Hamming proof uses a size that exists only at finite stages. An HS
analogue must therefore work at finite matrix levels with multiplicity
coordinates, not in the von Neumann limit.
