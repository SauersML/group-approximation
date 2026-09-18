# Measured absorption is capped by the almost malnormal hull

Worker `swarm-0917-w5-fp-lf-finite-cost`, 2026-09-17.

Target hole: `fpbs-locally-free-free-actions-have-finite-cost` (and its child
`fpbs-locally-free-malnormally-exhausted-finite-cost`).

**Summary.**
- Wave 4 showed that group-element wq-normal absorption from `E_{a|H}` reaches
  exactly `E_{a|W(H)}`.
- One might hope that measurable choices do better. A partial isomorphism whose
  "label" `gamma(x)` varies with `x`, or a normalizing or quasi-normalizing
  element of the full pseudogroup, or the Gaboriau--Tucker-Drob window
  condition `phi(S) ∩ S` ergodic, could perhaps push past `W(H)`.
- **Theorem A** shows they cannot. If `S` is any Borel subrelation of
  `E_{a|Lambda}` and `phi ∈ [[E_a]]`, then on the part of `dom phi` where the
  contact relation `S_phi` has infinite classes, the label `gamma(x)` lies in
  `Q(Lambda)`, almost surely.
- **Corollary B.** Every transfinite chain of infinite-contact steps from a
  subrelation of `E_{a|Lambda}` stays inside `E_{a|W(Lambda)}`, and the chain
  of Wave 4 attains this cap.
- **Proposition E.** For an increasing exhaustion `Gamma = ∪ M_n` by finitely
  generated subgroups, `C(a) < ∞` if and only if `relC(E_a | E_{a|M_n}) -> 0`.
- **Consequence.** In a malnormally exhausted locally free group such as
  `Gamma_mal`, every proof of finite cost has to pay for partial isomorphisms
  with finite contact, with total mass tending to 0. Zero-cost absorption of
  any kind cannot leave a stage.

Nothing is imported except the complete-section fact used only in Lemma 0
(the positive direction, which is not needed for the obstruction), and the
hull construction of `fpbs-wq-normal-hull-is-almost-malnormal` (ESTABLISHED).

## 0. Conventions

- `Gamma` is a countable group. `a` is a free p.m.p. Borel action of `Gamma`
  on a standard probability space `(X, mu)`. Discarding an invariant null set,
  `g x != x` for all `x` and `g != e`.
- `E_a` is the orbit relation. For `L <= Gamma`, `E_{a|L}` is the orbit
  relation of the restriction to `L`.
- Enumerate `Gamma = {g_0 = e, g_1, g_2, ...}`.
- `[[E_a]]` is the full pseudogroup: Borel bijections `phi : dom phi -> ran phi`
  between Borel sets with `phi x E_a x`. For such `phi`, freeness gives a
  unique Borel **label** `gamma : dom phi -> Gamma` with `phi x = gamma(x) x`,
  since the sets `{x : phi x = g x}` are Borel and pairwise disjoint. Every
  `phi ∈ [[E_a]]` preserves `mu`, because it is a countable disjoint union of
  restrictions of the measure-preserving maps `a(g)`.
- For `Lambda <= Gamma` and `g ∈ Gamma` put
  `I_Lambda(g) = Lambda ∩ g^{-1} Lambda g` and
  `Q(Lambda) = {g : I_Lambda(g) infinite}`.
- A graphing is a countable family of elements of `[[E_a]]`. Its cost is the sum
  of the measures of the domains. For Borel subrelations `S ⊆ R ⊆ E_a`,
  `relC(R | S)` is the infimum of the costs of graphings `Phi ⊆ R` such that
  `S` and `Phi` together generate `R`.

**Fact 0.1 (double cosets).** `I_Lambda(l_1 g l_2) = l_2^{-1} I_Lambda(g) l_2`
for `l_1, l_2 ∈ Lambda`. Hence `Q(Lambda)` is a union of
`(Lambda, Lambda)`-double cosets. Also `I_Lambda(g^{-1}) = g I_Lambda(g) g^{-1}`,
so `Q(Lambda) = Q(Lambda)^{-1}`.

*Proof.* `Lambda ∩ l_2^{-1} g^{-1} l_1^{-1} Lambda l_1 g l_2
= l_2^{-1}(Lambda ∩ g^{-1} Lambda g) l_2`, because `l_1^{-1} Lambda l_1 = Lambda`
and `l_2^{-1} Lambda l_2 = Lambda`. The inverse statement is conjugation by `g`. ∎

**Fact 0.2 (almost malnormal).** If `M` is infinite and almost malnormal
(`g M g^{-1} ∩ M` finite for every `g ∉ M`), then `Q(M) = M`.

*Proof.* For `g ∈ M`, `I_M(g) = M` is infinite. For `g ∉ M`,
`I_M(g) = g^{-1}(g M g^{-1} ∩ M) g` is finite. ∎

**Contact relation.** For a Borel subrelation `S ⊆ E_a` and `phi ∈ [[E_a]]`,
put

```text
S_phi = { (x, y) ∈ S : x, y ∈ dom phi and (phi x, phi y) ∈ S },
D_phi(S) = { x ∈ dom phi : the S_phi-class of x is infinite }.
```

- `S_phi` is an equivalence relation on `dom phi`. It is reflexive because `S`
  is, symmetric because `S` is, and transitive because `S` is transitive and
  `phi` is a function.
- It is Borel, since `S`, `phi` and `dom phi` are Borel.
- `D_phi(S)` is Borel and `S_phi`-invariant:
  `x ∈ D_phi(S)` iff for every `N` there are `N` distinct indices `n` with
  `(x, g_n x) ∈ S_phi`. The points `g_n x` are distinct by freeness.
- `phi` carries `S_phi` onto `phi(S) ∩ S` on `ran phi`. So `D_phi(S)` is where
  `phi(S|dom phi) ∩ S` has infinite classes, transported back by `phi`.

An **infinite-contact step** from `S` adds `phi|D_phi(S)` to `S`.

## 1. Lemma 0: infinite-contact steps are free

This is the positive half. It shows that the class of approaches killed below
is a genuine repair method: it contains wq-normal absorption, normalizers,
commensurators and the window trick.

**Import** (Gaboriau, lecture notes on measure equivalence, cost and
L2-Betti numbers, Exercise 1.17 (i)=>(iii), as quoted in
`fpbs-wq-normal-price-one-subgroup-forces-price-one-proof`): "if almost every
class of a standard p.m.p. equivalence relation is infinite, then for every
`eps > 0` there is a complete section of measure at most `eps`."

**Lemma 0.** Let `S ⊆ E_a` be a Borel subrelation, `phi ∈ [[E_a]]` and
`D = D_phi(S)`. For every `eps > 0` there is a Borel `A ⊆ D` with
`mu(A) <= eps` such that the relation generated by `S` and `phi|A` contains the
graph of `phi|D`. Hence `relC(<S, phi|D> | S) = 0`.

The same holds for countably many `phi_k`, using `eps/2^k`, and along a
transfinite chain of countable length, since the set of all partial maps used
is countable.

*Proof.*
- `S_phi|D` is a Borel equivalence relation on `D` with infinite classes. It
  is a subrelation of `E_a`, so every element of its pseudogroup preserves
  `mu`, and it is p.m.p.
- By the import there is a Borel complete section `A ⊆ D` of `S_phi|D` with
  `mu(A) <= eps`.
- For `x ∈ D` choose `y ∈ A` with `(x, y) ∈ S_phi`. Then `x S y`,
  `y (phi|A) phi y` and `phi y S phi x`, the last because `(x, y) ∈ S_phi`.
  So `(x, phi x)` lies in the generated relation.
- For a chain, argue by induction on `beta`. Every `S_beta` lies in the
  relation generated by `S_0` and all the chosen `phi_k|A_k`, because the
  successor argument uses only `S_beta`-edges, which are available by the
  induction hypothesis. ∎

## 2. Theorem A: the label of a contact is in `Q(Lambda)`

**Theorem A.** Let `Lambda <= Gamma` and let `S ⊆ E_{a|Lambda}` be a Borel
subrelation. Let `phi ∈ [[E_a]]` have label `gamma`. Then

```text
gamma(x) ∈ Q(Lambda)   for mu-almost every x ∈ D_phi(S).
```

**Step 1 (coset cocycle).** Define the Borel map
`c : dom phi -> Lambda\Gamma` by `c(x) = Lambda gamma(x)`. If `(x, y) ∈ S_phi`
with `y = h x` and `h ∈ Lambda`, then `c(y) = c(x) h^{-1}`.

*Proof.*
- Since `S ⊆ E_{a|Lambda}`, the element `h ∈ Lambda` with `y = h x` exists, and
  it is unique by freeness.
- Since `(phi x, phi y) ∈ S ⊆ E_{a|Lambda}`, there is `h' ∈ Lambda` with
  `phi y = h' phi x`. That is, `gamma(y) h x = h' gamma(x) x`.
- By freeness `gamma(y) h = h' gamma(x)`, so
  `Lambda gamma(y) = Lambda gamma(x) h^{-1}`. ∎

**Step 2 (invariant set).** `B = {x ∈ dom phi : gamma(x) ∉ Q(Lambda)}` is Borel
and `S_phi`-invariant.

*Proof.* By Step 1, `S_phi`-related points have labels in the same double coset
`Lambda gamma(x) Lambda`. Apply Fact 0.1. ∎

**Step 3 (bounded fibres).** Let `x ∈ B` and let `C ∈ Lambda\Gamma`. The
`S_phi`-class of `x` contains at most `|I_Lambda(gamma(x))| < ∞` points `y`
with `c(y) = C`.

*Proof.*
- Let `y_1 = h_1 x` and `y_2 = h_2 x` be in the class with `c(y_1) = c(y_2)`,
  where `h_i ∈ Lambda`.
- By Step 1, `Lambda gamma(x) h_1^{-1} = Lambda gamma(x) h_2^{-1}`. So
  `gamma(x) h_1^{-1} h_2 gamma(x)^{-1} ∈ Lambda`.
- Also `h_1^{-1} h_2 ∈ Lambda`. Hence
  `h_1^{-1} h_2 ∈ Lambda ∩ gamma(x)^{-1} Lambda gamma(x) = I_Lambda(gamma(x))`.
- Fix `y_1`. Then `y_2 = h_1 i x` for some `i ∈ I_Lambda(gamma(x))`, and there
  are at most `|I_Lambda(gamma(x))|` such points. This set is finite because
  `x ∈ B`. ∎

**Step 4 (null-set lemma).** Let `T` be a Borel equivalence relation on a Borel
set `Y ⊆ X`, with `T ⊆ E_a` and every class of `T` infinite. If a Borel
`Z ⊆ Y` meets every `T`-class in finitely many points, then `mu(Z) = 0`.

*Proof.*
- Fix a Borel injection `iota : X -> R`, which exists because `X` is standard
  Borel.
- For each `j >= 1`, let `Z_j` be the set of `z ∈ Z` that are exactly the
  `j`-th smallest point of `[z]_T ∩ Z` under `iota`. This set is Borel. `z ∈ Z_j`
  iff exactly `j - 1` indices `n` have `g_n z ∈ Z`, `(z, g_n z) ∈ T` and
  `iota(g_n z) < iota(z)`. Distinct indices give distinct points by freeness.
- `Z = ∪_j Z_j`, and each `Z_j` meets each class in at most one point. So it is
  enough to treat a Borel `Z'` meeting each class at most once.
- For `z ∈ Z'` and `m >= 1`, let `n_m(z)` be the `m`-th index `n` with
  `(z, g_n z) ∈ T`. It exists because the class is infinite. Put
  `psi_m(z) = g_{n_m(z)} z`. Each `psi_m` is Borel and piecewise a translate
  `a(g_n)` on the Borel pieces `{n_m = n}`.
- `psi_m` is injective on `Z'`. The pieces are disjoint and `psi_m(z)` lies in
  the class of `z`, which meets `Z'` only at `z`; two different points of `Z'`
  lie in different classes. So `mu(psi_m(Z')) = mu(Z')`.
- For `m != m'`, `psi_m(Z')` and `psi_{m'}(Z')` are disjoint. Points coming from
  different `z` lie in different classes. For the same `z`,
  `n_m(z) != n_{m'}(z)`, and freeness gives `g_{n_m(z)} z != g_{n_{m'}(z)} z`.
- So `sum_m mu(Z') <= 1`, and `mu(Z') = 0`. ∎

**Step 5 (conclusion).**
- Put `Y = B ∩ D_phi(S)`. It is Borel and `S_phi`-invariant by Step 2 and §0,
  and `T = S_phi|Y` has infinite classes.
- For each of the countably many cosets `C ∈ Lambda\Gamma`, the Borel set
  `Y_C = Y ∩ c^{-1}(C)` meets every `T`-class in finitely many points by
  Step 3. So `mu(Y_C) = 0` by Step 4.
- `Y = ∪_C Y_C` is null. This is the statement of Theorem A. ∎

**Remark (no hypothesis on `S` beyond `S ⊆ E_{a|Lambda}`).** `S` need not be
ergodic, aperiodic, generated by group elements or of finite cost. The label
`gamma` is an arbitrary Borel map. `Lambda` need not be finitely generated.

## 3. Corollary B: the cap is the hull, and it is attained

**Definition (infinite-contact chain).** A family `(S_beta)_{beta <= alpha}` of
Borel subrelations of `E_a`, for a countable ordinal `alpha`, such that:
- `S_{beta+1}` is generated by `S_beta` and `phi_{beta,k}|D_{phi_{beta,k}}(S_beta)`
  for countably many `phi_{beta,k} ∈ [[E_a]]`;
- `S_lambda = ∪_{beta < lambda} S_beta` at limits.

The **infinite-contact closure** of `S_0` is the union of all such chains
starting at `S_0`. Up to null sets it is the smallest Borel subrelation
`S* ⊇ S_0` with `phi|D_phi(S*) ∈ [[S*]]` for every `phi`. By Lemma 0 every step
of a chain is free, so `relC(S_alpha | S_0) = 0` for every chain.

**Corollary B.** Let `Lambda <= Gamma` be infinite, with wq-normal hull `W(Lambda)`
as in `fpbs-wq-normal-hull-is-almost-malnormal`, and let `S_0 ⊆ E_{a|Lambda}`
be a Borel subrelation.
1. **(Cap.)** Every infinite-contact chain from `S_0` satisfies
   `S_beta ⊆ E_{a|W(Lambda)}` modulo null sets, for all `beta`.
2. **(Closure.)** `E_{a|M}` is infinite-contact closed for every infinite
   almost malnormal `M`. For every `phi ∈ [[E_a]]`, `phi|D_phi(E_{a|M})` already
   lies in `[[E_{a|M}]]`.
3. **(Attained.)** If `S_0 = E_{a|Lambda}`, there is a chain with
   `S_alpha = E_{a|W(Lambda)}`. So the infinite-contact closure of `E_{a|Lambda}`
   is exactly `E_{a|W(Lambda)}`, for every free action `a`.

*Proof.*
- **Setting.** Put `M = W(Lambda)`. By item 2 of the hull claim `M` is almost
  malnormal, and it contains `Lambda`, so it is infinite. By Fact 0.2,
  `Q(M) = M`.
- **Item 2.** Let `S ⊆ E_{a|M}` be Borel and `phi ∈ [[E_a]]`. By Theorem A with
  `Lambda := M`, the label of `phi` lies in `M` almost everywhere on
  `D_phi(S)`. So `phi|D_phi(S)` has graph in `E_{a|M}` modulo a null set.
- **Item 1.** Argue by induction on `beta`, applying item 2 at successors.
  - `S_0 ⊆ E_{a|Lambda} ⊆ E_{a|M}`.
  - If `S_beta ⊆ E_{a|M}`, each added `phi_{beta,k}|D` is in `[[E_{a|M}]]` a.e.
    The generated relation is contained in the equivalence relation `E_{a|M}`.
  - Limits are countable unions.
- **Item 3.** Use the hull chain `(W_beta)` of
  `fpbs-wq-normal-hull-is-almost-malnormal`, and put `S_beta = E_{a|W_beta}`.
  - At a successor, enumerate the countable set
    `{g : g W_beta g^{-1} ∩ W_beta infinite}` as `g_k`, and let `phi_k = a(g_k)`
    on `X`.
  - The contact relation `(S_beta)_{phi_k}` contains
    `{(x, sigma x) : sigma ∈ W_beta ∩ g_k^{-1} W_beta g_k}`.
    - For such `sigma`, `(x, sigma x) ∈ E_{a|W_beta}`.
    - Also `phi_k sigma x = (g_k sigma g_k^{-1}) phi_k x` with
      `g_k sigma g_k^{-1} ∈ W_beta`.
  - This subgroup is `g_k^{-1}(g_k W_beta g_k^{-1} ∩ W_beta) g_k`, which is
    infinite. By freeness every class is infinite, so `D_{phi_k}(S_beta) = X`.
  - `S_beta` together with all `a(g_k)` generates `E_{a|W_{beta+1}}`.
  - Limits match unions. ∎

**Corollary C (special cases killed).** Let `M` be infinite and almost
malnormal, and let `S ⊆ E_{a|M}` be Borel.
- **Normalizers.** If `phi ∈ [E_a]` (full group, `dom phi = X`) normalizes an
  aperiodic `S`, that is `phi(S) = S`, then `S_phi = S`. So `D_phi(S) = X` and
  `phi ∈ [E_{a|M}]`. In particular `N_{[E_a]}(E_{a|M}) = [E_{a|M}]`. The same
  holds for partial normalizers `phi ∈ [[E_a]]` with
  `phi(S|dom phi) = S|ran phi` and `S|dom phi` aperiodic.
- **Window trick.** If `phi(S|dom phi) ∩ S` is ergodic on a non-null set
  `ran phi`, with `mu` non-atomic, its classes are infinite a.e. Then
  `phi ∈ [[E_{a|M}]]`. So the Gaboriau--Tucker-Drob weak-normality condition
  never enlarges `E_{a|M}`.
- **Quasi-normalizers.** Suppose `phi(S) ∩ S` has finite index in `S|ran phi`
  on a set where `S` is aperiodic. Then `S_phi` has infinite classes there,
  and the same conclusion holds.

This is the orbit-equivalence analogue of Popa's fact that the quasi-normalizer
of `L(M)` in `L(Gamma)` is `L(M)` for almost malnormal `M`. Nothing from that
theory is used.

## 4. Proposition E: finite cost means vanishing stage relative cost

**Proposition E.** Let `Gamma = ∪_n M_n` be an increasing union of finitely
generated subgroups, where `M_n` has `d_n` generators, and let `a` be a free
p.m.p. action. The quantity `rho_n = relC(E_a | E_{a|M_n})` is non-increasing
in `n`, and the following are equivalent:
- (i) `C(a) < ∞`;
- (ii) `rho_n < ∞` for some `n`;
- (iii) `rho_n -> 0`.

*Proof.*
- **Monotone.** A graphing that repairs `E_{a|M_n}` also repairs the larger
  `E_{a|M_{n+1}}`.
- **(iii) => (ii).** Trivial.
- **(ii) => (i).** The `d_n` generators, as maps on `X`, form a graphing of
  `E_{a|M_n}` of cost `d_n`. Adding a repairing graphing of cost `<= rho_n + 1`
  generates `E_a`, so `C(a) <= d_n + rho_n + 1`.
- **(i) => (iii).** Let `Phi = (phi_i)` be a generating graphing of cost `K < ∞`.
  - Split each `phi_i` along its label into pieces `phi_{i,g} = phi_i|{gamma_i = g}`.
    The family of all pieces still generates `E_a` and has total cost `K`.
  - Let `Phi_n^out` be the pieces with `g ∉ M_n`. The other pieces have graph in
    `E_{a|M_n}`, so `E_{a|M_n}` and `Phi_n^out` generate `E_a`.
  - Hence `rho_n <= sum_{i, g ∉ M_n} mu(dom phi_{i,g})`. This tends to 0 by
    dominated convergence, because `M_n` increases to `Gamma` and the double
    sum is finite. ∎

## 5. The obstruction for the hole

Let `Gamma` be locally free with `c* < ∞`, in the malnormally exhausted class of
`fpbs-locally-free-malnormally-exhausted-finite-cost`. No finitely generated
`H` has `W(H) = Gamma`. Take a compressed exhaustion by finitely generated
`H_n`, and put `M_n = W(H_n)`, a proper almost malnormal subgroup. Fix any free
action `a`.

**Invariant.** The almost malnormal hull `W(H_n)`, equivalently the label set
`Q(M_n) = M_n`.

**Step at which the class dies.** A successor step of an infinite-contact chain
(Lemma 0 steps: normalizers, partial normalizers, quasi-normalizers,
commensurating group elements, window-trick partial maps, wq-normal absorption)
whose added map has label outside `M_n` on a non-null set. By Theorem A, such
a map has finite contact almost everywhere where its label leaves `M_n`. So
Lemma 0 does not apply, and the chain cannot leave `E_{a|M_n}` (Corollary B).

**Consequence.**
- By Proposition E, `C(a) < ∞` iff `relC(E_a | E_{a|H_n}) -> 0`.
- Any repairing graphing `Phi_n` for `E_{a|H_n}`, presented as a chain, has a
  first step leaving `E_{a|M_n}`. That step consists of partial maps whose
  labels lie outside `M_n` on a non-null set, and which have finite contact
  with the current relation there. So they are not free by Lemma 0, and their
  cost has to be paid.
- A finite-cost proof must make these finite-contact payments tend to 0 in
  total as `n -> ∞`, which zero-cost absorption cannot supply.
- This holds even if the added partial maps use arbitrary measurable labels.
  This closes the loophole left by the group-element statement
  `fpbs-wq-normal-subgroup-cost-transfer` ("reaches exactly `W(H)`").

**What is NOT killed.**
1. **Mixed chains.** After one paid finite-contact step `psi`, the relation
   `S' = <E_{a|M_n}, psi>` is no longer inside a subgroup orbit relation, and
   Theorem A says nothing about later infinite-contact steps from `S'`. Wave 4's
   certificate counts (`experiments/locally-free-finite-cost-2026-09-17/`)
   concern exactly this regime for `Gamma_mal`. The question is whether a sparse
   `psi = b|A` can create infinite contact for `b` with `S'`.
2. **Paid repairs of summable mass that never create contact**, for example
   percolation-style repairs as in `fpbs-infinite-contact-zero-relative-cost`
   §6--7, where contact is not necessary.
3. **Methods not presented as chains from a subgroup relation**, such as weak
   containment or auxiliary cost-invariance.

Theorem A gives no lower bound on `relC(E_a | E_{a|M_n})`. Whether this
relative cost is positive for a single stage of `Gamma_mal` (for example
`M = <a, b a b^{-2}> <= F_2 = <a, b>`, a malnormal rank-2 subgroup of infinite
index) remains open. By contrast, for the non-malnormal `<a, b^2> <= F_2` it is
0 by Corollary B item 3.
