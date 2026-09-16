# Infinite centralizers force fixed price one; the torsion-quotient case reduces to faithful just-infinite quotients (2026-09-16)

Written proofs by the lane `swarm-fpbs-bounded-cost-fg-torsion-q`. They are
not formally verified. Nodes:

- Section 2: `fpbs-finite-normal-quotient-lifts-price-one` (Lemma A).
- Section 3: Lemma B, used inline by the route of Section 5.
- Section 4: `fpbs-infinite-centralizer-forces-price-one` (Theorem C).
- Section 5: the route `fpbs-bounded-cost-fg-torsion-via-just-infinite-reduction`
  from `fpbs-bounded-cost-just-infinite-faithful-price-one` (statement O) to
  `fpbs-bounded-cost-fg-torsion-quotient-price-one`.

Imported inputs, all ESTABLISHED in the graph on 2026-09-16:

- **[IND]** `fpbs-normalized-cost-induction-input`: for a p.m.p. countable
  Borel equivalence relation `R` on `(X, mu)` with `mu(X) = 1` and a Borel
  complete section `Y`, `C(R) - 1 = mu(Y) (C_(mu_Y)(R|Y) - 1)`, where
  `mu_Y = mu|Y / mu(Y)`.
- **[KHE]** `fpbs-khezeli-products-have-fixed-price-one`: the product of two
  infinite countable groups has fixed price one (arXiv:2509.08325). The graph
  status records an imported theorem.
- **[WQ]** `fpbs-wq-normal-price-one-subgroup-forces-price-one`: an infinite
  wq-normal subgroup with fixed price one forces fixed price one, and so does
  an infinite amenable wq-normal subgroup.

## 1. Conventions

- Groups are countable. Actions are Borel actions on standard Borel
  probability spaces preserving the measure. An essentially free action
  becomes free after discarding an invariant null set, which changes no cost,
  so actions below are free.
- For `L <= Gamma` and an action of `Gamma` on `X`, `R_L` is the orbit
  relation of the restricted action. `C(R)` is the cost.
- `Gamma` has **fixed price one** if every essentially free p.m.p. action of
  `Gamma` has cost one. A finite group of order `n` has fixed price `1 - 1/n`,
  so a group with fixed price one is infinite.
- A group `N` satisfies **(H_K)** if every essentially free p.m.p. action of
  `N`, ergodic or not, has cost at most `K`.
- For `N ◁ Gamma` write `pi : Gamma -> Q = Gamma/N`,
  `rho : Q -> Out(N)` for the outer action and `Q_0 = ker rho` for the outer
  kernel. `C_Gamma(N)` is the centralizer and `Z(N)` the center.

**Fact 1.1.** `C_Gamma(N)` is normal in `Gamma`, `C_Gamma(N) ∩ N = Z(N)` and
`pi(C_Gamma(N)) = Q_0`. Hence `Q_0 ≅ C_Gamma(N)/Z(N)`.

*Proof.* `gamma C_Gamma(N) gamma^-1 = C_Gamma(gamma N gamma^-1) = C_Gamma(N)`.
The intersection is `Z(N)` by definition. If `c in C_Gamma(N)`, conjugation by
`c` is trivial on `N`, so `pi(c) in Q_0`. Conversely, if `pi(gamma) in Q_0`,
there is `a in N` with `gamma u gamma^-1 = a u a^-1` for all `u in N`. Then
`a^-1 gamma in C_Gamma(N)` and `pi(a^-1 gamma) = pi(gamma)`. □

**Fact 1.2.** If `M ◁ Gamma` is infinite and `M <= Lambda <= Gamma`, then
`Lambda` is wq-normal in `Gamma`. In particular an infinite normal subgroup is
wq-normal.

*Proof.* This is fact (i) of `fpbs-amenable-outer-kernel-forces-price-one-proof`.
For every proper subgroup `K ⊇ Lambda` and every `g notin K`,
`g K g^-1 ∩ K ⊇ M`, which is infinite. □

## 2. Lemma A: fixed price one lifts across a finite normal kernel

**Lemma A.** Let `F ◁ Gamma` be finite and `Q = Gamma/F`. For every free p.m.p.
action of `Gamma` on `(X, mu)` there is a free p.m.p. action of `Q` on a
standard probability space `(D, mu_D)` with

    C(R_Gamma) - 1 = (C(R_Q on D) - 1) / |F|.

Consequently, if `Gamma/F` has fixed price one, then `Gamma` has fixed price
one.

This direction is the one that is needed below. The other direction
(`Gamma` fixed price one implies `Gamma/F` fixed price one) is not used and is
not claimed.

*Proof.* Let `Gamma` act freely on `(X, mu)`, and write `q = gamma F`.

1. **A Borel fundamental domain for `F`.**
   - Fix a Borel injection `tau : X -> R`. It exists since `X` is standard.
   - Put `D = {x in X : tau(x) < tau(f x) for all f in F \ {e}}`. It is Borel.
   - `F` acts freely, so `F x` has `|F|` points with distinct `tau`-values.
     `D ∩ F x` is exactly the point where `tau` is least.
   - So `X` is the disjoint union of the sets `f D`, `f in F`. Indeed, if
     `f x = f' x'` with `x, x' in D`, then `x' in F x`, so `x = x'` and `f = f'`
     by freeness.
   - `mu` is `F`-invariant, so `mu(D) = 1/|F|`. Put `mu_D = |F| mu|D`.
   - Let `r : X -> D` send `x` to the unique point of `D ∩ F x`. It is Borel:
     `r(x) = f x` on the Borel set `{x : f x in D}`, for each of the finitely
     many `f in F`.
2. **The action of `Q` on `D`.**
   - For `q = gamma F` and `x in D` put `q . x = r(gamma x)`.
   - *Well defined.* For `f in F`, `gamma f x = (gamma f gamma^-1) gamma x`
     lies in `F gamma x`, since `F` is normal, and `r` is constant on
     `F`-orbits.
   - *Action.* `e . x = r(x) = x` for `x in D`. If `q' = gamma' F`, then
     `r(gamma' x) = f gamma' x` for some `f in F`, and
     `gamma f gamma' x in F gamma gamma' x`. So
     `q . (q' . x) = r(gamma gamma' x) = (q q') . x`.
   - Each map `x -> q . x` is Borel.
3. **`Q` preserves `mu_D`.**
   - Fix `q = gamma F`. For `f in F` let `D_f = {x in D : f gamma x in D}`.
     These sets are Borel and partition `D`: for `x in D` exactly one point of
     `F gamma x` lies in `D`, and freeness makes the corresponding `f` unique.
   - On `D_f`, `q . x = f gamma x`.
   - `q .` is injective on `D`. If `r(gamma x) = r(gamma x')`, then `gamma x'`
     lies in `F gamma x = gamma F x`, so `x' in F x`, and `x = x'` since both
     lie in `D`.
   - Hence for Borel `B ⊆ D` the sets `f gamma (B ∩ D_f)` are pairwise
     disjoint and `mu(q . B) = sum_f mu(f gamma(B ∩ D_f)) = sum_f mu(B ∩ D_f) = mu(B)`.
   - `q^-1 .` is the inverse map, so each `q .` is a measure-preserving Borel
     bijection of `(D, mu_D)`.
4. **Freeness.** If `q . x = x`, then `f gamma x = x` for some `f in F`. The
   action of `Gamma` is free, so `f gamma = e`, `gamma in F` and `q = e`.
5. **Orbit relation.** The orbit relation of `Q` on `D` is `R_Gamma|D`.
   - If `y = q . x`, then `y = f gamma x` is in `Gamma x`.
   - Conversely, let `x, y in D` with `y = gamma x`. Then `y` is the point of
     `D` in `F gamma x`, so `y = r(gamma x) = q . x` with `q = gamma F`.
6. **Cost.** `D` meets every `F`-orbit, so it is a complete section of
   `R_Gamma`. By [IND], with `mu_D = mu|D / mu(D)`,

       C(R_Gamma) - 1 = mu(D) (C_(mu_D)(R_Gamma|D) - 1) = (C(R_Q on D) - 1) / |F|.

7. **Consequence.** Suppose `Q` has fixed price one. The action of step 2 is a
   free p.m.p. action of `Q` on the standard probability space `(D, mu_D)`,
   so its cost is one. By step 6, `C(R_Gamma) = 1`. The action of `Gamma` was
   arbitrary, so `Gamma` has fixed price one. □

## 3. Lemma B: an infinite normal subgroup bounds the cost of the whole action

**Lemma B.0 (small complete sections).** Let an infinite group `N` act freely
on `(X, mu)`, preserving `mu`. For every `delta > 0` there is a Borel set
`A ⊆ X` with `mu(A) <= delta` that meets every `N`-orbit.

This is Exercise 1.17 (i)=>(iii) of Gaboriau's lecture notes, as already used
in `fpbs-wq-normal-price-one-subgroup-forces-price-one-proof`. A direct proof
for free actions follows.

*Proof.*
1. Choose `F ⊆ N` with `|F| = m >= 1/delta`. Let
   `S = {f^-1 f' : f, f' in F, f != f'}`. It is finite, symmetric and does not
   contain `e`. A set `A` satisfies `s A ∩ A = ∅` for all `s in S` iff the
   translates `f A`, `f in F`, are pairwise disjoint. Call such `A`
   *independent*. Then `m mu(A) <= 1`.
2. **A countable Borel colouring.** Fix a countable family `(B_k)` of Borel
   sets that separates points and is closed under complements. For `x in X`
   and `s in S`, `x != s x` by freeness, so
   `k_s(x) = min{k : x in B_k, s x notin B_k}` exists. Put
   `c(x) = (k_s(x))_(s in S)`. It takes countably many values and is Borel. If
   `y = s x` with `s in S`, then `c(x) != c(y)`: with `k = k_s(x)` we have
   `y notin B_k`, while `k_s(y) = k` would force `y in B_k`.
3. **Greedy maximal independent set.** Enumerate the colours `c_0, c_1, ...`.
   Let `A_0 = ∅` and
   `A_(j+1) = A_j ∪ {x : c(x) = c_j and x notin S A_j}`, where
   `S A_j = ∪_(s in S) s A_j` is Borel.
   - Each `A_(j+1)` is independent. New points have the same colour, so no two
     of them differ by an element of `S`, and none lies in `S A_j`.
   - So `A = ∪_j A_j` is Borel and independent, and `mu(A) <= 1/m <= delta`.
   - If `x notin A` has colour `c_j`, then `x in S A_j`, since otherwise
     `x in A_(j+1)`. So `X = A ∪ S A ⊆ N A`, and `A` meets every `N`-orbit. □

**Lemma B.** Let `N ◁ Lambda` be infinite, and let `Lambda` act freely on
`(X, mu)`, preserving `mu`. Then `C(R_Lambda) <= C(R_N)`. Consequently, if `N`
satisfies (H_K), so does `Lambda`.

*Proof.*
1. Assume `C(R_N) < infinity` and fix `eps > 0`. Let `Phi` be a graphing of
   `R_N` with cost at most `C(R_N) + eps`.
2. Let `(gamma_j)_(j >= 1)` list a set of representatives of the cosets of `N`
   in `Lambda`. For each `j`, Lemma B.0 gives a Borel set `A_j` meeting every
   `N`-orbit, with `mu(A_j) <= eps 2^-j`.
3. Let `Psi` be `Phi` together with the partial maps `gamma_j` restricted to
   `A_j`. Its cost is at most `C(R_N) + 2 eps`, and it generates a
   subrelation of `R_Lambda`.
4. **`Psi` generates `R_Lambda`.** Let `y = lambda x` with `lambda in Lambda`.
   - Write `lambda = gamma_j v` with `v in N`.
   - Pick `w in N` with `w x in A_j`.
   - Then `y = u gamma_j (w x)` with `u = gamma_j v w^-1 gamma_j^-1`, and
     `u in N` since `N` is normal.
   - So `x` and `w x` are joined by `Phi`, `w x` and `gamma_j w x` by
     `gamma_j|A_j`, and `gamma_j w x` and `y` by `Phi`.
5. So `C(R_Lambda) <= C(R_N) + 2 eps` for every `eps > 0`.
6. **Consequence.** A free p.m.p. action of `Lambda` restricts to a free p.m.p.
   action of `N`. Under (H_K) its cost is at most `K`, so
   `C(R_Lambda) <= K`. □

**Literature.** Lemma B is the action-wise form of Gaboriau's
*Critères VI.24 (2) (Sous-groupe normal)*, in D. Gaboriau, *Coût des relations
d'équivalence et des groupes*, Invent. Math. 139 (2000). Its hypothesis is an
infinite normal subgroup with fixed price, and it compares the costs of the two
groups. See also *Théorème 3* of the introduction. The PDF
<https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/Cout/Cout.pdf> was fetched
on 2026-09-16. A raw text extraction lost the mathematical symbols, so the
exact inequality in the source is not quoted here. The text does say that the
criteria are proved "de la même façon" as Proposition VI.23: a Borel set of
small measure meeting all orbits of the subgroup carries the extra
generators. That is the argument above. The graph does not rely on the
citation, since the proof above is complete given Lemma B.0.

## 4. Theorem C: commuting infinite normal subgroups force fixed price one

**Theorem C.** Let `N` and `M` be infinite normal subgroups of a countable
group `Gamma` with `[N, M] = 1`. Then `Gamma` has fixed price one. No cost
hypothesis is needed.

*Proof.* Put `Z = N ∩ M` and `L = N M`.

1. **`Z` is abelian and normal in `Gamma`.** It is an intersection of normal
   subgroups. Elements of `Z ⊆ N` commute with elements of `Z ⊆ M`.
2. **Case `Z` infinite.** `Z` is an infinite amenable normal subgroup, hence
   wq-normal by Fact 1.2. [WQ] gives `Gamma` fixed price one.
3. **Case `Z` finite: `L/Z` is a direct product.**
   - `L` is a subgroup since `N` and `M` commute, and it is normal in
     `Gamma`.
   - `N/Z` and `M/Z` are normal subgroups of `L/Z` that commute and generate
     `L/Z`.
   - `(N/Z) ∩ (M/Z) = (N ∩ M)/Z` is trivial, by the correspondence theorem,
     since both contain `Z`.
   - So multiplication `N/Z x M/Z -> L/Z` is an isomorphism.
   - `N/Z` and `M/Z` are infinite, since `Z` is finite.
4. **`L/Z` has fixed price one.** This is [KHE].
5. **`L` has fixed price one.** `Z` is a finite normal subgroup of `L`, and
   Lemma A applies.
6. **`Gamma` has fixed price one.** `L ⊇ N` is an infinite normal subgroup of
   `Gamma`, so it is wq-normal by Fact 1.2, and [WQ] lifts fixed price one from
   `L` to `Gamma`. □

**Corollary C.1.** Let `N ◁ Gamma` be infinite. If `C_Gamma(N)` is infinite,
then `Gamma` has fixed price one. In particular this holds if `Z(N)` is
infinite, or if the outer kernel `Q_0 = ker(Gamma/N -> Out(N))` is infinite.

*Proof.* By Fact 1.1, `M = C_Gamma(N)` is normal in `Gamma` and commutes with
`N`. Theorem C applies. `Z(N) ⊆ C_Gamma(N)`, and `Q_0 = pi(C_Gamma(N))` is a
quotient of `C_Gamma(N)`. □

The two statements are equivalent: if `N` and `M` commute, `M ⊆ C_Gamma(N)`.

**Corollary C.2 (commuting modulo a finite subgroup).** Let `N` and `M` be
infinite normal subgroups of a countable group `Gamma` such that `[N, M]` is
finite. Then `Gamma` has fixed price one. More generally, if some finite
`F ◁ Gamma` has `C_{Gamma/F}(NF/F)` infinite for an infinite `N ◁ Gamma`, then
`Gamma` has fixed price one.

*Proof.*
1. **`F = [N, M]` is normal.** It is generated by the commutators `[n, m]` with
   `n in N`, `m in M`. For `gamma in Gamma`,
   `gamma [n, m] gamma^-1 = [gamma n gamma^-1, gamma m gamma^-1]` is again such
   a commutator, since `N` and `M` are normal.
2. **The images commute.** Let `p : Gamma -> Gamma/F`. Then `p(N)` and `p(M)`
   are normal in `Gamma/F`, and `[p(n), p(m)] = p([n, m]) = 1`.
3. **The images are infinite.** `p(N) ≅ N/(N ∩ F)` and `N ∩ F` is finite.
   Likewise for `M`.
4. **Conclusion.** Theorem C gives `Gamma/F` fixed price one, and Lemma A lifts
   it to `Gamma` across the finite kernel `F`.

For the general form, apply Corollary C.1 to `NF/F ◁ Gamma/F`, which is
infinite, and then Lemma A. □

**Remarks.**
- **Relation to `fpbs-amenable-outer-kernel-forces-price-one`.** That lemma
  needs an infinite amenable subgroup of `Q_0`. Corollary C.1 needs only that
  `Q_0` is infinite. So Case 0 of
  `fpbs-bounded-cost-normal-via-quotient-trichotomy` extends to every infinite
  outer kernel.
- **The dead "commuting part" attempt.** The attempt recorded on
  `fpbs-bounded-cost-fg-torsion-quotient-price-one` stopped at the passage
  from `N x C` to its quotient by a finite central subgroup. That passage, from
  a group to its quotient, is avoided here. One passes instead to `L/Z`, which
  is itself a direct product, and lifts from `L/Z` to `L` across the finite
  kernel `Z`. Lemma A handles that direction.
- **Literature.** No statement of Theorem C was found in the repo or in
  arXiv:2509.08325 (read 2026-09-16). It is a short consequence of Khezeli's
  theorem, and no novelty is claimed beyond the written proof. The intro of
  arXiv:2509.08325 lists "groups with an infinite normal subgroup" among
  classes with fixed price one. Read literally, that cannot be right, since
  free groups have infinite normal subgroups. It is not relied upon.

## 5. Theorem D: reduction to faithful just-infinite quotients

**Statement O** (`fpbs-bounded-cost-just-infinite-faithful-price-one`). Let
`N ◁ Gamma` be infinite and satisfy (H_K) for some `K < infinity`. Suppose
`Q = Gamma/N` is infinite, finitely generated, torsion and just-infinite, and
`C_Gamma(N)` is finite and contained in `N`. Then `Gamma` has fixed price one.

In O, `Q_0 = pi(C_Gamma(N)) = 1`, so the outer action is faithful, and
`Z(N) = C_Gamma(N)` is finite.

**Statement T''.** Let `N ◁ Gamma` be infinite and satisfy (H_K). Suppose
`Q = Gamma/N` is infinite, finitely generated and torsion. Then `Gamma` has
fixed price one. There is no condition on the outer kernel.

**Theorem D.** Statement O implies T''. Hence O implies the target
`fpbs-bounded-cost-fg-torsion-quotient-price-one` (T'). Conversely
`O ⇐ T' ⇐ T''` trivially, so O, T' and T'' are equivalent given Lemma B and
Corollary C.1.

**Lemma D.1.** Every infinite finitely generated group `Q` has a normal
subgroup `P` such that `Q/P` is just-infinite: infinite, with every nontrivial
normal subgroup of finite index.

*Proof.* Let `𝒫` be the set of normal subgroups of `Q` of infinite index,
ordered by inclusion. It contains `{e}`.
- **Chains have upper bounds.** Let `(P_i)` be a chain and `U = ∪ P_i`, a
  normal subgroup. If `U` had finite index, it would be finitely generated,
  since finite-index subgroups of finitely generated groups are. Its finitely
  many generators would lie in one `P_i`, so `U = P_i`, which has infinite
  index. So `U in 𝒫`.
- **A maximal element.** By Zorn's lemma `𝒫` has a maximal element `P`.
  `Q/P` is infinite. A nontrivial normal subgroup of `Q/P` is `R/P` with
  `R ◁ Q` and `R ⊋ P`. Maximality gives `R notin 𝒫`, so `R/P` has finite
  index. □

**Lemma D.2.** An infinite just-infinite group has no nontrivial finite normal
subgroup: such a subgroup would have finite index and be finite.

*Proof of Theorem D.* Let `N ◁ Gamma`, `K` and `Q` be as in T''.

1. **Choose a just-infinite quotient.** By Lemma D.1 pick `P ◁ Q` with `Q/P`
   just-infinite. `Q/P` is finitely generated and torsion.
2. **Enlarge the normal subgroup.** Put `N_1 = pi^-1(P)`.
   - `N_1 ◁ Gamma`, `N ⊆ N_1`, and `Gamma/N_1 ≅ Q/P`.
   - `N` is an infinite normal subgroup of `N_1`, so `N_1` satisfies (H_K) by
     Lemma B.
3. **Infinite centralizer.** If `C_Gamma(N_1)` is infinite, Corollary C.1
   gives `Gamma` fixed price one.
4. **Finite centralizer.** Otherwise `C_Gamma(N_1)` is finite and normal in
   `Gamma` by Fact 1.1. Its image in `Gamma/N_1 ≅ Q/P` is a finite normal
   subgroup of a just-infinite group, hence trivial by Lemma D.2. So
   `C_Gamma(N_1) ⊆ N_1`.
5. **Apply O.** `(Gamma, N_1)` satisfies every hypothesis of O, so `Gamma` has
   fixed price one.

**Converse.** Under the hypotheses of O, `Q_0 = 1` contains no infinite
amenable subgroup, so O is a special case of T'. And T' is a special case of
T''. □

**What the reduction removes and what it does not.**
- The outer-kernel hypothesis of T' is not needed. Every infinite outer kernel
  is handled by Corollary C.1, with no cost hypothesis.
- The remaining statement O has a faithful outer action of a just-infinite
  finitely generated torsion group on `N`, and finite `Z(N)`.
- By Corollary C.2, a proof of O may also assume that `C_{Gamma/F}(NF/F)` is
  finite for every finite `F ◁ Gamma`.
- **Burnside.** For the split `B(m,n) = N ⋊ B(m-1,n)` of
  `fpbs-burnside-upper-cost-one-via-fg-torsion-quotient`, step 3 never
  applies. `C_Gamma(N_1) ⊆ C_Gamma(x_1)`, which is finite cyclic by
  `fpbs-burnside-embedding-input`. So O is needed in full for Burnside groups,
  and nothing here gives fixed price one for them.

## 6. Scope and certificate boundary

- **Checked by hand.** Lemma A, Lemma B.0, Lemma B, Theorem C, Corollaries
  C.1 and C.2, Lemmas D.1 and D.2 and Theorem D. Nothing is formally verified.
- **Imported.** [IND] is Gaboriau's induction formula, recorded in the graph
  through `fpbs-normalized-induction-reference`. [KHE] is an imported theorem
  whose proof was not rechecked here. [WQ] is a repo proof built on Gaboriau's
  lecture notes and Ornstein--Weiss.
- **Not claimed.**
  - Fixed price one for `Gamma/F` from fixed price one for `Gamma`, for finite
    `F ◁ Gamma`.
  - Statement O, which is open and equivalent to the target.
  - Any cost statement for free Burnside groups beyond the reduction.
- **Where attempts on O die** is recorded in
  `notes/fpbs-bounded-cost-fg-torsion-quotient-pr-swarm-2026-09-16.md` and in
  the Attempts of `fpbs-bounded-cost-just-infinite-faithful-price-one`.
