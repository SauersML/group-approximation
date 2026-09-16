# Building-open subgroups of Kac--Moody lattices have infinite bi-index (2026-09-16)

Lane `swarm-fp-simple-kac-moody-lattices-a`. Target: `fp-simple-kac-moody-lattices-are-highly-transitive`
(BFFHZ Question 3.6, part one). This artifact carries the proofs for:

- `km-building-open-subgroups-have-infinite-bi-index`, route
  `km-building-open-subgroups-bi-index-proof`: Theorem A, §2--§3;
- `km-building-open-subgroups-have-infinite-ht-orbits`, route
  `km-building-open-ht-orbits-from-bi-index-proof`: Corollary B, §4.

The question stays OPEN. This is a no-go for one class of candidate actions, not a decision.

## 0. Sources and pins

**[CM]** P.-E. Caprace, T. Marquis, *Open subgroups of locally compact Kac--Moody groups*,
arXiv:1108.4934v2 (v1 2011-08-24, v2 2012-08-09). The arXiv metadata has no journal
reference, and the published version was not checked. Line numbers refer to the e-print
TeX `OpenKM_rev.tex`, fetched 2026-09-16.

- **l.822 (setup).** "Let $\GGG=\GGG(\FF_q)$ be a (minimal) Kac--Moody group over a finite
  field $\FF_q$ of order $q$. The group $\GGG$ is endowed with a root group datum [...] which
  yields a twin BN-pair $(\mathcal B_+, \mathcal B_-, \mathcal N)$ with associated twin
  building $(\Delta_+, \Delta_-)$. Let $C_0$ be the fundamental chamber of $\Delta_+$, namely
  the chamber such that $\mathcal B_+ = \Stab_\GGG(C_0)$ [...]"
- **l.825.** "We next let $G$ be the completion of $\GGG$ with respect to the positive building
  topology. Thus the finitely generated group $\GGG$ embeds densely in the topological group
  $G$, which is locally compact, totally disconnected and acts properly and continuously on
  $\Delta := \Delta_+$ by automorphims. [...] Let $B = \overline{\mathcal B_+}$ be the closure
  of $\mathcal B_+$ in $G$, let $N = \Stab_G(A_0)$ and $H = B \cap N = \Fix_G(A_0)$."
- **l.826.** "The pair $(B, N)$ is a BN-pair of type $(W, S)$ for $G$; in particular we have
  $N/H \cong W$. Moreover, the group $B$ is a compact open subgroup, and every standard
  parabolic subgroup $P_J = B W_J B$ for some $J \subseteq S$ is thus open in $G$."
- **No irreducibility in the setup.** The section setup l.819--826 (checked again 2026-09-16)
  places no irreducibility hypothesis on `(W,S)`. The only "irreducible" in the statements used
  here is in Corollary `corintro2`, which is quoted for context and not used in any proof.
- **l.844.** "Thus $\mathcal P_J = \Stab_\GGG(R_J(C_0))$, $P_J = \Stab_G(R_J(C_0))$ and
  $\mathcal P_J$ is dense in $P_J$."
- **l.220.** "Let $\Phi=\Phi(\Sigma)$ denote the set of half-spaces of $\Sigma$. A half-space
  $\alpha \in \Phi$ will also be called a \textbf{root}."
- **l.227.** "we call a subset $J\subseteq S$ \textbf{essential} if each irreducible component
  of $J$ is non-spherical."
- **l.779.** "$\Phi_J=\{\alpha\in\Phi \ | \ \exists v\in W_J, \ s\in J: \alpha=v\alpha_s\}$, where
  $\alpha_s$ denotes the positive root associated with the reflection $s$."
- **l.782--784, Lemma `lemme racine essentielle`.** "Let $L\subseteq S$ be essential. Then for
  each root $\alpha\in\Phi_L$, there exists $w\in W_L$ such that $w.\alpha \subsetneq \alpha$."
  The proof in [CM] cites Hée, Prop. 8.1; Hée was not read.
- **l.907--916, Theorem `thm complet`.** "Let $O$ be an open subgroup of $G$. Let $J\subseteq S$
  be the type of a residue which is stabilized by some finite index subgroup of $O$ and minimal
  with respect to this property. Then there exist a spherical subset $J'\subseteq J^{\perp}$
  and an element $g\in G$ such that $$L_J^+\cdot U_{J\cup J^{\perp}}<gOg\inv<P_{J\cup J'}.$$ In
  particular, $gOg\inv$ has finite index in $P_{J\cup J'}$."
- **l.152--154, Corollary `corintro2`.** "Let $G$ be a complete Kac--Moody group of irreducible
  type over a finite field. Then $G$ has few open subgroups if and only if the Weyl group of $G$
  is of affine type, or of compact hyperbolic type." Here "few open subgroups" means that every
  proper open subgroup is compact (l.129). The proof (l.1209) notes that these are exactly the
  types all of whose proper parabolic subgroups are finite.

**[CR]** P.-E. Caprace, B. Rémy, *Simplicity and superrigidity of twin building lattices*,
arXiv:math/0607664v2 (Invent. Math. 176 (2009) 169--221, per the arXiv metadata). Line numbers
refer to the e-print TeX `SimplSuperrigid.tex`.

- **l.511--512.** The kernel of the action of $\Lambda$ on $\mathscr{B}_+$ "is the centralizer
  $Z_\Lambda(\Lambda^\dagger)$ and is contained in $T$".
- **l.543, l.549.** The completion of $\Lambda$ in a left-invariant ultrametric is called the
  building topology.
- **l.556--566, Proposition `prop:TopoCompletions`.**
  - "(ii) The canonical map $\pi_+ : \Lambda \to \Lambda^{\mathrm{eff}}_+$ has a unique extension
    to a continuous surjective open homomorphism $\overline \pi_+ :\overline \Lambda_+ \to
    \overline \Lambda^{\mathrm{eff}}_+$."
  - "(iii) The kernel of $\overline \pi_+$ is the discrete subgroup $Z_\Lambda(\Lambda^\dagger) <
    \overline \Lambda_+$."

**Coxeter groups and BN-pairs.** Only standard facts are used, at chapter level (Bourbaki,
*Lie IV--VI*, Ch. IV §1--§2; Abramenko--Brown, *Buildings*, GTM 248, Ch. 2, 3, 6). They were not
re-read on 2026-09-16. Three facts are used:

- the sign character;
- the exchange and deletion conditions;
- the BN-pair axioms, in particular (BN3): `sBw ⊆ BwB ∪ BswB` for `s ∈ S`, `w ∈ W`.

Everything else about Coxeter groups is proved in §3.4.

## 1. Setting

- **(S1)** `Λ = 𝒢(F_q)` is a minimal Kac--Moody group over a finite field. Its twin root datum
  has Coxeter system `(W,S)` with `S` finite and `W` infinite. `Δ = Δ_+` is the positive building
  and `C_0` its fundamental chamber.
- **(S2)** `G` is the completion of `Λ` in the positive building topology ([CM] l.825, which is
  [CR]'s `\overline Λ_+`, [CR] l.543--549). We use only the following.
  - **(G1)** `Λ ≤ G` is dense, and `G` is a Hausdorff topological group ([CM] l.825).
  - **(G2)** `G` acts on `Δ`, and the action restricted to `Λ` is the original action ([CR] Prop.
    (ii): `\overline π_+` extends `π_+`). The kernel of `Λ ↷ Δ` is `Z_+ := Z_Λ(Λ^†)` ([CR]
    l.511--512).
  - **(G3)** `(B,N)` is a BN-pair of type `(W,S)` for `G`, and `B = Stab_G(C_0)` is compact open.
    For `J ⊆ S`, `P_J = B W_J B = Stab_G(R_J(C_0))` is open ([CM] l.826, l.844; `J = ∅` gives
    `B = Stab_G(C_0)`).
  - **(G4)** Theorem `thm complet` of [CM].
- **(S3)** A subgroup `M ≤ Λ` is **building-open** if `Λ ∩ V ⊆ M` for some open subgroup `V ≤ G`.
  These are exactly the subgroups that are open in the topology induced on `Λ` by `G`.

**Examples of building-open subgroups.**
- **Chamber fixators.** For every finite set `F` of chambers of `Δ`,
  `Fix_Λ(F) = Λ ∩ Fix_G(F)`, and `Fix_G(F)` is open. Every chamber has the form `λC_0` with
  `λ ∈ Λ`, since `Λ` is chamber-transitive (`Δ = Λ/𝓑_+`). Then `Stab_G(λC_0) = λBλ^{-1}` is open
  by (G3), and `Λ ∩ Stab_G(C) = Stab_Λ(C)` by (G2).
- **Parabolics.** Similarly the Borel subgroup `𝓑_+ = Λ ∩ B` and the parabolics
  `𝓟_J = Λ ∩ P_J`.

## 2. Theorem A

**Theorem A.** In the setting of §1, assume `(W,S)` is irreducible. Let `M ≤ Λ` be
building-open. Then

```text
[Λ : M] < ∞      or      |M \ Λ / M| = ∞.                                   (A)
```

**Two supplements.**
- **(A')** When every proper parabolic subgroup `W_K`, `K ⊊ S`, is finite, (A) has a shorter
  proof (§3.5), which uses neither §3.4(C7) nor the [CM] nesting lemma.
  - **Irreducibility is automatic.** A reducible `W = W_1 × W_2` with `W` infinite has an infinite
    proper parabolic, namely an infinite factor. So (A') does not enlarge the class of types; it
    only shortens the proof.
  - **Where irreducibility matters.** Step 4 genuinely needs it: for `W_1` infinite, `W_2` finite
    and `K = S_1`, the set `W_K\W/W_K ≅ W_2` is finite. But there `[G:P_K] < ∞`, so this is not a
    counterexample to (A). Reducible types are not claimed.
- **(A'')** If `N ⊴ Λ` with `N ⊆ Z_+`, then (A) holds for every subgroup of `Λ/N` containing
  the image of some `Λ ∩ V`. Apply (A) to its preimage, which contains `Λ ∩ V` and has the same
  index and the same number of double cosets.

## 3. Proof of Theorem A

### 3.1 Step 1: transfer to G

Let `V` be an open subgroup with `Λ ∩ V ⊆ M`, and let `O` be the closure of `M` in `G`.

1. **`O` is an open subgroup.** Closures of subgroups are subgroups. For `g ∈ V` and an open
   `U ∋ g`, the set `U ∩ V` is open and nonempty, so it meets the dense `Λ`. Hence
   `V ⊆ closure(Λ ∩ V) ⊆ O`.
2. **`Λ ∩ O = M`.**
   - `MV` is a union of left `V`-cosets, hence open. Its complement is also a union of left
     `V`-cosets, hence open. So `MV` is clopen and `O ⊆ MV`.
   - If `λ ∈ Λ ∩ MV`, write `λ = mv` with `m ∈ M`, `v ∈ V`. Then `v = m^{-1}λ ∈ Λ ∩ V ⊆ M`, so
     `λ ∈ M`. Thus `M ⊆ Λ ∩ O ⊆ Λ ∩ MV ⊆ M`.
3. **`ΛO = G`.** For `g ∈ G`, the open set `gO` meets `Λ`, say in `λ`, and then `g ∈ λO`.
4. **Index.** `λM ↦ λO` is a `Λ`-equivariant map `Λ/M → G/O`. It is surjective by (3) and
   injective by (2). So `[Λ:M] = [G:O]`.
5. **Double cosets.** `|M\Λ/M|` is the number of `M`-orbits on `Λ/M ≅ G/O`, and `|O\G/O|` is the
   number of `O`-orbits on `G/O`. These orbits coincide.
   - For `gO ∈ G/O`, the stabilizer `S_g = O ∩ gOg^{-1}` is open in `O`.
   - For `o ∈ O`, the open set `oS_g` meets the dense subgroup `M` of `O`, say in `m`. Then
     `m gO = o gO`.

   Hence `|M\Λ/M| = |O\G/O|`.

### 3.2 Step 2: reduction to a parabolic

- **Apply [CM] Theorem `thm complet`** to `O`. It gives `K = J ∪ J' ⊆ S` and `g ∈ G` with
  `O' := gOg^{-1} ≤ P_K` of finite index.
- **Case `K = S`.** `P_S = Stab_G(R_S(C_0)) = Stab_G(Δ) = G` by (G3), since `R_S(C_0)` is the set
  of all chambers (buildings are gallery-connected). So `[G:O] = [G:O'] < ∞`, and by Step 1
  `[Λ:M] < ∞`.
- **Case `K ⊊ S`.** Conjugation by `g` gives `|O\G/O| = |O'\G/O'|`. Every `P_K`-double coset is
  a union of `O'`-double cosets, so `|O'\G/O'| ≥ |P_K\G/P_K|`.

It remains to show `|P_K\G/P_K| = ∞` for `K ⊊ S`.

### 3.3 Step 3: from G to W

For `w ∈ W`, let `n_w ∈ N` be a representative. Since `H ⊆ B`, the sets `B n_w B`, `B n_w`,
`n_w B` depend only on `w`; write `BwB` and so on.

**(B1) Bruhat disjointness: `BwB = Bw'B` implies `w = w'`.**

Induct on `m = min(ℓ(w), ℓ(w'))`, and assume `ℓ(w) ≤ ℓ(w')`.
- **`m = 0`.** Then `w = 1`, so `n_{w'} ∈ B ∩ N = H` and `w' = 1`.
- **`m > 0`.** Choose `s ∈ S` with `ℓ(sw) < ℓ(w)`.
  - From `n_w ∈ Bw'B` we get `n_{sw} ∈ n_s^{-1} n_w H ⊆ s B w' B`.
  - By (BN3), `s B w' ⊆ Bw'B ∪ Bsw'B`, so `B(sw)B ∈ {Bw'B, B(sw')B}`.
  - Both pairs `(sw, w')` and `(sw, sw')` have minimum length at most `ℓ(sw) = m-1`. By induction
    `sw = w'` or `sw = sw'`.
  - The first is impossible, since `ℓ(sw) < ℓ(w) ≤ ℓ(w')`. Hence `w = w'`.

**(B2) Double cosets of a parabolic.** For `K ⊆ S` and `w ∈ W`,
`P_K n_w P_K ⊆ ⋃_{x,y ∈ W_K} BxwyB`.

1. **Left factor.** Let `x = s_1⋯s_k` with `s_i ∈ K`. Then `BxB ⊆ Bs_1B s_2B ⋯ Bs_kB`.
   - (BN3) gives `B s B u B ⊆ BuB ∪ BsuB` for all `u ∈ W`.
   - Applying this `k` times, from the right, gives `BxBwB ⊆ ⋃ Bx'wB`, where `x'` runs over the
     products of subwords of `s_1⋯s_k`. All of these lie in `W_K`.
2. **Right factor.** Inverting (BN3) for `w^{-1}` gives `wBs ⊆ BwB ∪ BwsB`. The same argument
   gives `Bx'wByB ⊆ ⋃_{y' ∈ W_K} Bx'wy'B`.
3. Since `P_K = ⋃_{x ∈ W_K} BxB`, the claim follows.

**(B3) Injection.** `W_K w W_K ↦ P_K n_w P_K` is a well-defined injection
`W_K\W/W_K → P_K\G/P_K`.

- **Well defined.** If `w' = xwy` with `x,y ∈ W_K`, then `n_{w'} ∈ n_x n_w n_y H ⊆ P_K n_w P_K`.
- **Injective.** Suppose `P_K n_{w'} P_K = P_K n_w P_K`. By (B2), `n_{w'} ∈ Bx'wy'B` for some
  `x',y' ∈ W_K`. By (B1), `w' = x'wy'`.

So it suffices to show `|W_K\W/W_K| = ∞` for `K ⊊ S`.

### 3.4 Step 4: the Coxeter lemma

**Lemma C.** Let `(W,S)` be an irreducible Coxeter system with `S` finite and `W` infinite, and
let `K ⊊ S`. Then `|W_K\W/W_K| = ∞`.

**Notation.**
- `ℓ` is the length with respect to `S`.
- `Cay` is the Cayley graph, with edges `{x, xu}` for `u ∈ S`. Left multiplication by any
  `v ∈ W` is a graph automorphism.
- For `s ∈ S`, `α_s := {x ∈ W : ℓ(sx) > ℓ(x)}`.
- `Φ^c := {vα_s : v ∈ W, s ∈ S}` is the set of combinatorial roots.

**Imported facts.**
- **(E1) Sign character.** There is a homomorphism `ε: W → {±1}` with `ε(s) = -1` for all
  `s ∈ S`. Hence `ℓ(ux) = ℓ(x) ± 1` for `u ∈ S`.
- **(E2) Exchange.** If `x = s_1⋯s_k` with `k = ℓ(x)`, `s ∈ S` and `ℓ(sx) < ℓ(x)`, then
  `sx = s_1⋯ŝ_i⋯s_k` for some `i`.
- **(E3) Deletion.** If `ℓ(s_1⋯s_k) < k`, two letters can be deleted without changing the
  product.

**(C0) `W_K ∩ S = K`, and each `x ∈ W_K` has an expression of length `ℓ(x)` with letters in `K`.**
Start with any `K`-word for `x` and apply (E3) until the length is `ℓ(x)`; deletion keeps the
letters in `K`. If `s ∈ S ∩ W_K`, then `ℓ(s) = 1` by (E1), and the resulting word is a single
letter of `K` equal to `s`.

**(C1) If `s ∈ S∖K`, then `W_K ⊆ α_s`.** Suppose `x ∈ W_K` with `ℓ(sx) < ℓ(x)`. Apply (E2) to a
`K`-expression of `x` of length `ℓ(x)` from (C0). Then `sx ∈ W_K`, so `s ∈ W_K ∩ S = K`, a
contradiction.

**(C2) Folding: if `s, u ∈ S`, `x ∈ α_s` and `xu ∉ α_s`, then `sx = xu`.**
1. By (E1) and `xu ∉ α_s`, `ℓ(sxu) = ℓ(xu) - 1`.
2. If `ℓ(xu) = ℓ(x) - 1`, then `ℓ(sxu) = ℓ(x) - 2`. But `ℓ(sxu) ≥ ℓ(sx) - 1 = ℓ(x)`, a
   contradiction.
3. So `ℓ(xu) = ℓ(x) + 1`. If `x = s_1⋯s_k` is reduced, then `s_1⋯s_k u` is reduced.
4. (E2) deletes one letter from `s_1⋯s_k u` to give `sxu`.
   - Deleting some `s_i` gives `sx = s_1⋯ŝ_i⋯s_k`, of length `< ℓ(x)`, contradicting `x ∈ α_s`.
   - Hence the deleted letter is `u`: `sxu = x`, that is, `sx = xu`.

**(C3) `sα_s = W∖α_s`; `α_s` and `W∖α_s` are connected in `Cay`; `1 ∈ α_s`, `s ∉ α_s`.**
- **Complement.** `x ∈ α_s` iff `ℓ(sx) > ℓ(x)` iff `sx ∉ α_s`.
- **Connected.** Take `x ∈ α_s` and a reduced `x = s_1⋯s_k`. Suppose a prefix
  `p_j = s_1⋯s_j` has `ℓ(sp_j) < ℓ(p_j)`. By (E2), `sp_j = s_1⋯ŝ_i⋯s_j`, so
  `sx = s_1⋯ŝ_i⋯s_k` has length `< k`, which is impossible. So the path `1, p_1, …, p_k = x`
  stays in `α_s`.
- **Complement connected.** `W∖α_s = sα_s` is the image of `α_s` under a graph automorphism.

**(C4) Cut sets.** Let `β = vα_s ∈ Φ^c` and `t := vsv^{-1}`.
- `t` maps `β` onto `W∖β`, by (C3) transported by `v`.
- An edge `{x, xu}` has exactly one endpoint in `β` iff `xux^{-1} = t`.
  - **Forward.** If `x ∈ β` and `xu ∉ β`, then `v^{-1}x ∈ α_s` and `v^{-1}xu ∉ α_s`. By (C2),
    `sv^{-1}x = v^{-1}xu`, so `xux^{-1} = t`.
  - **Converse.** If `xux^{-1} = t`, then `xu = tx`, and exactly one of `x`, `tx` lies in `β`.
- Since `β ≠ ∅ ≠ W∖β` and `Cay` is connected, cut edges exist. So `t =: t_β` is determined by
  `β` as a set.

**(C5) For each edge `{y, yu}`, at most one `β ∈ Φ^c` contains `y` but not `yu`.**
1. If `β, β'` both do, then `t_β = yuy^{-1} = t_{β'}` by (C4). So `β` and `β'` have the same set
   `E` of cut edges.
2. By (C3), transported by `v`, `β` and `W∖β` are connected. No edge outside `E` joins them. So
   the components of `Cay∖E` are exactly `β` and `W∖β`, and likewise for `β'`.
3. Both are the component containing `y`, so `β = β'`.

**(C6) `#{β ∈ Φ^c : 1 ∈ β, w ∉ β} ≤ ℓ(w)` for every `w ∈ W`.**
- Let `1 = x_0, x_1, …, x_k = w` be a geodesic in `Cay`, `k = ℓ(w)`.
- For such a `β`, let `j(β)` be the least `j` with `x_j ∈ β` and `x_{j+1} ∉ β`; it exists
  because `x_0 ∈ β` and `x_k ∉ β`.
- By (C5), `β ↦ j(β)` is injective into `{0, …, k-1}`.

**(C7) Identification with [CM]'s roots.**
- **The imported fact** (Abramenko--Brown Ch. 3, chapter level, not re-read): the chambers of
  the Coxeter complex `Σ(W,S)` are the elements of `W`, `W` acts by left multiplication, and the
  half-space of the wall of `s` containing the fundamental chamber `1` is `α_s`.
- **What is actually proved here.** Let `t = vsv^{-1}` be a reflection. The panels through
  which the wall of `t` passes are the edges `{x, xu}` with `xux^{-1} = t`, since `t` swaps
  their two chambers. By (C3)--(C5), removing exactly these edges from `Cay` leaves two
  connected components, `vα_s` and `W∖vα_s = (vs)α_s`. So the only import is that the two
  half-spaces of a wall, as chamber sets, are the components of the chamber graph after
  deleting the edges through that wall. Then `α_s` is the half-space of the wall of `s`
  containing the fundamental chamber `1`, which is [CM]'s positive root `α_s` (l.779).
- **Consequence.** [CM]'s `Φ` (l.220) is `Φ^c`, with the same `W`-action and with `⊊` meaning
  strict inclusion of chamber sets. Every half-space is `vα_s` or `v sα_s = (vs)α_s`.
- **Scope.** This is used only in (C8), and only when `W_K` is infinite.

**(C8) Proof of Lemma C.**
1. **Setup.** Choose `s ∈ S∖K`. By (C1), `W_K ⊆ α_s`. Since `(W,S)` is irreducible and `W` is
   infinite, `S` is essential ([CM] l.227), and `sα_s ∈ Φ_S` ([CM] l.779, with `v = s`).
2. **Nesting.** [CM] Lemma `lemme racine essentielle` with `L = S`, read through (C7), gives
   `h ∈ W` with `h(sα_s) ⊊ sα_s`. Taking complements with (C3), `hα_s ⊋ α_s`.
3. **The chain.** Put `α_i := h^i α_s`. Then `α_0 ⊊ α_1 ⊊ ⋯`, and every `α_i` contains
   `α_0 ⊇ W_K`.
4. **Far cosets.** For `n ≥ 0` and `0 ≤ i ≤ n`,
   `h^n s W_K ⊆ h^n sα_s = h^n(W∖α_s) = W∖α_n ⊆ W∖α_i`.
5. **Length bound.** Let `w' = u h^n s u'` with `u, u' ∈ W_K`.
   - Each of the `n+1` distinct roots `uα_0, …, uα_n` contains `uW_K = W_K ∋ 1`.
   - None contains `w' ∈ u h^n s W_K ⊆ u(W∖α_i) = W∖uα_i`.
   - By (C6), `ℓ(w') ≥ n+1`.
6. **Conclusion.** Every element of `W_K h^n s W_K` has length `≥ n+1`. If there were finitely
   many `(W_K,W_K)`-double cosets, the minimal lengths of elements in them would be bounded. Hence
   `|W_K\W/W_K| = ∞`. ∎

With Steps 1--3 this proves Theorem A. ∎

### 3.5 Step 4': proper parabolics finite (proof of (A'))

Suppose every `W_K` with `K ⊊ S` is finite, and let `K ⊊ S` be given by Step 2.

1. **`O` is compact.** `P_K = ⋃_{x ∈ W_K} BxB` is a finite union of the compact sets `BxB`, each
   the image of `B × B` under `(b,b') ↦ b n_x b'`. So `P_K` is compact. `O'` is an open, hence
   closed, subgroup of `P_K`, so it is compact, and so is `O`.
2. **`G` is not compact.** The cosets `n_w B`, `w ∈ W`, are pairwise distinct by (B1), since
   `n_w B ⊆ BwB`. So `[G:B] = ∞`. A compact group with an open subgroup `B` would have
   `[G:B] < ∞`.
3. **Conclusion.** Each double coset `OgO` is compact. Finitely many of them would cover `G` by
   a compact set. So `|O\G/O| = ∞`, and `|M\Λ/M| = ∞` by Step 1.

**What (A') needs.** It uses only (G1)--(G4), (BN3), (B1) and the finiteness of `W_K`. It does
not use (C0)--(C8) or the nesting lemma.

**In the compact case (A) is elementary once `O` is known to be compact.** A compact open `O` is
commensurated in `G`, so `M = Λ ∩ O` is commensurated in `Λ`. A commensurated subgroup of finite
bi-index has finite index. The real inputs are:
- [CM] `thm complet`, which gives compactness of every proper open subgroup when proper
  parabolics are finite. This is [CM] Corollary `corintro2` for irreducible types.
- For other types, Step 4.

## 4. Corollary B: building-open subgroups in multiply transitive actions

Keep the setting of Theorem A. Let `N ⊴ Λ` with `N ⊆ Z_+`, and put `Γ := Λ/N`.
- **Examples.** `N` trivial; `N` the centre of `Λ`, which lies in `Z_Λ(Λ^†) = Z_+`. So the lattices
  `S_q = Λ_q/Z`, and every `Λ/Z(Λ)`, are covered.
- **Not covered.** Caprace--Rémy's simplicity theorem ([CR] TeX l.132--136) makes `[Λ,Λ]` modulo
  its finite centre simple. When `Λ` is not perfect this is not a quotient of `Λ`. The passage
  to the finite-index subgroup `[Λ,Λ]` is not treated here.
- **Notation.** For an open subgroup `V ≤ G`, let `Γ_V` be the image of `Λ ∩ V` in `Γ`.
- **Chamber fixators.** `N` acts trivially on `Δ`, so `Γ` acts on `Δ`. Then
  `Fix_Γ(F) = Γ_{Fix_G(F)}` for finite sets `F` of chambers, and `𝓟_J/N = Γ_{P_J}`.

Let `Γ` act on an infinite set `Ω`, and write `Γ_ω` for point stabilizers.

**Corollary B.**
- **(a)** If the action is transitive with finitely many orbitals, no `Γ_ω` contains any `Γ_V`.
- **(b)** Let `k ≥ 1`. If the action is `2k`-transitive, every `Γ_V`-orbit has more than `k`
  points.
- **(b')** If the action is highly transitive, every orbit of every `Γ_V`, and of every
  finite-index subgroup of `Γ_V`, is infinite. Equivalently, `[Γ_V : Γ_V ∩ Γ_ω] = ∞` for all `V`
  and `ω`.
- **(c)** Suppose the action is primitive with finitely many orbitals, and let `M̃` be the
  preimage of `Γ_ω` in `Λ`. Then `closure_G(M̃)` is `G` or is not open.
- **(d)** If `H ≤ Γ` has infinite index and `|H\Γ/H| < ∞`, let `H̃` be its preimage in `Λ`. Then
  `closure_G(H̃)` is not open, or is an open subgroup of finite index in `G`.

### Proofs

**(a)** `Γ_ω` has infinite index `|Ω|`, and `|Γ_ω\Γ/Γ_ω|` equals the number of orbitals, which is
finite. By (A'') it contains no `Γ_V`.

**(b)**
1. Suppose some `Γ_V`-orbit `A` has `m ≤ k` points, and let `M_A` be the setwise stabilizer of
   `A`. Then `Γ_V ⊆ M_A`.
2. **Infinite index.** An infinite set admits `j`-transitivity for all `j ≤ 2k`, by extending
   tuples. So `Γ` is transitive on the set `Ω^{(m)}` of `m`-subsets, and
   `[Γ:M_A] = |Ω^{(m)}| = ∞`.
3. **Finitely many double cosets.** Let `(A_1,A_2)` and `(A_3,A_4)` be pairs of `m`-subsets with
   `|A_1 ∩ A_2| = |A_3 ∩ A_4|`.
   - There is a bijection `A_1 ∪ A_2 → A_3 ∪ A_4` mapping `A_1` to `A_3` and `A_2` to `A_4`.
   - It is realized by an element of `Γ`, because `|A_1 ∪ A_2| ≤ 2m ≤ 2k`.
   - So `Γ` has at most `m+1` orbits on pairs of `m`-subsets, and `|M_A\Γ/M_A| ≤ m+1`.
4. This contradicts (A'').

**(b')**
- **Orbits of `Γ_V`.** Apply (b) for every `k`.
- **Finite-index subgroups.** Let `L ≤ Γ_V` have index `r < ∞` with a finite orbit `Lω`. Then
  `Γ_V ω` is a union of at most `r` translates of `Lω`, hence finite, contradicting the first
  part.
- **The equivalence.** It is the orbit-stabilizer relation `|Γ_V ω| = [Γ_V : Γ_V ∩ Γ_ω]`.

**(c)**
1. Put `O = closure_G(M̃)` and assume `O` is open. `M̃` is the stabilizer of `ω` for the pulled
   back `Λ`-action, which is primitive, so `M̃` is maximal in `Λ`.
2. `Λ ∩ O` is a subgroup containing `M̃`. If `Λ ∩ O = Λ`, then `O ⊇ closure(Λ) = G`.
3. Otherwise `Λ ∩ O = M̃`, so `M̃` is building-open. It has infinite index and finitely many
   double cosets, contradicting Theorem A.

**(d)**
1. Put `O = closure_G(H̃)` and assume `O` is open. Then `M := Λ ∩ O ⊇ H̃` is building-open.
2. Every `M`-double coset is a union of `H̃`-double cosets. So
   `|M\Λ/M| ≤ |H̃\Λ/H̃| = |H\Γ/H| < ∞`.
3. By Theorem A, `[Λ:M] < ∞`. By Step 1 applied to `M`, whose closure is `O`,
   `[G:O] = [Λ:M] < ∞`. ∎

**Link to type (A) actions.** For a finitely presented simple `Γ`,
`fp-simple-type-a-actions-iff-finite-bi-index-subgroups` identifies type (A) actions with proper
finitely generated `H` with `|H\Γ/H| < ∞`. Such an `H` has infinite index, because `Γ` is infinite
simple. So by (d), the closure in `G` of `H̃` is non-open or has finite index. Moreover `H`
contains no `Γ_V`: otherwise `H̃ ⊇ Λ ∩ V` would be building-open with infinite index and finitely
many double cosets, contradicting (A'').

## 5. The explicit members S_q

**The group.** Let `Λ_q` be of type `(2,4,6)` over `F_q`, `q ≥ 4`, and `S_q = Λ_q/Z`
(`km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`).
- `|S| = 3` and all `m_{ij} ∈ {2,4,6}`.
- A proper `K ⊊ S` has at most two elements, so `W_K` is trivial, of order 2, or finite dihedral
  of order at most 12.
- `W` is the infinite `(2,4,6)` triangle group.

**What holds.** Theorem A holds for `S_q` through (A') and (A''), without (C7) or the nesting
lemma. In every highly transitive action of `S_q`:
- all orbits of `𝓑_+/Z`, of every `Fix_{S_q}(F)` and of their finite-index subgroups are infinite;
- no point stabilizer contains any building-open subgroup.

Not covered: the negative building, and subgroups whose closure is not open (§6).

## 6. Imports and limits

**Imports (all read in TeX 2026-09-16, except those marked).**
- [CM] l.822--826, l.844 (setup, BN-pair, parabolics), `thm complet` (l.907--916).
- [CM] `lemme racine essentielle` (l.782--784), only for (C8). Its proof cites Hée Prop. 8.1,
  not read.
- [CR] Prop. `prop:TopoCompletions` (ii)--(iii) and l.511--512.
- Coxeter (E1)--(E3), BN-pair axioms, and (C7): chapter level, not re-read.

**Limits.**
1. **The question is not decided.** HT actions with stabilizers whose closure is non-open are
   not touched. Examples are discrete subgroups of `G`, stabilizers of ideal points of the Davis
   realization, and subgroups dense in `G`.
2. **Negative building.** The same statement for the completion in the negative building topology
   presumably follows by the symmetry `α ↦ -α` of twin root data, or by a Chevalley involution.
   This was not checked, so it is not claimed.
3. **Not a combination theorem.** Theorem A says nothing about subgroups `M` with `Λ ∩ V_+ ⊄ M`
   and `Λ ∩ V_- ⊄ M` for all open `V_±`. `Λ` is discrete in `G_+ × G_-` (irreducible lattice,
   `km-246-completions-are-kazhdan-howe-moore-simple` (KHM3)), so the "mixed" subgroups
   `Λ ∩ (V_+ × V_-)` are finite and give nothing.
4. **Novelty.** Theorem A is a short combination of [CM], density, BN-pair axioms and Coxeter
   combinatorics. No literature statement of it was found (§7). No novelty is claimed, and it may
   well be folklore.

## 7. Literature gate record (2026-09-16)

**arXiv API queries**, with sleeps between calls, all returning 0 entries:
- `abs:"highly transitive" AND abs:"Kac-Moody"`;
- building and open-subgroup variants.

**Primary sources consulted** (TeX or abstracts; dates or ids from arXiv metadata):
- **Recent (2024--2026):**
  - Rybak arXiv:2605.14159v3
  - Hyde--Lodha arXiv:2509.09788
  - Caprace--Thom arXiv:2606.27993
  - Flores arXiv:2607.28316
  - Chakraborty arXiv:2607.26267
  - Elliott arXiv:2601.15185
  - Avni--Gelander arXiv:2510.03492
  - Vigdorovich arXiv:2503.12737
  - Bischof arXiv:2504.17513
- **Older:**
  - André--Guirardel arXiv:2212.06020
  - Abramenko--Gates arXiv:1912.05611
  - Garion--Glasner arXiv:1008.0563
  - Glasner--Kitroser--Melleray arXiv:1601.07538
  - Hull--Osin arXiv:1501.04182
  - Fima--Le Maître--Moon--Stalder arXiv:2003.11116
  - Caprace--Rémy arXiv:math/0607664v2
  - Caprace--Marquis arXiv:1108.4934v2
- **Via the repo:**
  - Creutz--Peterson arXiv:1311.4513v3
  - Le Boudec--Matte Bon, Ann. H. Lebesgue 5 (2022)

**Outcome.**
- None of them proves or refutes high transitivity of finitely presented simple Kac--Moody
  lattices.
- None states Theorem A.
- Garion--Glasner's question on high transitivity of `SL_n(Z)`, `n ≥ 3`, is recorded there as
  open. It is the linear analogue; this is from the abstract and introduction, and its current
  status was not re-checked.
