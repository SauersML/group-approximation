# solve-bh-mcg-outfn, 2026-09-13

Lane target: Boone--Higman, preferably permutational, for `Mod(Σ_g)` with `Σ_g`
closed, and for `Out(F_n)`.

**Verdict.** Partial. Both roots stay OPEN:
- `closed-surface-mapping-class-groups-satisfy-boone-higman` (`g ≥ 3`);
- `out-free-groups-satisfy-boone-higman` (`n ≥ 3`).

What this lane landed:
- **ESTABLISHED:** one elementary restriction lemma. A virtual section of
  `Aut(F_n) → Out(F_n)` restricts to a virtual section of every punctured-surface
  Birman sequence of rank `n`.
- **OPEN:** two nodes that make the free-group analogue of Chen--Salter a concrete
  target in even rank.

## 1. Literature pins

- **Survey and BFFHZ.** Already pinned on main in the two root nodes: BBMZ
  arXiv:2306.16356v3, Remark 5.4; BFFHZ arXiv:2503.21882v2, Section 4.
- **Later results.** Web search on 2026-09-13 ("Boone-Higman Out(F_n) finitely
  presented simple group 2026") found nothing past BFFHZ for these two cases. This
  was a spot check.
- **Chen--Salter, arXiv:1804.11235v1.** TeX `virtual_splitting.tex`, fetched on MSI
  (`~/mcgout/cs`).
  - l.152--153, the sequence treated: `1 \to \pi_1(\Sigma_g,*) \to
    \Mod(\Sigma_{g,*}) \to \Mod(\Sigma_g) \to 1`, with `Σ_g` closed.
  - l.164--166, verbatim: "For $g \ge 4$, the Birman exact sequence does not
    virtually split. Moreover, for any subgroup $\Gamma \le \mathcal
    I(\Sigma_g)$ of finite index in the Torelli group, there is no splitting
    $\sigma: \Gamma \to \mathcal I(\Sigma_{g,*})$ of the Birman exact sequence
    restricted to $\Gamma$."
  - The TeX contains no statement about bases with punctures.
- **L. Chen, arXiv:1708.07921.** TeX `draft2.tex` on MSI (`~/mcgout/chen`).
  - l.121: "If $S=S_g$ a surface of genus $g>1$ and for $n>1$, the bundle $f_{n}(S)$
    does not have a section."
  - These are configuration-space bundles `PConf_{n+1}(S) → PConf_n(S)`, i.e.
    surface braid groups, over the whole group. The statement is not virtual and
    not about mapping class groups, so it doesn't answer the question here.

## 2. The restriction lemma (landed, ESTABLISHED)

`free-group-virtual-sections-give-punctured-birman-sections`, with route
`free-group-virtual-sections-punctured-birman-proof`.
- A section `s: Γ → Aut(F_n)` over finite-index `Γ ≤ Out(F_n)` restricts, through
  Dehn--Nielsen--Baer, to a section of
  `1 → π1(Σ_{g,k}) → PMod(Σ_{g,k+1}) → PMod(Σ_{g,k}) → 1` over `Γ ∩ PMod(Σ_{g,k})`,
  whenever `k ≥ 1` and `2g + k − 1 = n`.
- Trust surface: DNB for punctured surfaces and the pure Birman sequence
  (Farb--Margalit Thm 8.8, Thm 4.6), not re-read.

## 3. Once-punctured base: adaptation map (OPEN node)

Setup:
- `Σ = Σ_g`, `g ≥ 2`, with puncture `x` and new marked point `∗`;
- `σ: Γ → PMod(Σ; x, ∗)` a section of forgetting `∗` over finite-index
  `Γ ≤ PMod(Σ; x)`;
- the x-pushing group `Λ := Γ ∩ π1(Σ, x) = ker(Γ → Mod(Σ))`, normal in `Γ`, of
  finite index in `π1(Σ, x)`.

**(F) Factorization.**
- `σ(Λ)` lies over the identity of `Mod(Σ)`, so `σ(Λ) ≤ PB_2(Σ) = π1 PConf_2(Σ)`
  (the kernel of forgetting both points, `g ≥ 2`).
- Its two coordinates are `λ` (forget `∗`) and `s(λ) := (forget x)(σ(λ))`.
- So `i × s = ι∘σ|_Λ`, where `ι: PConf_2(Σ) ⊂ Σ × Σ`.
- By Chen--Salter Lemma `HPConf` (l.669--675), `(i × s)^*[Δ] = 0` in `H^2(Λ; Q)`.

**(E) Equivariance.**
- For `γ ∈ Γ` and `λ ∈ Λ`: `s(γλγ^{-1}) = φ_γ s(λ) φ_γ^{-1}` with
  `φ_γ := (forget x)σ(γ) ∈ Mod(Σ, ∗)`.
- `φ_γ` and `γ` have the same image in `Mod(Σ)`, since forgetting both points
  commutes.
- So `s` is equivariant up to conjugacy under the image `Γ̄ ≤ Mod(Σ)`. This is
  Chen--Salter Lemma `equivariant` (l.590--609) with `p = g`.

**(C) Contradiction, given the dichotomy.**
- **Case A:** `s = i`. Then `(i × i)^*[Δ] = χ(Σ_g)·d·[Λ] ≠ 0`, with `d = [π1Σ : Λ]`.
- **Case B:** `s = 1`. Then the value is `d·[Λ] ≠ 0`.
- This is their l.677--704 verbatim, with `\overline{\mathcal H}` replaced by `Λ`.

### 3.1 Twist-lift lemma (proof written here; not landed as a claim)

**(LT)** Let `c ⊂ Σ ∖ x` be a simple closed curve essential in `Σ`, and `T_c^m ∈ Γ`.
For a suitable `M`, `σ(T_c^M)` is a multitwist about curves `c', c''` (isotopic to
`c` after forgetting `∗`) and possibly `d'` (bounding a disk containing `x` and `∗`).
So `(forget x)σ(T_c^M)` is a multitwist about curves isotopic to `c` in `Σ`.

*Proof.*
- **Centralizer rank.** A pants decomposition of `Σ ∖ x` containing `c` has
  `3g − 2` curves. Powers of their twists in `Γ` give `Z^{3g−2}` in the centralizer
  of `T_c^m`. As `σ` is injective, the same holds for `σ(T_c^m)`.
- **Step 1.** Let `γ' ∈ CRS(σ(T_c^m))` with `γ` (forget `∗`) essential in `Σ ∖ x`
  and not isotopic to `c`.
  - If `i(γ, c) ≠ 0`: a power of `T_c^m` fixes `γ`, against Chen--Salter Prop.
    `noin` (l.198--205).
  - If `γ` is disjoint from `c`: `γ` is essential and non-peripheral in a component
    of `(Σ ∖ x) ∖ c`. So some `e` there has `i(e, γ) ≠ 0`. `T_e^{m'} ∈ Γ` commutes
    with `T_c^m`, so a power of `σ(T_e^{m'})` fixes `γ'`, and forgetting `∗` gives a
    contradiction.
  - The only other possibility is `γ` inessential in `Σ ∖ x`, i.e. `γ'` a curve
    `d'` bounding a disk containing `x` and `∗`. Pairwise disjoint such curves are
    isotopic, so there is at most one.
- **Step 2.** Suppose the CRS contains no lift of `c`. Then it is `∅` or `{d'}`.
  - If `∅`: `σ(T_c^m)` has infinite order, so it is pseudo-Anosov, and its
    centralizer is virtually cyclic (McCarthy, l.240--242). That contradicts
    `Z^{3g−2}`.
  - If `{d'}`: some power is the identity or pseudo-Anosov on `R = Σ ∖ disk`.
    - The identity case would make a power a power of `T_{d'}`. Forgetting `∗`
      then kills it, but `T_c^{mN} ≠ 1`.
    - In the pseudo-Anosov case the centralizer lies in `Stab(d')`, and restriction
      shows it is virtually abelian of rank `≤ 2`: virtually cyclic on `R`, plus
      `⟨T_{d'}⟩`, while the twice-punctured disk has trivial pure mapping class
      group rel boundary modulo `T_{d'}`. That contradicts `3g − 2 ≥ 4`.
- **Step 3.** Suppose a power of `σ(T_c^m)` is pseudo-Anosov on a component `C` of
  the complement of the CRS.
  - `C` is not an annulus and not the twice-punctured disk. After forgetting `∗` it
    contains a component `R_0` of `(Σ ∖ x) ∖ c`.
  - Pick `e` essential and non-peripheral in `R_0`. By Steps 1--2, `σ(T_e^{M'})`
    has a lift `e'` of `e` in its CRS, and `σ(T_c^m)` commutes with it. So a power
    of `σ(T_c^m)` fixes `e'`.
  - `e'` meets no CRS curve, so `e' ⊂ C`, and it is essential and non-peripheral
    there. A pseudo-Anosov on `C` fixes no such curve, which is a contradiction.
  - Hence some power `σ(T_c^M)` is a multitwist about the CRS. Forgetting `x` sends
    `d'` to a peripheral curve, which gives the second sentence of (LT). ∎

### 3.2 The unverified step

Chen--Salter derive the dichotomy A/B from the lifts of bounding-pair maps (Lemma
`BPlifts`, l.494--518) and Lemma `Ghom` (l.520--547).

**Analogue here.**
- For simple `α ∈ π1(Σ, x)`, the push `α = T_{α_L} T_{α_R}^{-1}` with `x` between
  `α_L` and `α_R`.
- An argument like (LT) should give `σ(α^k)` as a multitwist about lifts of `α_L`,
  `α_R`, `d'`.
- So `(forget x)σ(α^k) = (T_{α̂_L} T_{α̂_R}^{-1})^u`, a push of `∗` along a curve
  parallel to `α`.

**What is unchecked.** The identification of that push with `α^u` in the
basepoint-free form Lemma `Ghom` needs.
- Pushing `∗` along the parallel curve determines a based loop only once a path
  from `x` to `∗` is fixed.
- When `∗` sits in the annulus between two lifts of `α_L` rather than next to `x`,
  that path crosses `α̃_L`, and the based element differs by a conjugation that
  depends on `α`.
- The proof of Lemma `Ghom` uses `f(β^ℓ α^k β^{-ℓ})` for simple conjugates, and it
  must be rechecked under this ambiguity.
- Chen--Salter's handle-pushing proof faces the same point and treats it
  implicitly.

**Sharper form of the gap (sketched, not landed).**
- **Free-conjugacy form.** (LT) gives the dichotomy's input only up to
  conjugacy, and robustly.
  - Let `α` be simple and `c` essential in `Σ` and disjoint from `α`.
    `(forget x)σ(T_c^M)` is a multitwist about lifts of `c`, and it commutes with
    the push `s(α^k)`.
  - By the argument of Chen--Salter Lemma `BPint` (l.294--307), the support of
    `s(α^k)` misses those lifts.
  - The curves disjoint from `α` fill `Σ ∖ α`. So `s(α^k)` is conjugate in
    `π1(Σ)` to `α^{m(α,k)}`.
  - Hence `ρ(α) := m(α,k)/k` is well defined, and invariant under conjugation and
    under `Γ̄`.
- **Where `Ghom` breaks.** `Ghom` needs *based* equalities, and the conjugators
  `β_α` from the path ambiguity break its commutation step.
- **The homology alternative is blocked.**
  - The alternative would be to show that `s_* − t·i_*` kills a spanning set of
    `H_1(Λ; Q)`.
  - That needs the classes of powers of lifts of simple closed curves to span. For
    covers of *punctured* surfaces they need not: Malestein--Putman,
    arXiv:1708.06486, abstract, "We construct examples of finite covers of
    punctured surfaces where the first rational homology is not spanned by lifts of
    simple closed curves".
  - Here the cover is of the *closed* `Σ_g`, which that abstract does not address,
    so the obstruction is not known to apply. Either way this route needs its own
    spanning argument.

Until this is written out, the node stays OPEN.

### 3.3 A cohomological partial

Transfer and absolute irreducibility of `H^1(Σ_g; Q)` under finite-index subgroups
of `Mod(Σ_g)` give:
- `s^* = t·i^* + r` with `t ∈ Q` and `r` into `ker(cor)`;
- cross terms between `i^*H^1` and `ker(cor)` vanish (projection formula);
- `(i × s)^*[Δ] = d(1 + t² − 2gt) + u`, where `u` is the value of the `Γ̄`-invariant
  form `⟨r(·) ∪ r(·)⟩`, a multiple of the intersection form.

If `r = 0`, a zero would need `t = g ± √(g² − 1) ∉ Q`, so there is a contradiction.
`r = 0` holds when `π1(Σ)/Λ` is abelian: each nontrivial isotypic summand then has
dimension `2g − 2 < 2g` (Chevalley--Weil for unbranched covers). `Λ` is dictated by
`σ`, so this does not close the claim.

## 4. Consequences for the Boone--Higman roots

- **Even rank.** If `once-punctured-birman-sequence-does-not-virtually-split`
  holds, every lifting construction for `Out(F_{2g})` dies (Attempts 1 and 6 of
  `out-free-groups-virtually-embed-in-aut-free-groups`). What would remain is an
  exotic faithful action of a finite-index subgroup on a free group.
- **Product and finite-extension hosts give nothing new** (observation, not
  landed).
  - Take `Q = Out(F_n)`, `n ≥ 3`, or `Mod(Σ_g)`, `g ≥ 3`. Two normal subgroups with
    trivial intersection commute.
  - A nontrivial normal subgroup is infinite (virtually torsion-free, no finite
    normal subgroups) and contains a fully irreducible or pseudo-Anosov element,
    whose centralizer is virtually cyclic.
  - So any embedding into `Γ_1 × Γ_2` is injective on one factor. Locally finite
    kernels (lamp wreath hosts, `bh-type-a-class-closed-under-permutational-lamp-wreaths`)
    are trivial.
- **Exact gap for the roots, unchanged in substance.**
  - A type (A) actor containing `Out(F_n)` or `Mod(Σ_g)`, or an embedding into
    `Aut(F_m)` or a punctured mapping class group.
  - The orbit-of-pairs route with `Hom(π1, M)/Inn(M)` fails: the `Aut(M)`-classes
    of values on peripheral or simple loops are infinitely many invariants of
    pairs, and constants from `M` are not conjugation-equivariant (BFFHZ Section 4
    remark, recorded on main).

## 5. Ownership

- **Last touched by a peer within 6h (15:51):** the Zaremsky 3.10 nodes and
  `every-*-embeds-in-some-aut-free-group`. Read, not edited.
- **Edited:** `out-free-groups-virtually-embed-in-aut-free-groups`, Attempt 7 only;
  last touched 2026-09-12.
