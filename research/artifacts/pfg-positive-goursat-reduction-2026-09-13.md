# Sofic set actions of products of free groups: Goursat reduction and the left-right sofic class

Lane `ex3-pfg-positive`, 2026-09-13. Unreviewed. Soficity is GKP Definition 2.1(5).
(CA), (FI) and (LS) are from `research/artifacts/pfg-positive-co-amenable-restriction-2026-09-13.md`.
(S2) is from `separating-sofic-quotient-sets-make-an-action-sofic`.

## 1. The left-right sofic class

For a countable group `Q` and epimorphisms `q_1 : F ↠ Q` and `q_2 : F' ↠ Q` from
countable free groups, define the left-right action

```text
LR(q_1,q_2) :  F × F' ↷ Q,      (u,v)·h = q_1(u) h q_2(v)^-1.
```

Its point stabilizer at `1` is the fibre product
`M(q_1,q_2) = { (u,v) : q_1(u) = q_2(v) }`. With `q_1 = q_2` this is the
Mikhailova left-right action (MLF1) of `mikhailova-left-right-action-current-frontier`.

**Definition.** `Q` is *left-right sofic* if `LR(q_1,q_2)` is sofic for all such
`q_1`, `q_2`.

**Proposition 1.1.**

(i) If `LR(q,q)` is sofic for one epimorphism `q : F ↠ Q`, then `Q` is
left-right sofic. For finitely generated `Q`, `F` may be taken finitely
generated. This covers item 1 of the frontier node.

(ii) Amenable groups are left-right sofic.

(iii) Subgroups of left-right sofic groups are left-right sofic.

(iv) Finite direct products of left-right sofic groups are left-right sofic.

(v) `Q` is left-right sofic iff every finitely generated subgroup of `Q` is
(Theorem 2.1 below). For finitely generated `Q`, left-right sofic means (MLF1)
is sofic.

(vi) A marked-group limit of finitely generated left-right sofic groups is
left-right sofic. Hence LEA groups are left-right sofic. This recovers
`mikhailova-left-right-action-sofic-for-lea-quotients`.

*Proof.*

(i) Since `F` is free, choose `θ_i : F_i → F` with `q∘θ_i = q_i`. Then
`LR(q_1,q_2)` is `LR(q,q)` precomposed with `θ_1 × θ_2`, and models compose.

(ii) The action factors through `Q × Q ↷ Q`. Use GKP Theorem 2.17 and
Proposition 2.15(1).

(iii) Let `P ≤ Q` with markings `p_i`. Extend them to epimorphisms
`q_1 = p_1 * s_1 : F * F'' ↠ Q` and `q_2` likewise. Restrict `LR(q_1,q_2)` to
`F × F'` (GKP 2.15(3)). Its orbit through `1` is `p_1(F) p_2(F')^-1 = P`,
carrying `LR(p_1,p_2)` (GKP 2.15(2)).

(iv) Mark `Q_1 × Q_2` by `q = q^1 * q^2 : F_1 * F_2 ↠ Q_1 × Q_2`. Then `LR(q,q)`
is the pullback, along the natural map `(F_1*F_2)^2 → (F_1×F_1) × (F_2×F_2)`,
of the product of `LR(q^1,q^1)` and `LR(q^2,q^2)`. That product is sofic by
(S2).

(vi) Suppose marked groups `Q_n → Q` on `m` generators, so
`ker(q_n) ∩ B_R = ker(q) ∩ B_R` for large `n`. Then the radius-`r` balls of the
two Schreier graphs agree for large `n`. For `|g|, |g'| ≤ r`,
`g^-1 g' ∈ M(q,q)` is a membership test of length `≤ 4r` for the kernel. So
the identity on words is a partial equivariant injection into `LR(q_n,q_n)`,
and (LS) applies. The LEA statement follows because LEA groups are limits of
subgroups of amenable groups, which are left-right sofic by (ii) and (iii). `∎`

## 2. Goursat reduction

Let `G = F × F'` with `F`, `F'` countable free, and `L ≤ G` any subgroup. Put:

- `A = p_1(L)` and `B = p_2(L)`;
- `N_1 × 1 = L ∩ (A × 1)` and `1 × N_2 = L ∩ (1 × B)`.

By Goursat's lemma, `L = { (a,b) ∈ A × B : ρ_1(a) = ρ_2(b) }` for epimorphisms
`ρ_1 : A ↠ Q_L` and `ρ_2 : B ↠ Q_L`, where `Q_L = A/N_1 ≅ B/N_2`. Call `Q_L` the
Goursat quotient of `L`.

**Theorem 2.1.** If every finitely generated subgroup of `Q_L` is left-right
sofic, then `G ↷ G/L` is sofic.

*Proof.*

**Step 0 (finitely generated actors).** Write `F = ∪_k F^(k)` and
`F' = ∪_k F'^(k)` as increasing unions of finitely generated free factors, and
put `G_k = F^(k) × F'^(k)`. By GKP 2.15(4) it suffices to show each restriction
to `G_k` is sofic, and by 2.16 it suffices to do so orbitwise. The orbit through
`gL` is `G_k/L_g` with `L_g = G_k ∩ gLg^-1`. Conjugation by `g = (g_1, g_2)`
carries `L` to a fibre product over `Q_L`, and intersecting with `G_k` gives
the fibre product of the restrictions of `ρ_i ∘ c_(g_i)^-1` to the projections
of `L_g`. So the Goursat quotient of `L_g` is a subgroup of `Q_L`, and its
finitely generated subgroups are finitely generated subgroups of `Q_L`. Assume
from now on that `F` and `F'` are finitely generated.

**Step 1 (a local fibre product).** Fix a finite window `F_0 ⊆ B_f(G)` and a
finite set `E ⊆ { gL : |g| ≤ r }`. Put:

- `W = B_(2r+2f)(G)`;
- `L_R = ⟨ L ∩ W ⟩`, which is finitely generated;
- `A_R = p_1(L_R)` and `B_R = p_2(L_R)`, both finitely generated;
- `L^+ = L ∩ (A_R × B_R)`.

Then `L_R ≤ L^+ ≤ L`, so `p_1(L^+) = A_R` and `p_2(L^+) = B_R`. Also
`L^+ = { (a,b) ∈ A_R × B_R : ρ_1(a) = ρ_2(b) }`. So `L^+` is the fibre product of
`ρ_1|A_R` and `ρ_2|B_R` over `P = ρ_1(A_R) = ρ_2(B_R)`, a finitely generated
subgroup of `Q_L`. Hence

```text
(A_R × B_R)/L^+  ≅  LR(ρ_1|A_R, ρ_2|B_R)   is sofic, since P is left-right sofic.
```

**Step 2 (Marshall Hall retraction).** By Marshall Hall's theorem, the finitely
generated subgroup `A_R` is a free factor of a finite-index subgroup
`F_1 = A_R * C ≤ F`. Likewise `F'_1 = B_R * D ≤ F'`. Let
`r : F_1 → A_R` and `r' : F'_1 → B_R` be the retractions killing `C` and `D`.
Put `G_1 = F_1 × F'_1`, which has finite index in `G`, and
`K = (r × r')^-1(L^+) ≤ G_1`. Since `r × r'` is the identity on `A_R × B_R`,

```text
K ∩ (A_R × B_R) = L^+.
```

`G_1 ↷ G_1/K` is the composition of the epimorphism `r × r'` with the sofic
action of Step 1, so it is sofic by GKP 2.15(1). By (FI), `G ↷ G/K` is sofic.

**Step 3 (a sofic target).** Let `Y = G/K × G/(A_R × B_R)` with the diagonal
`G`-action. `G/(A_R × B_R) = F/A_R × F'/B_R` is sofic by GKP Theorem 2.19 and
(S2). The product of two sofic `G`-sets is sofic under the diagonal: apply (S2)
to `G × G`, then restrict to the diagonal (GKP 2.15(3)).

**Step 4 (partial embedding).** For `x ∈ E` choose `g_x` with `|g_x| ≤ r` and
`x = g_x L`, and put

```text
ι(x) = ( g_x K , g_x (A_R × B_R) ).
```

- *Equivariance.* Let `s ∈ F_0` with `x, sx ∈ E`. Then
  `g_(sx)^-1 s g_x ∈ L ∩ W ≤ L^+ ≤ K ∩ (A_R × B_R)`, so `ι(sx) = s·ι(x)`.
- *Injectivity.* `ι(x) = ι(x')` gives `g_x^-1 g_(x') ∈ K ∩ (A_R × B_R) = L^+ ≤ L`,
  so `x = x'`.

By (LS), `G ↷ G/L` is sofic. `∎`

The stabilizer of the base point of `Y` is `L^+`, which is smaller than `L`.
This is why (LS) is needed: neither global separation nor approximation by
larger subgroups applies.

**Corollary 2.2 (equivalences).** The following are equivalent.

(a) `product-of-free-groups-set-actions-are-sofic`: every action of a product
of two countable free groups on a countable set is sofic.

(b) Every countable group is left-right sofic.

(c) For every finitely presented group `H`, the Mikhailova left-right action
(MLF1) is sofic.

*Proof.*

- (a) ⇒ (c): (MLF1) is such an action.
- (c) ⇒ (b): a finitely generated `Q = ⟨X | R⟩` is the marked limit of the
  finitely presented groups `Q_n = ⟨X | relators in R of length ≤ n⟩`, so
  Proposition 1.1(vi) makes it left-right sofic. Proposition 1.1(v) then gives
  every countable group.
- (b) ⇒ (a): GKP 2.16 reduces to transitive actions, and Theorem 2.1 applies.
  `∎`

So a single finitely presented `H` with a nonsofic (MLF1) refutes (a). In
particular the fixed nonsofic property-(T) quotient left open in
`mikhailova-left-right-action-current-frontier` is a special case of (a).

## 3. Co-amenable overgroups

**Theorem 3.1.** If `H` has a co-amenable subgroup `P` that is left-right sofic,
then `H` is left-right sofic.

*Proof.* Let `q_1 : F ↠ H` and `q_2 : F' ↠ H`. Put `A_i = q_i^-1(P)`. Since
`F/A_1 ≅ H/P` as `F`-sets, `A_1` is co-amenable in `F`, and likewise `A_2`
in `F'`. So `D = A_1 × A_2` is co-amenable in `F × F'`: products of Følner sets
are Følner. By (CA) it suffices that the restriction of `LR(q_1,q_2)` to `D` is
sofic.

The `D`-orbits are the double cosets `PhP`. The stabilizer of `h` in `D` is

```text
L_h = { (a,b) ∈ A_1 × A_2 : q_1(a) = h q_2(b) h^-1 },
```

a subgroup of the product of the two free groups `A_1`, `A_2`. Its first
projection is `A_1 ∩ q_1^-1(P ∩ hPh^-1)`, and `q_1` identifies its Goursat
quotient with `P ∩ hPh^-1 ≤ P`. By Proposition 1.1(iii) every finitely generated
subgroup of it is left-right sofic. Theorem 2.1, applied to the actor
`A_1 × A_2`, makes each orbit sofic, and GKP 2.16 finishes. `∎`

**Corollary 3.2.**

(a) If `R ◁ H`, `R` is left-right sofic and `H/R` is amenable, then `H` is
left-right sofic.

(b) Let `H = ⟨B, t | t b t^-1 = θ(b)⟩` be an ascending HNN extension with
`θ : B → B` injective and `B` left-right sofic. Then `H` is left-right sofic.
The kernel of `H ↠ Z` is the increasing union of the copies `t^-k B t^k`, which
is left-right sofic by Proposition 1.1(iii),(v). Then apply (a).

(c) `H` is left-right sofic iff some co-amenable subgroup is, iff every
co-amenable subgroup is.

**Firewall 3.3 (property (T)).** If `H` has property (T), every co-amenable
subgroup has finite index. An invariant mean on `ℓ^∞(H/P)` gives almost
invariant vectors in `ℓ^2(H/P)`, and (T) turns them into an invariant vector,
so `H/P` is finite. So for Kazhdan `H`, Theorem 3.1 adds nothing beyond
finite-index subgroups. The same holds for any `H` without infinite amenable
transitive actions.

**Remark 3.4.** Every group produced from amenable groups by (iii)--(vi) and
Theorem 3.1 is sofic, by Corollary 1.3 of part 1 and the permanence of soficity
under limits and subgroups. So these closure properties cannot reach a
nonsofic quotient. A positive answer to (a) for a nonsofic `H` needs a model
with nontrivial kernel action, as (MCC4) of
`mikhailova-left-right-soficity-is-one-color-code` requires.
