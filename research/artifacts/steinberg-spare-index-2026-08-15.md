# Spare-index independence at n = 5

**Verdict: PROVED.**  This also closes **Lemma X** of
`ATLAS_COMPLETENESS_DERIVATION_2026-08-15.md` — see §11 for the full
reconciliation, including why that note's stall was only apparent (its
Lemma 3.1 assumes commutations of the length-`t` object that are in fact
derivable, and none of its five rejected routes was needed).

No extra relators are needed.  The emitted family
described in `research/artifacts/atlas-rank5-dictionary-2026-08-15.md` §2.5
(full (St2)/(St3) instantiation on `A = {1,e,f,e*,f*}`, all 25 coefficient
pairs, all roots, all three intermediate indices equated to one canonical
right-hand side) already forces `Ê_ij(w)` to be independent of the chain of
spare indices, for every monomial `w` of every length `t ≥ 1`.

The proof is an induction on `t` that carries three statements at once —
chain-independence, a commutation statement, and a general splitting law.
Hall–Witt is **not** needed; the only bracket identity used is
`[ab,c] = a[b,c]a⁻¹[a,c]`.  The argument is an `n ≥ 5` argument: three
distinct places consume a spare index that `n = 4` does not supply.

Three by-products fall out along the way, and the third is a defect report:

* the splitting law **is** (St3) for `Ê` on monomials, and the commutation
  statement **is** (St2) for `Ê` on monomials — so those are now *proved*,
  not "true by construction" as the program note assumed;
* `Ê_ij` automatically descends through every *multiplicative* Cuntz–Krieger
  reduction (`e*e → 1`, `f*f → 1`, `e*f → 0`, `f*e → 0`, and unit letters),
  leaving only the single *additive* relation `ee* + ff* = 1` for the
  additive-extension step;
* **the emitted family is missing the 100 relators `x_ij(a)²`, and they are
  provably not derivable from it** (§8.2) — the additive extension needs
  them, and a characteristic-zero lift to `St₅(L_Z(1,2))` shows the emitted
  family cannot force them.  This is a real, cheap, safe repair to emit
  next; it is a defect of the family, not of this lemma, whose proof uses no
  additivity and no torsion statement.

---

## 1. Conventions

`n = 5`, indices in `{1,…,5}`.  Commutator and conjugation:

```
[x, y] = x y x⁻¹ y⁻¹ ,        ᶻx = z x z⁻¹ .
```

With this convention the pinned scheme reads, in matrices,
`[1 + r e_ij, 1 + s e_jk] = 1 + rs e_ik` for `i ≠ k` — checked directly, so
the convention matches (St3) as pinned.  (Everything below is
convention-robust: `L` is an `F₂`-algebra, but the proof never uses that.)

A **letter** is an element of `A = {1,e,f,e*,f*}`; a **monomial** (or
**word**) `w = a₁a₂⋯a_t` is a finite sequence of letters, `t = |w| ≥ 1`.
Words are handled *as words*: `Ê_ij` is defined on the free monoid on `A`,
not on `L`.  Passing from words to ring elements is a separate matter
(§7, §8).

**Chains.**  For a root `(i,j)` and `|w| = t`, a *legal chain* is a sequence
`κ = (k₀ = i, k₁, …, k_{t-1}, k_t = j)` with

```
k_m ≠ k_{m-1}   (1 ≤ m ≤ t),        k_m ≠ j   (1 ≤ m ≤ t-1),
```

i.e. exactly the sequences produced by the recursion
`Ê_ij(a₁⋯a_t) = [X_{i k₁}(a₁), Ê_{k₁ j}(a₂⋯a_t)]`, `k₁ ∉ {i,j}`.  Note the
asymmetry: an interior index may equal `i` (e.g. `Ê_ij(abc) = [X_ik(a),
[X_ki(b), X_ij(c)]]` is legal) but never `j`.  At `n = 5` each root has
exactly `3^{t-1}` legal chains.  Write

```
Ê^κ_ij(w) = [X_{k₀k₁}(a₁), [X_{k₁k₂}(a₂), [ ⋯ , X_{k_{t-1}k_t}(a_t)] ⋯ ]] .
```

## 2. Exactly what is available in G₀

Only three families are used.  Nothing else — no additivity, no `X(a)² = 1`,
no property of `L`, no information about the canonical right-hand sides
beyond the fact that there *is* one.

* **(A) Root-subgroup commutativity.**  `[X_ij(a), X_ij(b)] = 1`, all
  `a,b ∈ A`, all roots.  (200 emitted relators = 20 roots × 10 unordered
  distinct letter pairs.)
* **(B) (St2).**  `[X_ij(a), X_kl(b)] = 1` whenever `i ≠ l` and `k ≠ j`,
  all 25 coefficient pairs.  Merging with (A) gives the form used
  throughout:

  > **(B′)** `X_ij(a)` and `X_kl(b)` commute whenever `j ≠ k` **and**
  > `l ≠ i` — i.e. two generators fail to commute only when the target of
  > one is the source of the other.

* **(C) (St3), all three chains anchored.**  For every root `(i,k)`, every
  `j ∉ {i,k}` and every pair `(a,b) ∈ A²`,
  `[X_ij(a), X_jk(b)] = C_{ik}(a,b)`, where `C_{ik}(a,b)` is **one** word
  depending only on `(i,k)` and `(a,b)`, the same for all three `j`.

  The proof uses **only the consequence** that the three `j`-chains agree:

  > **(P₂)** `[X_ij(a), X_jk(b)] = [X_{ij'}(a), X_{j'k}(b)]` for all
  > `j, j' ∉ {i,k}`.

  It never uses what `C_{ik}(a,b)` *is*.  That matters: in the atlas
  realisation `C` is an explicit word in the twelve atlas generators (via
  the 500 verified two-letter dictionary entries), whereas in the abstract
  `G₀` it is a word in the `X`'s.  The derivation is agnostic.

**Coverage check — VERIFIED against the emitter source.**  (B′) is needed at
*all* root pairs meeting the side condition, which at `n = 5` is 120
unordered pairs of distinct roots: 60 index-disjoint, **30 same-source**
`((i,j),(i,l))` and **30 same-target** `((i,j),(k,j))`.  Lemma K below uses a
same-target pair essentially, so this is not a formality.
`experiments/atlas_relator_rank5_full_family.py:159-164` reads

```python
roots = [(i, j) for i in range(1, 6) for j in range(1, 6) if i != j]
for (i, j), (k, ell) in itertools.combinations(roots, 2):
    if i != ell and k != j:
        for r, s in itertools.product(COEFF_LETTERS, repeat=2):
```

— the genuine (St2) side condition over *all* pairs of distinct roots, all 25
ordered coefficient pairs.  So same-source and same-target pairs are emitted,
and `120 × 25 = 3,000` candidates against the reported 2,980 distinct
nonidentity relators (the `add()` helper drops empty words and dedups).  The
`(k,l) = (i,j)` block at lines 151-154 gives the 200 root-subgroup relators,
and lines 169-173 give (St3) with `rhs = rank5_word_multi(i, k, [r, s])`,
which does **not** mention `j` — that is (P₂), verbatim in the source.

## 3. The three statements

For `t ≥ 1`:

* **(P_t)** For every root `(i,j)` and every `|w| = t`, all legal chains
  give the same element.  Call it `Ê_ij(w)`.
* **(Q_t)** For every root `(i,j)`, `|w| ≤ t`, every root `(p,q)` with
  `p ≠ j` and `q ≠ i`, and every `c ∈ A`:  `[Ê_ij(w), X_pq(c)] = 1`.
* **(Q′_t)** For all `|w| ≤ t`, `|w′| ≤ t` and roots `(i,j)`, `(k,l)` with
  `j ≠ k` and `l ≠ i`:  `[Ê_ij(w), Ê_kl(w′)] = 1`.
* **(R_t)** For every `|w| ≤ t`, every factorisation `w = uv` with `u,v`
  nonempty, and every `m ∉ {i,j}`:
  `Ê_ij(uv) = [Ê_im(u), Ê_mj(v)]`.

`(Q′)` is `(St2)` for `Ê`; `(R)` with `m = j` read at the root `(i,k)` is
`(St3)` for `Ê`:  `[Ê_ij(u), Ê_jk(v)] = Ê_ik(uv)`, `i ≠ k`.

Order of proof inside stage `t`:  **(P_t) → (R_t) → (Q_t) → (Q′_t)**, each
using only earlier stages plus what precedes it in this order.

## 4. The two elementary identities

**(I1)** `[ab, c] = a[b,c]a⁻¹ · [a,c]` in any group.
*Proof.* `a(bcb⁻¹c⁻¹)a⁻¹ · aca⁻¹c⁻¹ = abcb⁻¹a⁻¹c⁻¹ = (ab)c(ab)⁻¹c⁻¹.* ∎

**(I2)** If `[x,z] = 1` then, with `u = [x,y]`, `w = [y,z]`, `γ = [u,z]`,

```
[x, w] = u w u⁻¹ · γ · w⁻¹ .
```

*Proof.* `x w x⁻¹ = [xyx⁻¹, xzx⁻¹] = [uy, z]` (using `xyx⁻¹ = [x,y]y = uy`
and `xzx⁻¹ = z`).  By (I1), `[uy,z] = u[y,z]u⁻¹[u,z] = u w u⁻¹ γ`.  Hence
`[x,w] = xwx⁻¹w⁻¹ = u w u⁻¹ γ w⁻¹`. ∎

**(I2′) Collapse.**  If in addition `w` commutes with `u` and with `z`, then
`[x, w] = γ`.
*Proof.* `[u,w] = 1` gives `u w u⁻¹ = w`; and `w` commuting with both `u`
and `z` makes it commute with any word in them, in particular with
`γ = uzu⁻¹z⁻¹`, so `[x,w] = w γ w⁻¹ = γ`. ∎

Both were verified as literal group identities by random search in `S₁₂`
(§9).

## 5. Lemma K (the engine)

> **Lemma K.**  Let `i, j, k, m` be **pairwise distinct**, `a ∈ A`, and let
> `u₂, v` be nonempty words.  Assume (P), (Q′), (R) hold at all lengths
> `< 1 + |u₂| + |v|`.  Then
>
> ```
> [ X_ik(a), Ê_kj(u₂ v) ]  =  [ Ê_im(a u₂), Ê_mj(v) ] .
> ```
>
> In particular the left-hand side does not depend on `k`.

*Proof.*  Put

```
x = X_ik(a),      y = Ê_km(u₂),      z = Ê_mj(v),
u = [x,y],        w = [y,z],         γ = [u,z].
```

Five checks; each index condition is verified against (B′)/(Q′) explicitly,
and all five were confirmed to hold over all 120 pairwise-distinct
quadruples `(i,j,k,m)` at `n = 5` by brute force (§9).

1. **`[x,z] = 1`.**  Roots `(i,k)` and `(m,j)`.  (Q′) needs `k ≠ m` ✓ and
   `j ≠ i` ✓.
2. **`u = Ê_im(a u₂)`.**  `[X_ik(a), Ê_km(u₂)]` is precisely the left-nested
   chain for `Ê_im(a u₂)` with first spare index `k`; legal because
   `k ∉ {i,m}` ✓.  Equal to the canonical value by (P) at length
   `1 + |u₂|`.  (When `|u₂| = 1` this is the emitted (C)/(P₂) — the
   *anchor*: the two-letter right-hand side enters here and nowhere else.)
3. **`w = Ê_kj(u₂ v)`.**  This is (R) at the root `(k,j)`, factorisation
   `u₂ | v`, spare index `m`; legal because `m ∉ {k,j}` ✓.
4. **`[u, w] = 1`.**  Roots `(i,m)` and `(k,j)`.  (Q′) needs `m ≠ k` ✓ and
   `j ≠ i` ✓.
5. **`[z, w] = 1`.**  Roots `(m,j)` and `(k,j)` — a **same-target** pair.
   (Q′) needs `j ≠ k` ✓ and `j ≠ m` ✓.

By 1, (I2) applies; by 4 and 5, (I2′) collapses it:
`[x, w] = γ = [Ê_im(a u₂), Ê_mj(v)]`.  The right-hand side mentions
`i, j, m` only. ∎

Lengths used: `|a u₂| = 1+|u₂|`, `|u₂ v| = |u₂|+|v|`, `|v|`, all
`≤ t - 1` where `t = 1 + |u₂| + |v|` (because `|v| ≥ 1` and `|u₂| ≥ 1`), so
Lemma K only ever calls the induction hypothesis one level down.

## 6. The induction

### 6.1 Base `t = 1`

(P₁) is vacuous, (R₁) vacuous, and (Q₁) = (Q′₁) is exactly (B′).

### 6.2 Base `t = 2`

**(P₂)** is the emitted (C).  **(R₂)** is (P₂) restated.

**(Q′₂).**  Four cases, `j ≠ k`, `l ≠ i` throughout.
`|w| = |w′| = 1` is (B′).  For `|w′| = 2` write
`Ê_kl(w′) = [X_kp(b₁), X_pl(b₂)]` with `p ∉ {i,j,k,l}` — such `p` exists
because `|{i,j,k,l}| ≤ 4 < 5`, and `p ∉ {k,l}` makes the chain legal, so
(P₂) licenses the choice.  Then `Ê_ij(w)` (of length 1 or 2 — treat length
2 by the already-proved `|w′| = 1` case with roles swapped, the side
condition being symmetric) commutes with `X_kp(b₁)` (needs `k ≠ j` ✓,
`p ≠ i` ✓) and with `X_pl(b₂)` (needs `p ≠ j` ✓, `l ≠ i` ✓), hence with
their commutator.  The case `|w| = 2, |w′| = 1` is the same statement read
backwards.

### 6.3 Step: (P_t) for `t ≥ 3`

Let `w = a₁ a₂ v′` with `|v′| = t - 2 ≥ 1`, and let `κ` be a legal chain
with first spare index `k₁ = k`.  By (P_{t-1}) the tail is well defined, so

```
Ê^κ_ij(w) = [ X_ik(a₁), Ê_kj(a₂ v′) ]  =:  Ê^{(k)}_ij(w),
```

a function of `k ∈ S := {1,…,5} \ {i,j}` alone; `|S| = 3`.  For each
`m ∈ S` with `m ≠ k`, Lemma K (with `u₂ = a₂`) gives

```
Ê^{(k)}_ij(w) = V_m ,      V_m := [ Ê_im(a₁a₂), Ê_mj(v′) ] ,
```

and `V_m` does not mention `k`.  Write `S = {k_A, k_B, k_C}`.  Then

```
Ê^{(k_A)} = V_{k_B} = V_{k_C},
Ê^{(k_B)} = V_{k_A} = V_{k_C},
Ê^{(k_C)} = V_{k_A} = V_{k_B},
```

so `V_{k_A} = V_{k_B} = V_{k_C}` and all three `Ê^{(k)}` coincide. ∎

> **This is the step that consumes the third spare index.**  With only two
> spare indices (`n = 4`) the relations `Ê^{(k_A)} = V_{k_B}` and
> `Ê^{(k_B)} = V_{k_A}` are the only ones available and they compare
> nothing.

### 6.4 Step: (R_t) for `t ≥ 3`

Let `w = uv`, `|w| = t`, `m ∉ {i,j}`.  If `|u| = 1` this is (P_t).  If
`|u| ≥ 2` write `u = a₁ u₂` and pick `k ∈ {1,…,5} \ {i,j,m}` (two choices).
By (P_t), `Ê_ij(w) = [X_ik(a₁), Ê_kj(u₂ v)]`, and Lemma K turns this into
`[Ê_im(a₁u₂), Ê_mj(v)] = [Ê_im(u), Ê_mj(v)]`.  Lemma K's hypothesis 3 is
(R_{t-1}) at the root `(k,j)` with split `u₂|v` and spare `m ∉ {k,j}` ✓. ∎

### 6.5 Step: (Q_t)

Let `|w| = t`, and let `(p,q)` be a root with `p ≠ j`, `q ≠ i`.  Choose
`k₁ ∉ {i,j,p,q}` (exists: `|{i,j,p,q}| ≤ 4 < 5`).  By (P_t),
`Ê_ij(w) = [X_{i k₁}(a₁), Ê_{k₁ j}(v)]` with `|v| = t-1`.  Then

* `[X_{i k₁}(a₁), X_pq(c)] = 1` by (B′): needs `k₁ ≠ p` ✓, `q ≠ i` ✓;
* `[Ê_{k₁ j}(v), X_pq(c)] = 1` by (Q_{t-1}): needs `p ≠ j` ✓, `q ≠ k₁` ✓.

So `X_pq(c)` commutes with both entries, hence with the commutator. ∎

> **Second consumption of the spare index**: `k₁` must dodge four indices.

### 6.6 Step: (Q′_t)

Induct on `|w′|`.  `|w′| = 1` is (Q_{|w|}).  For `|w′| ≥ 2` write
`w′ = b₁ w″` and choose `p ∉ {i,j,k,l}` (exists at `n = 5`; also `p ∉
{k,l}`, so the chain is legal and (P_{|w′|}) licenses it):
`Ê_kl(w′) = [X_kp(b₁), Ê_pl(w″)]`.  Then

* `[Ê_ij(w), X_kp(b₁)] = 1` by (Q_{|w|}): needs `k ≠ j` ✓, `p ≠ i` ✓;
* `[Ê_ij(w), Ê_pl(w″)] = 1` by the inner induction: needs `p ≠ j` ✓,
  `l ≠ i` ✓. ∎

> **Third consumption of the spare index.**

This completes the induction, hence the Lemma.  ∎∎

## 7. Free corollaries

**C1 (St2)/(St3) for `Ê` on monomials.**  (Q′) and (R) are exactly these.
The program note's phrase "`Ê` … satisfies (St1)–(St3) by construction"
overstates: (St2) and (St3) are *theorems of the same induction*, and (St3)
in particular is false for a naively-defined `Ê` without (P).

**C2 (multiplicative CK reduction is automatic).**  If `w = u·ab·v` with
`a,b ∈ A` and `ab = c ∈ A` in `L`, then `Ê_ij(w) = Ê_ij(u c v)`; if
`ab = 0` in `L` then `Ê_ij(w) = 1`.
*Proof.*  Pick `m ∉ {i,j}` and `p ∉ {m,j}`.  By (R),
`Ê_mj(ab·v) = [Ê_mp(ab), Ê_pj(v)]`, and `Ê_mp(ab) = C_{mp}(a,b)`, which is
`X_mp(c)` (resp. `1`) by the emitted (C).  So `Ê_mj(abv) = Ê_mj(cv)`
(resp. `= 1`).  Apply (R) once more at `(i,j)` with split `u | abv`.
Degenerate cases `u` or `v` empty use one application. ∎

Consequently `Ê_ij` factors through the quotient of the free monoid on `A`
by the four *multiplicative* Cuntz–Krieger rules `e*e → 1`, `f*f → 1`,
`e*f → 0`, `f*e → 0` and by unit letters (`1·a = a·1 = a`).  Only the single
**additive** relation `ee* + ff* = 1` is left over for the additive
extension, which is where `atlas-steinberg-context-absorption` and the
emitted `partition` relator take over.

## 8. What this does *not* close

The completeness gap of `atlas-steinberg-rank-five-translation` needs
`Ê_ij : L → G₀`, not just `Ê_ij` on monomials.  Two things remain, both
outside this lemma:

1. **Order of the product.**  `Ê_ij(Σ_s w_s) := Π_s Ê_ij(w_s)` needs the
   factors to commute — that is (Q′) with `(k,l) = (i,j)`, which is proved
   above (this is the only place the root-subgroup relators (A) are
   genuinely needed; Lemma K never produces a same-root pair).
2. **`Ê_ij(w)² = 1` — MISSING, and provably not derivable.**  `Ê_ij` must be
   a homomorphism `(L,+) → G₀`, so `Ê_ij(a)² = Ê_ij(a + a) = Ê_ij(0) = 1`;
   equivalently, over `F₂` two representations of the same ring element as a
   sum of monomials differ by repeated monomials cancelling in pairs.  So
   `X_ij(a)² = 1` is *required*.  It does **not** follow from (A)+(B)+(C):

   > Let `L_Z = L_Z(1,2)`, the Leavitt path algebra of the rose with two
   > petals over `Z`.  It satisfies the same five Cuntz–Krieger relations —
   > which contain no characteristic assumption — and by Tomforde it is a
   > **free `Z`-module**, with the vertex `1` a basis element, so `2·1 ≠ 0`.
   > `St₅(L_Z)` satisfies (St1)–(St3), hence satisfies (A), (B), and (C) with
   > every canonical right-hand side sent to `E_ik(ab)`.  So there is a
   > homomorphism `G₀ → St₅(L_Z)`, `X_ij(a) ↦ E_ij(a)`, under which
   > `X_ij(1)²` maps to `E_ij(2)`, whose image in `E₅(L_Z)` is `1 + 2e_ij ≠ 1`.
   > Hence `X_ij(1)² ≠ 1` in `G₀`.

   The lift needs the canonical two-letter words to be characteristic-free,
   and they are: `rank5_word_multi` → `root_word`
   (`experiments/atlas_relator_rank5_dictionary.py:107-122`) builds them as
   *purely multiplicative* nested commutators through a spare index, with no
   additive decomposition — nothing anywhere uses the char-2 identity
   `ee* = 1 + ff*`.  I checked the source for this.

   **Repair (cheap, safe, and it should be emitted next):** add the 100
   relators `x_ij(a)²`, `a ∈ A` over the 20 roots, and verify them in `R̄` the
   same way as the rest.  They *are* in `R̄` — each `x_ij(a)` evaluates to a
   transvection over an `F₂`-algebra, so its square evaluates to `1` — so this
   is exactly the graceful degradation the program note anticipated.  The 100
   length-one relators suffice for all lengths: by (Q′), `δ = Ê_ij(uv)` is
   central in `⟨Ê_im(u), Ê_mj(v)⟩`, so (I1) gives
   `[Ê_im(u)², Ê_mj(v)] = δ²`, and `Ê_ij(w)² = 1` propagates up by induction
   on `|w|` from `|w| = 1`.  (Identity confirmed numerically in the
   Heisenberg group, §9.)

   Note this is a defect of the *emitted family*, not of the present lemma —
   the lemma's proof never uses additivity or any torsion statement.

## 9. Verification runs

Scripts under the session scratchpad (regenerable in seconds; nothing was
built and nothing in the repo was touched).

* `check1.py` — index bookkeeping at `n = 5`.  Confirms: the (St2) side
  condition is symmetric; 120 unordered pairs of distinct roots satisfy it
  (60 disjoint, 30 same-source, 30 same-target) so `120 × 25 = 3,000`
  candidate (St2) relators against the emitted 2,980 distinct nonidentity
  ones, and `20 × 10 = 200` root-subgroup ones matching exactly; the spare
  index required in §6.3/§6.5/§6.6 exists in every configuration at `n = 5`
  and fails in 24 configurations at `n = 4`; and **all five side conditions
  of Lemma K hold over all 120 pairwise-distinct `(i,j,k,m)`**.
* `check2.py` — (I1), (I2), (I2′) verified as group identities by random
  search in `S₁₂` (4,000 samples each; for (I2) with `x, z` forced to
  commute by disjoint support, and for (I2′) restricted to the 782 samples
  meeting the hypotheses).
* `check6.py` — the induction of §6 encoded as a dependency graph over the
   four statement families and checked against the proof order
   `(t, P<R<Q<Q′)`: acyclic, and `(P,t)` has **no** transitive dependency at
   length `≥ t`.  This is the direct refutation of the circularity diagnosed
   in `ATLAS_COMPLETENESS_DERIVATION_2026-08-15.md` §5 (see §11.4).
* `check2.py`'s collapse test is, in their notation, the **weakened Lemma
   3.1** of §11.3: 782 random samples in `S₁₂` meeting `[X,Z] = [U,V] =
   [Z,V] = 1` were checked, and `[X,V] = [U,Z]` held in every one — with no
   hypothesis on `T` at all.
* `check5.py` — `[α², β] = [α,β]²` when `[α,β]` is central in `⟨α,β⟩`,
   verified in the Heisenberg group (5,000 samples); this is the propagation
   step of §8.2.  (The same test in `S₁₂` never meets the hypothesis, which
   is why the nilpotent model is used.)
* `check3.py` — the *statement* verified in the model `St₅(R)`, `R` the
  free `F₂`-algebra on the letter slots truncated at degree 6, by computing
  every legal chain: 9 chains per root at `t = 3`, 27 at `t = 4`, all
  agreeing, common value `1 + a₀a₁a₂(a₃) e_ij`; and the splitting law of
  (R) verified for every split point and every `m ∉ {i,j}` at `t = 4`.

## 10. Traps for the next reader

1. **The emitted (St2) must use the side condition, not "disjoint roots".**
   Lemma K's check 5 is a **same-target** pair `((m,j),(k,j))`, and (Q′)/§6
   repeatedly use **same-source** pairs.  Had any emitter read "disjoint
   roots" as `{i,j} ∩ {k,l} = ∅`, 60 of the 120 pairs would be missing and
   this proof would break.  I checked: `atlas_relator_rank5_full_family.py`
   guards with `if i != ell and k != j` over `combinations(roots, 2)`, so the
   side condition is the real one and the proof is safe.  The prose label
   "disjoint-root commutation" on that block is a misnomer — do not let it
   mislead a future audit.
2. **This is an `n ≥ 5` proof, not an `n ≥ 4` proof.**  Three steps consume
   a spare index that `n = 4` does not have (§6.3, §6.5, §6.6).  It does not
   reprove [KrM, Theorem 3]; it proves what is needed at rank five.  Do not
   quote it as a rank-four statement.
3. **Interior indices may equal `i`, never `j`.**  The chain
   `Ê_ij(abc) = [X_ik(a), [X_ki(b), X_ij(c)]]` is legal and is covered by
   (P), but it is *not* an instance of the splitting law (R), which requires
   `m ∉ {i,j}`.  (P) and (R) are separate statements; do not derive one from
   the other.
4. **Nothing about the canonical right-hand side is used** beyond "all three
   `j` give the same element".  This is deliberate — it makes the lemma
   independent of how the 500 two-letter dictionary entries were realised as
   atlas words.  Conversely it means the lemma gives you *no* check on those
   entries.
5. **Hall–Witt is a red herring here.**  The expected route named it; the
   proof does not need it.  `[ab,c] = a[b,c]a⁻¹[a,c]` plus the observation
   that `w = [y,z]` commutes with both `u` and `z` does the whole job.  A
   reader trying to reconstruct a Hall–Witt version will find the third
   Hall–Witt term dies for the same reason and the surviving two terms
   reproduce (I2) after conjugation — more work, same content.
6. **`Ê_ij(w)² = 1` is missing from the emitted family and is provably not
   derivable from it** (§8.2), with a concrete 100-relator repair.  Do not
   let the present PROVED verdict be read as closing the completeness gap: it
   closes the *monomial* half.  The additive half now has one identified
   missing relator block and one remaining genuine step (the additive
   relation `ee* + ff* = 1` in monomial contexts, which is what
   `atlas-steinberg-context-absorption` is for).
7. **`X_ij(a)` is not known to be an involution, so do not silently drop
   inverses.**  The proof above is written with all inverses explicit for
   exactly this reason.  Any future write-up that "simplifies" using
   `X⁻¹ = X` because `L` has characteristic two is assuming §8.2's missing
   relators.

---

## 11. Reconciliation with `ATLAS_COMPLETENESS_DERIVATION_2026-08-15.md`

That note reaches the same target by the same overall plan and stalls at its
**Lemma X**.  Lemma X is closed by §6 above, and the stall was only apparent.
This section is the map, because the two notes use different names.

### 11.1 Dictionary

| there | here |
|:--|:--|
| `D^σ_ij(w)`, definition (D) | `Ê^κ_ij(w)` with first spare `σ` |
| (I) spare independence | **(P_t)** |
| (II) split independence, Lemma 4.1 | **(R_t)** |
| Lemma 5.1 (St2 for `D^σ`, `σ ∉ {k,l}`) | **(Q_t)/(Q′_t)**, with no `σ` proviso |
| Lemma 3.1 (transfer) | **Lemma K** (§5), with weaker hypotheses |
| **Lemma X** | two instances of **(Q′_t)** — see 11.2 |

### 11.2 Lemma X is (Q′)

Lemma X asks that `D^l_ij(w)` commute with `Ê_il(a)` and with `Ê_lj(w′)`.
By (P_t), `D^l_ij(w) = Ê_ij(w)`, and both claims are instances of (Q′_t):

* against `Ê_il(a)`: roots `(i,j)`, `(i,l)` — a **same-source** pair; (Q′)
  needs `j ≠ i` ✓ and `l ≠ i` ✓;
* against `Ê_lj(w′)`: roots `(i,j)`, `(l,j)` — a **same-target** pair; (Q′)
  needs `j ≠ l` ✓ and `j ≠ i` ✓.

Both are proved in §6.6 for every length.  So Lemma X holds at all lengths,
and by that note's own §§1-4 the completeness argument closes.

### 11.3 Why the stall was only apparent: Lemma 3.1's hypotheses are too strong

Their Lemma 3.1 assumes `[X,Z] = 1`, `[Y,V] = 1`, **and that `T = [X,V]`
commutes with `X`, `Y` and `V`**; its four-conjugation proof uses `[T,X]` and
`[T,Y]` at steps 2-4.  `T` is the length-`t` object at root `(i,j)`, so those
hypotheses are same-length statements — that is the entire source of the
circularity diagnosed in their §5 ("the one presentation the argument produces
is the one presentation whose commutation it cannot use").

**The commutations of `T` need not be assumed.**  In their notation, take
`x = X`, `y = Y`, `z = Z`, so `u = [x,y] = U` and `w = [y,z] = V`.  Identity
(I2) of §4, which needs only `[X,Z] = 1`, gives

```
T = [X, V] = U V U⁻¹ · [U,Z] · V⁻¹ .
```

Now `[U,V] = 1` collapses `U V U⁻¹` to `V`, and `V` commuting with `U` and with
`Z` makes it commute with `[U,Z]` — so `T = V [U,Z] V⁻¹ = [U,Z]`.  The
hypothesis set is therefore

```
[X,Z] = 1   roots (i,l),(k,j)   —  l ≠ k ✓, j ≠ i ✓
[U,V] = 1   roots (i,k),(l,j)   —  k ≠ l ✓, j ≠ i ✓
[Z,V] = 1   roots (k,j),(l,j)   —  j ≠ l ✓, j ≠ k ✓   (same-target)
```

**None of these mentions an object at root `(i,j)`.**  All three are (St2)
instances between strictly shorter objects at other roots, i.e. exactly what
their Lemma 5.1 supplies with no `σ` clash.  `[Y,V] = 1` is not needed either.

That is the whole repair: the derived object's own commutation is a
*consequence* (`V` commutes with `U` and `Z`, hence with `[U,Z]`), not a
hypothesis.  Their five rejected routes were all attempts to *supply* a
hypothesis that does not need supplying.

### 11.4 The joint induction is real, not circular — machine-checked

The team lead's idea (a) is correct, and 11.3 is what makes it go through.
Proof order per stage is **(P_t) → (R_t) → (Q_t) → (Q′_t)**, and (P_t) draws
only on `(P_{t-1}), (P_2), (R_{t-1}), (Q′_{t-1})`.  Encoding all four
statement families as a dependency graph and checking every edge against the
order `(t, P<R<Q<Q′)` (`check6.py`, §9):

```
ACYCLIC: every dependency is strictly earlier in the order
(P,t) transitive deps at length >= t:  NONE   (t = 3, 5, 9)
(Q',t) transitive deps at length > t:  NONE   (t = 3, 5, 9)
```

So spare independence at length `t` never depends on anything at length `t` or
above.  The representative switch their §5 wanted at length `t+1` is supplied
by (P_t) — available because (P_t) is proved *before* the commutation half of
its own stage, from strictly lower data.

### 11.5 Bounded-length sufficiency: `t₀ = 2`

Stated in the shape the emission engineer asked for: **given the emitted
family as it stands — no repairs — Lemma X and spare independence hold at all
lengths.**  The emitted base is length two ((P₂), the (St3) block equating all
three spare chains to one canonical right-hand side), the step from `t` to
`t+1` is unconditional for every `t ≥ 2`, and no chain-difference relators are
needed at any length.  So `t₀ = 2` and the chain-difference emission of their
§6 is not required (it remains harmless).

### 11.6 One correction to their §2

(III) is **not** fully closed: their Lemmas 2.1 and 2.2 handle the *ideal*
part of the well-definedness, but the extension from words to `F₂`-sums also
needs repeated monomials to cancel, i.e. `Ê_ij(w)² = 1` — see §8.2, where that
is shown to be missing from the emitted family and not derivable from it.
Their Lemma 2.2 is otherwise correct and is used unchanged.  Note also that
their §2 route to (III) *does* rest on (I) and (II), as they say, so it
inherits the closure proved here.

### 11.7 What their proof got right and is reused

Their §4 (Lemma 4.1, (II) from (I)) is exactly (R_t) here and the argument is
the same.  Their §2 absorption is used unchanged.  Their machine check (MSI
15862151) that the three spare chains agree in `Q` remains the right necessary
screen.  The only thing replaced is Lemma 3.1's hypothesis set.

## Verification addendum (2026-08-15, night — adversarial pass, CONFIRMED)

Every critical step re-derived by hand; six fixes, all incorporated into
the canonical node texts and recorded here:

1. §8.2's counterexample justification was incomplete as written: the
   five lifted Cuntz–Krieger relators must also survive the ℤ-lift.
   They do — `experiments/atlas_relator_rank5_relations.py:86-103` emits
   all of them with explicit `inverse(...)`, hence in sign-correct
   ℤ-form (cuntz = [x(E),x(e)]·x(1)⁻¹ etc.), all true in `L_ℤ(1,2)`.
2. §7's C2 attribution: for genuinely reducing letter pairs the
   identification of the canonical word with `X_mp(c)` comes from the
   emitted CK relators, not from block (C); §2's scope line is §§3–6.
3. §11.1: the corrected transfer hypotheses are not "weaker" — the two
   sets are incomparable; the correct property is that every corrected
   hypothesis concerns strictly shorter objects at roots other than
   `(i,j)`.
4. The third spare index is consumed in FOUR places (§6.2's `(Q′₂)` base
   included), not three.
5. Stale line citations: the (St3) emission block is at
   `atlas_relator_rank5_full_family.py:173-178`; `rank5_word_multi` is
   in the full-family file at `:102-109`, not the dictionary file.
6. The 3,000 → 2,980 emission gap consists only of freely-trivial words
   and exact duplicates (verified by reading `add()`), both lossless.

Independent re-derivations in the pass: both bracket identities; the
(P_t) edge-length table (max t−1, from `1+|u₂| ≤ t−1` since `|v| ≥ 1`);
the 120-root-pair count (380 − 140 ordered → 120 unordered = 60+30+30);
the `Q`-convention `[1+re_ij, 1+se_jk] = 1+rs·e_ik`; the Tomforde
freeness input; and the propagation identity `[α²,β] = δ²`.
