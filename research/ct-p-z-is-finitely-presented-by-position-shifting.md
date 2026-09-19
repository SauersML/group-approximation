---
rg: 2
id: ct-p-z-is-finitely-presented-by-position-shifting
kind: claim
title: For every finite set P of odd primes, CT_P(Z) is finitely presented, by an explicit truncation of the Ore tree presentation obtained by position shifting; an elementary answer to Kourovka 17.61 using neither Li nor Bleak-Quick
distinct_from:
  ct-p-z-is-a-one-vertex-k-graph-full-group: that gets F_infinity (hence finite presentation) from Li 2110.04505 and groupoid theory; this proves finite presentation alone, elementarily, from the box model.
  ct-p-z-has-a-finite-class-transposition-presentation: that asks for a truncation of the class-transposition relations (R1)-(R3); this truncates the Ore tree presentation instead. It gives finitely many class transpositions as generators (Tietze), but not relators drawn from (R1)-(R3).
  ct-p-z-has-the-ore-tree-presentation: that is the infinite presentation (Fact O); this is its finite truncation.
artifacts:
  - research/artifacts/gq-bh-pal-kourovka61-coherence-reduction.md
---

**ESTABLISHED** (lane proof, not reviewed; referee requested). Inputs:
- `ct-p-z-has-the-ore-tree-presentation` (Fact O; lane proof; step O1 is written in full in its
  pass-5 section);
- `piecewise-canonical-permutations-are-transposition-products` (`PC = CT_P(Z)`; lane proof).

No theorem of Li, Matui, Farsi–Kumjian–Pask–Sims or Bleak–Quick is used.

**Credit.** The position-shifting technique is Cannon–Floyd–Parry's for `F` and `V`, Brin's for
`2V`, and Hennig–Matucci's for `nV` (arXiv 1105.3714, §7, read at source). Here it is adapted to
colours of different arities. Martínez-Pérez–Matucci–Nucinkis (arXiv 1609.07058, Thm `fp`) prove
finite presentation for all valid, bounded, complete Cantor algebras. Given the identification
recorded in `ct-p-z-has-a-finite-class-transposition-presentation`, which was not checked, that
covers `CT_P(Z)` too. No priority is claimed.

## Statement

Let `P` be a finite set of odd primes and `P' = P ∪ {2}`. Then `CT_P(Z)` is finitely presented.
Explicitly, it has a presentation with at most `4|P| + 6` generators, listed in §3. The relators
are finitely many instances of the Fact O relations (listed in §3), rewritten through the shift
definitions (D). By Tietze moves, `CT_P(Z)` also has a finite presentation whose generators are
finitely many class transpositions.

## 1. Comb coordinates

Write `c_i = (2^{i−1} − 1)(2^i)` for `i ≥ 1` and `ℓ_n = (2^{n−1} − 1)(2^{n−1})` for `n ≥ 1`. So
`ℓ_1 = Z`, `c_1 = 0(2)`, `c_2 = 1(4)`, and `ℓ_n = c_n ⊔ ℓ_{n+1}` is the 2-split. The *comb*
`B_n = (c_1, …, c_{n−1}, ℓ_n)` is an ordered natural basis of size `n`, and `ℓ_n` is its *tail*.

**Convention (referee precision 1).** Products of permutations are compositions of functions:
`gh` means "apply `h` first". Under this convention the FC form `g^{−1} h g = h^{+δ(g)}` below is
the true identity in `PC`. Under the opposite convention every FC relator reads `g h g^{−1}`.

For ordered bases `b, b'` of equal size, `[b → b'] ∈ PC` maps `b_k` onto `b'_k` canonically. For
a generator `e: n → n'` of the Ore category `𝒞` of Fact O (a split `x_{n,i,p}` or a permutation),
put `ê := [B_{n'} → B_n·e]`, where `B_n·e` is the realization of `e` applied to `B_n`. The comb
paths form a spanning tree, so by Fact O (step O4, vertex group of a presented groupoid) `PC` is
presented as follows:
- generators: all `ê`;
- relations: the tree edges `x̂_{n,n,2} = 1`, and every instance of (a)–(d) at every object,
  translated by `e ↦ ê`.

Adjacent transpositions `s_k = (k k+1)` generate each `Sym(n)`, with the Coxeter relations as
(a). General naturality instances follow from those for the `s_k`, because naturality is
multiplicative, and one fixed word is chosen for each induced permutation (any two choices agree
by (a)).

**Stabilization.** Let `i < n`. The (b)-instance "split cell `i` by `p`, then split the tail by 2"
reads `x̂_{n,i,p} = x̂_{n+1,i,p}` once tree edges are 1. Likewise the (d)-instance of `s_k`
(`k ≤ n−2`) with the tail split reads `ŝ_k^{(n)} = ŝ_k^{(n+1)}`. After these Tietze moves the
generators are:
- `X_{i,p}` (`i ≥ 1`, `p ∈ P'`): identity on `c_1, …, c_{i−1}`; it maps `c_i, …, c_{i+p−1}` onto
  the `p` children of `c_i`, and `c_{i+p−1+k} ↦ c_{i+k}`, `ℓ_{m+p−1} ↦ ℓ_m`, all canonically;
- `π_k = τ_{c_k, c_{k+1}}` (`k ≥ 1`), a class transposition;
- `Y_{n,p}` (`n ≥ 1`, `p` odd): identity on `c_1, …, c_{n−1}`; it maps `c_n, …, c_{n+p−2}, ℓ_{n+p−1}`
  onto the `p` children of `ℓ_n` (the tail split; `Y_{n,2} = 1` is a tree edge);
- `ρ_n = τ_{c_{n−1}, ℓ_n}` (`n ≥ 2`), a class transposition.

The *position* is `i` for `X_{i,p}` and `π_i`, `n` for `Y_{n,p}`, and `n − 1` for `ρ_n`. `X` and
`π` are *finite* types, of width `w = 1, 2` and shift `δ = p − 1, 0`. `Y` and `ρ` are *tail*
types.

## 2. Every relation is a far commutation or a window

Write `FC(g; h)` for `g^{−1} h g = h^{+δ(g)}`, where `g` is of finite type, `h` is any generator
with `pos(h) ≥ pos(g) + w(g)`, and `h^{+δ}` is `h` with its index raised by `δ`. The translated
relations at object `n` fall into three classes:
- **FC:**
  - (b) for cells `i < j`: `FC(X_{i,p}; X_{j,q})`, or `FC(X_{i,p}; Y_{n,q})` when `j = n`;
  - (d) for `s_k` and a split of cell `i < k`: `FC(X_{i,p}; π_k)`, or `FC(X_{i,p}; ρ_n)` when
    `k = n−1`;
  - (d) for `i > k + 1`: `FC(π_k; X_{i,p})`, or `FC(π_k; Y_{n,p})` when `i = n`;
  - (a) for `(s_k s_l)^2`, `l ≥ k+2`: `FC(π_k; π_l)`, or `FC(π_k; ρ_n)`.

  Each is a correct instance in both directions of the table. For example, splitting cell `i` by
  `p` raises the index of every cell `> i` by `p − 1`, which is `δ(X_{i,p})`.
- **Left windows `W(i)`:** words in stable generators whose positions all lie in `[i, i + C]`,
  with `C = max pq + 1`:
  - `s_k^2`, `(s_k s_{k+1})^3` with `k + 1 ≤ n − 2`;
  - (c) at a cell `i < n` (its `pq` grandchildren sit at positions `i, …, i+pq−1`, below the new
    tail);
  - (d) for `s_k` with a split of cell `k` or `k + 1 < n`.
- **End windows `E(n)`:** words that involve tail generators and whose positions lie in
  `[n − 2, n + C]`:
  - `ρ_n^2`, `(π_{n−2} ρ_n)^3`;
  - (c) at the tail;
  - (d) for `s_{n−1}` with a split of cell `n−1` or `n`;
  - the tree relations `Y_{n,2} = 1`.

Every relation of (a)–(d) involves one cell cluster (a window) or two clusters, and a two-cluster
relation is one of the FC forms listed. The instances are uniform in the cells, so `W(i+1)` is
`W(i)` with every index raised by 1, and `E(n+1)` is `E(n)` raised by 1.

**The shift.** Put `s := X_{1,2}`. `FC(s; h)`, i.e. `s^{−1} h s = h^{+1}` for `pos(h) ≥ 2`, is an
instance of (b) or (d) with `i = 1`, `p = 2`.

## 3. The truncation

**Generators (finite).** `X_{1,p}`, `X_{2,p}` (`p ∈ P'`, including `s = X_{1,2}`), `π_1`, `π_2`,
`Y_{1,p}`, `Y_{2,p}` (`p ∈ P`), `ρ_2`, `ρ_3`: every generator of position 1 or 2.

**Definitions (D).** For every type and every position `j ≥ 3`, the generator of position `j` is
`s^{−(j−2)} g_2 s^{j−2}`, where `g_2` is the generator of that type at position 2.

**Relators (finite).**
- (F) `FC(g; h)` for `g` of finite type with `pos(g) ∈ {1, 2}`, `g ≠ s`, and
  `pos(h) ∈ {pos g + w(g), pos g + w(g) + 1}`, for all types of `h`. This includes
  `FC(X_{2,2}; h)` for `pos(h) ∈ {3, 4}`, which Lemma FC uses.
- (W) All left windows `W(1)`, `W(2)`.
- (E) All end windows `E(n)` with `n ≤ 4`.

There are finitely many relators, since `P` is finite. Each is an instance of a Fact O relation, so
it holds in `PC`. With (D), the generators generate `PC`.

**Lemma FC.** In any group containing elements `g_{υ,j}` that satisfy (D), the relations (F)
imply `FC(g; h)` for every `g` of finite type and every `h` with `pos(h) ≥ pos(g) + w(g)`.

*Proof.* Write `FC(τ,i; υ,j)` for the instance with `g` of type `τ` at position `i` and `h` of
type `υ` at position `j`.
- **Step A (reduce to `i ≤ 2`).** For `i ≥ 3`, (D) gives
  `FC(τ,i; υ,j) = s^{−(i−2)} FC(τ,2; υ,j−i+2) s^{i−2}`, because every generator involved has
  position `≥ 2`. For `i = 1`, `τ = s`, the statement is (D) itself.
- **Step B (induction on `j`, for `i ∈ {1,2}`).** Let `j ≥ i + w + 2`, where `w = w(τ)` and
  `δ = δ(τ)`. Put `u = X_{j−2,2}`.
  1. `FC(u; g_{υ,j−1})` holds by Step A and (F) at `(2; 3)`, since `j − 2 ≥ 2`. So
     `g_{υ,j} = u^{−1} g_{υ,j−1} u`.
  2. By induction on `j`, `FC(τ,i; X_2, j−2)` gives `u g_{τ,i} = g_{τ,i} u'`, where
     `u' = X_{j−2+δ,2}`.
  3. So `g_{τ,i}^{−1} g_{υ,j} g_{τ,i} = u'^{−1} (g_{τ,i}^{−1} g_{υ,j−1} g_{τ,i}) u'`.
  4. By induction this is `u'^{−1} g_{υ,j−1+δ} u'`.
  5. By Step A and (F) at `(2; 3)`, that equals `g_{υ,j+δ}`. ∎

**Theorem.** `⟨generators | (F), (W), (E)⟩`, with (D) read as abbreviations, is a presentation of
`PC = CT_P(Z)`.

*Proof.* The relators hold in `PC`, and the generators generate. It remains to derive every
relation of §1.
- The stabilization and tree relations were used as definitions, or they are `E`-relators.
- FC relations follow by Lemma FC.
- For `i ≥ 3`, `W(i) = s^{−(i−2)} W(2) s^{i−2}` by (D).
- For `n ≥ 5`, every position in `E(n−1)` is `≥ n − 3 ≥ 2`, so `E(n) = s^{−1} E(n−1) s` by (D). By
  induction every `E(n)` follows from (E).
- By Fact O the relations of §1 present `PC`. ∎

**Class-transposition generators.** `PC = CT_P(Z)` is generated by class transpositions. Writing
each of the finitely many generators above as a product of class transpositions and applying
Tietze moves gives a finite presentation whose generators are finitely many class transpositions.
The relators are arbitrary words, not instances of (R1)–(R3).

## 4. Scope and what is still open

- **Where finiteness of `P` is used.** Only in §2–3: finitely many colours give finitely many types
  and window families, and window widths are bounded by `max pq`. Fact O holds for every `P`.
- **Kourovka 17.61.** Combined with `PC = CT_P(Z)`, this answers 17.61 positively. The proof is
  elementary modulo two standard groupoid facts used in Fact O (step O4). It needs neither Li
  nor Bleak–Quick.
- **Still OPEN:**
  - the stronger truncation in which the relators are bounded-modulus instances of (R1)–(R3)
    (`ct-p-z-has-a-finite-class-transposition-presentation`). It would follow from injectivity
    of the transposition presentation (conditional on the `V` case) together with a
    depth-reduction lemma for (R2);
  - an explicit relator count;
  - a referee pass on Fact O's step O1 and on the window classification of §2.

## Lesson for general BH

For a full group of a box-type Cantor algebra with finitely many colours, finite presentation is
cheap once the Ore tree presentation is valid:
- one binary split `s = X_{1,2}` raises every position by 1;
- every relation is a far commutation or a bounded window;
- the CFP/Brin induction (Lemma FC) reduces the far commutations to those at positions 1–2.

The only place finiteness of the colour set enters is the number and width of the colour-exchange
windows. No Morse theory is needed: the hard part of MMN's general theorem is validity for general
laws, and for boxes validity is the CRT restriction lemma.

For BH hosts: an explicit host built as a group of piecewise-canonical maps over finitely many
arities is finitely presented by a finite check of validity and windows. The routing and
simplicity arguments can then be layered on top without any groupoid homology.

## Referee (ref-k1761, 2026-09-19): PASS, with two precisions

This is an independent adversarial check of 262cbb354f, covering the three items the author asked
for. The verdict rests on the unreviewed input `piecewise-canonical-permutations-are-transposition-products`
(`PC = CT_P(Z)`). Its Lemma 1 is the one used in Fact O, step O3, and reads correctly. The rest
of that node was not refereed.

- **§1, generators: correct.**
  - `B_n` is the comb: `ℓ_n = c_n ⊔ ℓ_{n+1}` is the 2-split, in child order.
  - `X_{i,p}`, `π_k`, `Y_{n,p}` and `ρ_n` are the stated maps. They follow from
    `ê = [B_{n'} → B_n·e]`.
  - The two stabilizations are exact (b)/(d) instances once the tree edges `x̂_{m,m,2}` are 1:
    - `x_{n,i,p} x_{n+p−1,n+p−1,2} = x_{n,n,2} x_{n+1,i,p}` for `i < n`;
    - the same with `s_k`, `k ≤ n−2`.
  - Every `ê` is one of the stable generators or a tree edge.
- **§2, classification: complete and correct.** I rechecked every relation type.
  - (a) Coxeter relations `s_k^2`, `(s_k s_{k+1})^3` and `(s_k s_l)^2`: the first two are
    windows `W(k)` or `E(n)`, according to whether `k+1 = n−1`. The third is
    `FC(π_k; π_l)` or `FC(π_k; ρ_n)`.
  - (b) with `i < j`: this is `FC(X_{i,p}; X_{j,q})`. If `j = n` it is `FC(X_{i,p}; Y_{n,q})`
    for odd `q`, or the stabilization for `q = 2`.
  - (c) at a cell `i < n`: every generator has position in `[i, i+pq]`, and no tail generator
    occurs, because the tail sits at `n+pq−1 > i+pq−1`. So this is `W(i)`. At the tail it is
    `E(n)`.
  - (d) for `s_k` with a split of cell `i`:
    - `i < k` gives `FC(X; π_k/ρ_n)`;
    - `i > k+1` gives `FC(π_k; X/Y)`, or the stabilization when `i = n` and `p = 2`;
    - `i ∈ {k, k+1}` gives `W(k)` if `k ≤ n−2`, else `E(n)`.

  In each case the width condition `pos(h) ≥ pos(g)+w(g)` holds. `W(i+1)` and `E(n+1)` are the
  index-raised `W(i)` and `E(n)`, because the local cell patterns do not depend on `n`.
- **Lemma FC: correct.**
  - Step A: when `i ≥ 3`, (D) turns `FC(τ,i;υ,j)` into `FC(τ,2;υ,j−i+2)` conjugated by
    `s^{i−2}`. All positions involved are `≥ 2`, and `j−i+2 ≥ 3`.
  - Step B: steps 1 and 5 use only the base relator `FC(X_{2,2}; ·, 3)` through Step A. Here
    `j−2 ≥ 2` and `j−2+δ ≥ 2`, so there is no circularity.
  - Step 2 uses the induction hypothesis at `j−2 ≥ i+w`, over all types, including `X_{·,2}`.
  - Step 4 uses it at `j−1`.
  - The base cases are exactly (F) at `pos(h) ∈ {i+w, i+w+1}`, for all types of `h`.
- **Theorem: correct.**
  - The relators hold in `PC`, and (D) holds in `PC` by `FC(s;·)`.
  - `W(i)` for `i ≥ 3` is `s^{−(i−2)}W(2)s^{i−2}`, since all positions in `W(2)` are `≥ 2`.
  - `E(n)` for `n ≥ 5` is `s^{−1}E(n−1)s`, since the positions in `E(n−1)` are `≥ n−3 ≥ 2`.
    `E(1..4)` are included.
  - The generator count `2(|P|+1) + 2 + 2|P| + 2 = 4|P| + 6` is right.
- **Precision 1: composition convention.** Read `gh` as "apply `h` first". Under that reading
  the FC form `g^{−1}hg = h^{+δ(g)}` is the true identity in `PC`. I checked
  `X_{1,2}^{−1} π_j X_{1,2} = π_{j+1}` and `X_{i,p}^{−1} X_{j,q} X_{i,p} = X_{j+p−1,q}` directly.
  Under the other convention every FC relator must be written `g h g^{−1}`. State the
  convention in §1.
- **Precision 2: credit, not inputs.** The proof consumes neither CFP, Brin, Hennig–Matucci §7 nor
  Martínez-Pérez–Matucci–Nucinkis. It is self-contained, and Lemma FC was checked directly, so I
  did not read those sources for correctness.

**Status:** it is correct that CT_P(Z) is finitely presented, conditional only on
`PC = CT_P(Z)`. Two items are still open, as the node says:
- the truncation of (R1)–(R3);
- an explicit relator count.
