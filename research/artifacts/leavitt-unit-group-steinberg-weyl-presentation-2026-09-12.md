# A seven-generator, sixty-relator presentation of the binary Leavitt unit group

Lane `ex-free-objects`, 2026-09-12. Unreviewed.

`L = L_(F_2)(1,2) = F_2<s0,s1,t0,t1 | t_i s_j = delta_ij, s0t0 + s1t1 = 1>`, `G = L^x`.
Letters `A = {1, e, f, E, F}` stand for `1, s0, s1, t0, t1`. Commutators are
`[x,y] = x y x^-1 y^-1`.

## 1. The presentation

Generators: `c, t, y_1, y_e, y_f, y_E, y_F`. Abbreviations (words in the generators):

```text
X12(a) = y_a                          X23(a) = c y_a c^-1
X34(a) = c^2 y_a c^-2                 X13(a) = t c y_a c^-1 t^-1
X32(a) = c t y_a t^-1 c^-1            X43(a) = c^2 t y_a t^-1 c^-2
X14(a) = c^-1 t c^-1 t y_a t^-1 c t^-1 c
```

Relators, sixty in all:

```text
(W)  5   t^2,  c^5,  (tc)^4,  (t c^-1 t c)^3,  (t c^-2 t c^2)^2
(K) 10   [y_a, c^2 t c^-2],  [y_a, c^-2 t c^2]                     a in A
(L)  1   (t y_1)^3
(D)  1   y_1^2
(B) 17   [X12(a), X34(b)] for the 15 multisets {a,b} in A;  [X12(1), X13(1)];  [X12(1), X32(1)]
(C) 13   [X12(a), X23(b)] = X13(ab)  whenever ab is a letter or 0:
         (1,b) for b in A;  (a,1) for a != 1;  (E,e), (F,f) -> 1;  (E,f), (F,e) -> 0 (relator [X12(a),X23(b)])
(P) 12   [X12(a), X23(b)] = [X14(a), X43(b)]  for the 12 pairs with ab not reducible:
         a in {e,f}, b in {e,f,E,F};  a, b in {E,F}
(Q)  1   [X12(e), X23(E)] [X12(f), X23(F)] = X13(1)
```

Literal words: `experiments/nonsofic-certificates/presentations/st5-weyl-presentation.json`
(total length 1,007; longest relator 38, the (P) family; sha256 of the newline-joined literal
relator list `9e0edd1308179c712525f11b0567a3a256ba21ec2481e8fed1528a4bcbacec9c`).

The images in `G`. Fix the complete prefix code `D = (d_1..d_5) = (00, 01, 10, 110, 111)`
and the ring isomorphism `Theta : M_5(L) -> L`, `Theta(M) = sum_ij S[d_i] M_ij T[d_j]`
(`T[d_i] S[d_j] = delta_ij`, `sum_i S[d_i]T[d_i] = 1`). Then

```text
c   -> Theta(P_(12345)) = the Thompson unit  d_k w -> d_(k+1) w   (indices mod 5)
t   -> Theta(P_(12))    = the Thompson unit swapping the prefixes 00 and 01
y_1 -> 1 + S[00]T[01]    y_e -> 1 + S[000]T[01]    y_f -> 1 + S[001]T[01]
y_E -> 1 + S[00]T[010]   y_F -> 1 + S[00]T[011]
```

with `P_sigma e_j = e_sigma(j)`. So `y_a = Theta(E_12(a))`, and `X_ij(a)` evaluates to
`Theta(E_ij(a)) = 1 + S[d_i] a T[d_j]`.

**Theorem.** The assignment above is an isomorphism `P -> L^x`. Consequently `P` is a
finitely presented simple nonsofic group (`openai-leavitt-unit-nonsofic`,
`binary-leavitt-unit-group-is-simple`).

For scale: the smallest explicit relator list in the graph before this was `T_St` of
`atlas-steinberg-rank-five-translation` (4,648 entries in twelve generators of `A8 * A8`,
X-lengths up to 595, total X-length 713,754 over its 4,612-word family), and it presents a
central extension of `L^x` relative to the atlas, not `L^x` itself. Khanh's Proposition 6.2
presentation has `20(4^195 - 1)/3` generators.

## 2. Proof

Throughout, `P` denotes the presented group. Four steps are pure group theory; one is exact
computation (Section 3); the last two consume two established claims.

### Step 1. The Weyl relators present S_5

Coset enumeration of `<c, t | W>` over the trivial subgroup closes with 120 cosets, so the
group has order at most 120. The permutations `c = (12345)`, `t = (12)` satisfy (W) (`tc = (2345)`
has order 4, `t c^-1 t c = (12)(15)` has order 3, `t c^-2 t c^2 = (12)(45)` has order 2) and
generate `S_5`. So `<c,t | W> = S_5`, and there is a homomorphism `sigma -> p_sigma`,
`S_5 -> P`, with `p_(12345) = c`, `p_(12) = t`.

### Step 2. Symmetry lemma

`c^2 t c^-2 = p_(34)` and `c^-2 t c^2 = p_(45)` generate the pointwise stabilizer
`Sym{3,4,5}` of `{1,2}`. By (K) every `y_a` commutes with it. For a root `(i,j)` put
`X_ij(a) := p_sigma y_a p_sigma^-1` for any `sigma` with `sigma(1) = i`, `sigma(2) = j`: two
choices differ by an element of `Sym{3,4,5}`, so this is well defined, and

```text
p_rho X_ij(a) p_rho^-1 = X_rho(i)rho(j)(a)        for all rho in S_5.      (EQ)
```

The seven abbreviations of Section 1 are instances (their permutations send `(1,2)` to the
named root). A relation among `X`'s involving at most five index variables, holding at one
injective assignment of indices, holds at every injective assignment: conjugate by `p_rho` and
use (EQ), since `S_5` is transitive on injective assignments.

### Step 3. The imposed families at every root

By Step 2, for all pairwise distinct indices:
- (B) `[X_ij(a), X_kl(b)] = 1` for `i,j,k,l` distinct and every ordered pair `(a,b)` (the
  multiset suffices: `rho = (13)(24)` swaps the roots, then invert);
  `[X_ij(1), X_il(1)] = 1`; `[X_ij(1), X_kj(1)] = 1`.
- (C) `[X_ij(a), X_jk(b)] = X_ik(ab)` (or `= 1` if `ab = 0`) for the 13 reducing pairs.
- (P) `[X_ij(a), X_jk(b)] = [X_ij'(a), X_j'k(b)]` for the 12 other pairs, all `j, j' not in {i,k}`
  (impose `j = 2, j' = 4` at root `(1,3)`; `Sym{2,4,5}` fixes the root and permutes spares).
- (Q) `[X_ij(e), X_jk(E)] [X_ij(f), X_jk(F)] = X_ik(1)`.
- (D) `X_ij(1)^2 = 1`.

### Step 4. The remaining commutations

Use only: if `x` commutes with `y` and `z`, it commutes with `[y,z]`. Choose `m` outside the
indices named (five indices leave room). Letters `a, b != 1`.

1. `[X_ij(1), X_il(a)] = 1`: `X_il(a) = [X_im(1), X_ml(a)]` (C); `X_ij(1)` commutes with
   `X_im(1)` (same source, (B)) and `X_ml(a)` (disjoint).
2. `[X_ij(a), X_il(1)] = 1`: `X_ij(a) = [X_im(a), X_mj(1)]` (C); `X_il(1)` commutes with
   `X_im(a)` (item 1) and `X_mj(1)` (disjoint).
3. `[X_ij(a), X_il(b)] = 1`: `X_il(b) = [X_im(1), X_ml(b)]`; `X_ij(a)` commutes with `X_im(1)`
   (item 2) and `X_ml(b)` (disjoint).
4. `[X_ij(1), X_kj(a)] = 1`: `X_kj(a) = [X_km(a), X_mj(1)]`; disjoint, then same target (B).
5. `[X_ij(a), X_kj(1)] = 1`: `X_ij(a) = [X_im(1), X_mj(a)]`; `X_kj(1)` commutes with `X_im(1)`
   (disjoint) and `X_mj(a)` (item 4).
6. `[X_ij(a), X_kj(b)] = 1`: `X_kj(b) = [X_km(b), X_mj(1)]`; disjoint, then item 5.
7. `[X_ij(a), X_ij(b)] = 1` (any `a, b`): `X_ij(b) = [X_im(1), X_mj(b)]`; same source (items
   2 or (B)), then same target (items 4-6 or (B)).

Every pair of roots `(i,j), (k,l)` with `j != k` and `l != i` is equal, same-source,
same-target or disjoint, so the whole (St2) family `(B')` of the spare-index theorem holds.

### Step 5. Involutivity at every letter

For `a != 1` write `delta = X_ij(a) = [alpha, beta]`, `alpha = X_im(1)`, `beta = X_mj(a)`. By
Step 4, `delta` commutes with `alpha`. The identity `[ab, c] = a[b,c]a^-1[a,c]` with `a = b = alpha`
gives `[alpha^2, beta] = alpha delta alpha^-1 delta = delta^2`; `alpha^2 = 1` by (D), so
`delta^2 = 1`.

### Step 6. A homomorphism from St_5(L)

`atlas-steinberg-spare-index-independence` proves `G_0 = St_5(L)` for the group `G_0` on 100
generators `X_ij(a)` with: root commutativity (A), the (St2) family (B'), (St3) with all three
intermediate indices anchored to one right-hand side (C), the Cuntz-Krieger relators (`cuntz`,
`zero`, `partition`), and the involutivity relators. Its proof uses the anchored (St3) family only
through the agreement of the three chains (P_2), never through what the right-hand side is
(`research/artifacts/steinberg-spare-index-2026-08-15.md`, Section 2 and trap 4). Take the
right-hand side of an irreducible pair to be the chain through the least spare index. Then
every relator of `G_0` is one of Steps 3-5: (A) and (B') by Step 4, the anchored family by (C)
and (P), `cuntz`/`zero` inside (C), `partition` = (Q), involutivity by (D) and Step 5. So
`X_ij(a) -> X_ij(a)` defines a homomorphism `psi : St_5(L) = G_0 -> P`.

### Step 7. psi is an isomorphism

- *Surjective.* `y_a = psi(x_12(a))`. Since `X_21(1) = t y_1 t^-1`, the relators (L) and `t^2`
  give `psi(x_12(1) x_21(1) x_12(1)) = y_1 t y_1 t^-1 y_1 = t`. Conjugating by `p_rho` (EQ),
  every `p_(ij)` lies in the image, and `c = p_(12) p_(23) p_(34) p_(45)`.
- *Injective.* The relators hold in `L^x` (Section 3), so the images define `phi : P -> L^x`,
  with `phi(p_sigma) = Theta(P_sigma)` and `phi(X_ij(a)) = Theta(E_ij(a))`. So `phi o psi` agrees
  on the generators `x_ij(a)` (`a in A`) with the canonical map `St_5(L) -> GL_5(L)` followed by
  `Theta`. That composite is an isomorphism by `leavitt-steinberg-map-iso-from-rank-three`
  (Khanh, arXiv:2609.08428v1, Theorem 5.4). Hence `psi` is injective.

So `psi` is an isomorphism and `phi = (phi o psi) o psi^-1` is one too. QED.

Without Theorem 5.4 the argument still gives surjections `St_5(L) ->> P ->> L^x` whose
composite is the canonical map, with kernel `K_2(5,L)`. Theorem 5.4 is exactly what makes both
maps injective, so the identification `P = L^x`, and with it nonsoficity, uses it.

## 3. Verification record

Script `experiments/nonsofic-certificates/presentations/verify_st5_weyl_presentation.py`, run on
MSI (acn, `/usr/bin/python3.11`, shared `leavitt.py` of
`nonsofic-certificates/current`, VERSION `2e9a9873`), 2.4 s, verdict PASS:

- all 60 relators evaluate to `1` in `L^x`, with dual mode on (44,473 products cross-checked
  between the Diamond-lemma normal form and prefix tables);
- HLT coset enumeration of (W): 120 cosets, and the coset table is a permutation representation;
- all 120 BFS words in `c, c^-1, t` evaluate to `Theta(P_sigma)`;
- 600 word checks: `p_sigma y_a p_sigma^-1 = Theta(E_ij(a))` for every root, every one of the six
  permutations sending `(1,2)` to it, and every letter;
- control (redundant with the proof): the full target family at every root holds in `L^x` -
  6,500 (A)+(B') instances, 1,500 (St3) instances (`[E_ij(a), E_jk(b)] = E_ik(ab)`), 60 partition
  instances, 100 squares; zero failures;
- negative controls, all correctly nontrivial: `[X12(e), X21(E)]`, `(t y_e)^3`, `[y_e, p_(23)]`,
  `(tc)^3`, `[X12(e),X23(E)] X13(1)^-1`, and a mismatched (P) relator.

The computation certifies Section 3's inputs only (relators hold; (W) presents `S_5`). The
completeness of the relator list is Steps 2-7, not a computation.

## 4. Trust surface

- `atlas-steinberg-spare-index-independence`: in-repo, adversarially verified 2026-08-15, not
  externally refereed. This is the only nontrivial input to `P = St_5(L)`.
- Khanh Theorem 5.4 (v1 preprint, read in full by the literature lane, not refereed): used only
  for `St_5(L) = GL_5(L)`.
- Nonsoficity of `L^x`: OpenAI chapter Theorem 1.1, and independently the kernel-checked
  `universalLeavittUnits_not_isSofic`.

Novelty check, bounded: repository graph grep (`seven generators`, `sixty relators`, Weyl
presentation, explicit presentation), the Khanh artifact, and one web search on 2026-09-12. None
found an explicit presentation of a nonsofic group with fewer than thousands of relators.
Khanh-Thanh arXiv:2607.10351 gives matrix generators, not relators.

## 5. What is not done, and the next object

- Relator pruning is partial. (A), five of the six same-source/same-target blocks of (B), and
  four squares are derived rather than imposed; (K), (C) and (P) are not pruned.
- Three generators. `L^x` contains Thompson's `V` (2 generators, 7 relators, Bleak-Quick), and
  every `X_ij(a)` is a `V`-conjugate of one leaf transvection `u = 1 + S[00]T[01]`. A
  presentation `<V, u | V-relators, centralizer relators, one relator per V-orbit of cone
  configurations>` should collapse (B) to a handful of relators and (K) to two. Completeness would
  follow from this presentation by Tietze transformations. That is the open claim
  `thompson-steinberg-presentation-of-leavitt-unit-group`.
