# Thompson's group V plus one involution: an eighteen-relator presentation of L_(F_2)(1,2)^x

Lane `ex-free-objects`, 2026-09-12. Unreviewed.

`L = L_(F_2)(1,2)`, `S[w]`, `T[w]` as in `experiments/nonsofic-certificates/leavitt.py`. A *cone*
is a binary word `alpha`, standing for the clopen set `alpha C`. Maps of `V` are written on the
right, as in Bleak--Quick: `w . (gh) = (w . g) . h`. Write `U_g e_w = e_(w.g)` for the Thompson
unit of `g`; then `psi(g) = U_g^-1` is a homomorphism `V -> L^x`. Commutators are
`[p,q] = p q p^-1 q^-1`, and `{}^g q = g q g^-1`.

## 1. The object

Generators `a, b, c, x`. The relators:

```text
(V)  Bleak--Quick (2.4):   a^2,  b^3,  (ab)^4,  c^-1 (ac)^2 a,
     (c a b^-1 a b a)^2 c b (c a b a b^-1 a)^2,
     a (cb)^2 a (b^-1 c)^2 b c a b c b^-1 c a b^-1 a c b^-1 (cb)^2 a b^-1,
     a b^-1 c b c (a b^-1)^2 c b c b^-1 a (b^-1 c)^2 b a b c b^-1 c a b^-1,
     c a (b^-1 c)^2 b a c a b a c b c (b^-1 c a)^2 b (c b^-1)^2 (a c b)^2 c b^-1 c a b^-1
(X1) x^2
(X2) (a x)^3
(H)  [x, {}^(h_a) a],  [x, {}^(h_b) b],  [x, {}^(h_c) a]
(B)  [x, {}^s x],  [x, {}^p x],  [x, {}^q x]
(C)  [x, {}^r x] = {}^p x
(Q)  {}^(k_0) x . {}^(k_1) x = x
```

with the words

```text
p = b^-1            q = a b^-1 a           r = a b^-1             s = b a b c a b^-1
k_0 = c a b^-1 c a b^-1                    k_1 = c a b c a b
h_a = b^-1 a c b^-1 a b^-1    h_b = b^-1 a b^-1 c a b c    h_c = b^-1 a b^-1 c a b^-1
```

Eighteen relators; total literal length 322 (the (V) block 136), longest 37. Literal words and
checksum: `experiments/nonsofic-certificates/presentations/thompson-steinberg-presentation.json`.

**Images.** `a -> U_(00 01)`, `b -> U_(01 10 11)^-1`, `c -> U_(1 00)`, `x -> 1 + S[00]T[01]`.
Under these images:
- `{}^s x = 1+S[10]T[110]`, `{}^p x = 1+S[00]T[10]`, `{}^q x = 1+S[10]T[01]`,
  `{}^r x = 1+S[01]T[10]`, `{}^(k_0) x = 1+S[000]T[010]`, `{}^(k_1) x = 1+S[001]T[011]`;
- `{}^(h_a) a`, `{}^(h_b) b`, `{}^(h_c) a` are the images of `iota_1(a) = (100 101)`,
  `iota_1(b) = (101 110 111)` and `iota_1(c) = (11 100)`. Here `iota_1(g)` acts as `g` inside
  the cone `1` and trivially on the cone `0`.

**Reading.** `(V)` is Thompson's group. `x` is one elementary transvection. `(H)` says that `x`
commutes with the copy of `V` living on the complementary cone. `(B)` gives three commutations,
`(C)` one Steinberg commutator law, `(Q)` the splitting `S[00]T[01] = S[000]T[010] + S[001]T[011]`,
and `(X2)` the Weyl link `a = x (axa) x`.

**Theorem.** The images define an isomorphism `Q -> L^x`, where `Q` is the presented group.
Hence `Q` is a finitely presented, simple, nonsofic group on four generators with eighteen
relators.

## 2. Proof

`Q` is the presented group, and `phi : Q -> L^x` is given by the images. `phi` exists because all
eighteen relators hold in `L^x` (Section 3). `P` denotes the sixty-relator group of
`leavitt-unit-group-steinberg-weyl-presentation`, and `P = L^x`.

**Step 0 (the V part).** By Bleak--Quick Theorem 2.1 and their statement after it that (2.4) has
the same normal closure as (2.3), `<a,b,c | (V)> = V` with `a,b,c` the maps above. So there is
`nu : V -> Q`. The images satisfy (V), so `rho = phi o nu : V -> L^x` is a homomorphism. It is
nontrivial, and `V` is simple (`thompson-v-finitely-presented-infinite-simple`), so `rho` is
injective. Its image is the group `𝒱` of all Thompson units. Injectivity alone would not give
this, because `V` contains proper copies of itself. It holds because `a, b, c` are Bleak--Quick's
named generators `t_(00,01)`, `t_(01,10) t_(01,11)` and `t_(1,00)` of `V` itself (their Section
2, right action), and `psi(V) = {U_g^-1 : g in V} = 𝒱`. *Consequently a word identity in
`a, b, c` that holds in `L^x` holds in `Q`.* For `g in 𝒱` write `ĝ = nu(rho^-1(g))`.

**Step 1 (leaf transvections are well defined).** Let `(alpha, beta)` be disjoint cones, not
`{0,1}`. Pick `g in 𝒱` with `g S[00] = S[alpha]` and `g S[01] = S[beta]`; one exists, since both
complements are nonempty clopen sets. Put `T(alpha,beta) = ĝ x ĝ^-1`. A second choice `g'` gives
`h = g^-1 g'` fixing `00w` and `01w` for every `w`. So `h` is supported on the cone `1`, and
`h in psi(iota_1(V)) = <psi(iota_1(a)), psi(iota_1(b)), psi(iota_1(c))>`. By Step 0, `ĥ` is a word
in the three elements of (H), all of which commute with `x`. So `T(alpha,beta)` is well defined, and
`phi(T(alpha,beta)) = 1 + S[alpha]T[beta]` (for Thompson units `g^-1 = g*`).

**Step 2 (transport).** If `v in 𝒱` acts by prefix replacement on cones `gamma_1..gamma_n`
(`v S[gamma_j] = S[gamma'_j]`), then `v̂ T(gamma_i w, gamma_j w') v̂^-1 = T(gamma'_i w, gamma'_j w')`.
Given pairwise disjoint `gamma_1..gamma_n` and `gamma'_1..gamma'_n`, each tuple with nonempty
complement, such a `v` exists. So a relation among leaf transvections over one such tuple holds
over every such tuple. Transporting the relators (base cones `00, 01, 10, 110`) gives, for
pairwise disjoint cones with nonempty complement:

```text
(B-dis) [T(al,be), T(ga,de)] = 1       (B-src) [T(al,be), T(al,ga)] = 1
(B-tgt) [T(al,ga), T(be,ga)] = 1       (C11)   [T(al,be), T(be,ga)] = T(al,ga)
(Q)     T(al0,be0) T(al1,be1) = T(al,be)                (X1) T(al,be)^2 = 1
```

**Step 3 (two derived Steinberg laws).** For `d in {0,1}`:
- `(C1d)` `[T(al,be), T(be d, ga)] = T(al d, ga)`. Write `T(al,be) = T(al0,be0) T(al1,be1) = yz`
  and `w = T(be d, ga)`. Then `[yz, w] = y[z,w]y^-1 [y,w]`. Here `[T(al e, be e), w]` is `1` for
  `e != d` (B-dis: four disjoint cones) and `T(al d, ga)` for `e = d` (C11).
  - For `d = 0` this gives `y . 1 . y^-1 . T(al0, ga) = T(al0, ga)`.
  - For `d = 1` it gives `y T(al1, ga) y^-1`. B-dis on the cones `al0, be0, al1, ga` (with `be1`
    in the complement) says that `y` commutes with `T(al1, ga)`, so the result is `T(al1, ga)`.
- `(CEd)` `[T(al, be d), T(be,ga)] = T(al, ga d)`. Write `T(be,ga) = T(be0,ga0) T(be1,ga1) = yz`
  and `w = T(al, be d)`, and use `[w, yz] = [w,y] . y[w,z]y^-1`.
  - For `d = 0`: `[w,y] = T(al,ga0)` (C11) and `[w,z] = 1` (B-dis).
  - For `d = 1`: `[w,y] = 1` (B-dis) and `y[w,z]y^-1 = y T(al,ga1) y^-1`. B-dis on `al, ga1, be0,
    ga0` (with `be1` in the complement) removes the conjugation.

**Step 4 (a homomorphism from P).** Use the chart `d_1..d_5 = 00,01,10,110,111`. Send
`c -> Theta(P_(12345))^`, `t -> a` (`rho(a) = Theta(P_(12))`), and `y_l -> T(d_1 l_s, d_2 l_t)`,
where `(l_s, l_t) = (∅,∅), (0,∅), (1,∅), (∅,0), (∅,1)` for `l = 1, e, f, E, F`. Every permutation
`Theta(P_sigma)` acts by prefix replacement on the chart leaves, so by Step 2
`X_ij(l) -> T(d_i l_s, d_j l_t)`. The sixty relators of `P` map to relations of `Q`:
- (W): `V`-identities (Step 0).
- (K): `Theta(P_(34))` and `Theta(P_(45))` fix the cones `00` and `01` pointwise, so they fix every
  `T(d_1 l_s, d_2 l_t)` (Steps 1-2).
- (L), (D): (X2), (X1).
- (B): disjoint letter pairs by B-dis (four disjoint subcones of `d_1..d_4`); the two
  unit-letter blocks by B-src and B-tgt.
- (C), 13 relators.
  - `(1,1)`, `(1,E)`, `(1,F)`, `(e,1)`, `(f,1)`, `(E,e)`, `(F,f)` are C11. For example
    `[T(d1,d2), T(d2, d3 0)] = T(d1, d3 0)`, and `[T(d1, d2 0), T(d2 0, d3)] = T(d1,d3)`.
  - `(1,e)`, `(1,f)` are C1d.
  - `(E,1)`, `(F,1)` are CEd.
  - `(E,f)`, `(F,e)` are B-dis: the cones `d1, d2 0, d2 1, d3` are disjoint.
- (P), 12 relators. Both sides equal one leaf transvection. For `l, m in {e,f}` use C1d; for
  `l in {e,f}`, `m in {E,F}` use C11; for `l, m in {E,F}` use CEd with
  `ga = d3 m_t`, giving `T(d1, d3 m_t l_t)`, which is `X13(lm)`.
- (Q): C11 twice, then (Q).

So there is a homomorphism `beta : P -> Q`, and `phi o beta` is the isomorphism `P -> L^x`
(checked on generators). Hence `beta` is injective.

**Step 5 (beta is onto).** Let `N <= Q` be generated by all `T(alpha,beta)`.
1. `N <= beta(P)`.
   - `beta(P)` contains `T(d_i l_s, d_j l_t)` for all letters.
   - Induct on suffix lengths: `T(d_i gamma' d, d_j delta) = [T(d_i gamma', d_k), T(d_k d, d_j delta)]`
     (C1d) and `T(d_i gamma, d_j delta' d) = [T(d_i gamma, d_k d), T(d_k, d_j delta')]` (CEd). Both
     reduce to suffix lengths at most `(1,1)`, which are C11 commutators of letter elements.
   - Same-leaf pairs: route through a third leaf by C11.
   - Arbitrary cones: refine by (Q) until each piece lies inside a chart leaf.
2. `N` is normal. For `g in {a,b,c}`, refine `T(alpha,beta)` by (Q) until `rho(g)` acts by prefix
   replacement on every piece, then apply Step 2. Also `x in N`.
3. `Q/N` is generated by the images of `a, b, c` and satisfies (V), so it is a quotient of `V`. By
   (X2), `a^3 in N`, and `a^2 = 1`, so `a in N`. So the quotient map `V -> Q/N` kills `a != 1`.
   Since `V` is simple, `Q/N = 1`.

So `Q = N <= beta(P)`. Then `beta` is an isomorphism, and `phi = (phi o beta) o beta^-1`. QED.

## 3. Verification record

`experiments/nonsofic-certificates/presentations/verify_thompson_steinberg_presentation.py` ran
on MSI with `/usr/bin/python3.11` and the shared `leavitt.py`, in 0.2 s; verdict PASS.
- (2.3) and (2.4) of Bleak--Quick hold in `L^x`, for both orientations of `b`.
- BFS over words in `a, b, b^-1, c` explored 1,217 elements and found all nine conjugators. Each
  predicate `g S[00] = S[alpha]`, `g S[01] = S[beta]` was rechecked in dual mode.
- The three `iota_1` images and six leaf transvections equal their exact targets.
- All eighteen relators are `1` in `L^x`.
- Five negative controls are correctly nontrivial: `(bx)^3`; half a split; a wrong C11
  right-hand side; `[x,a]`; `[x, T(01,10)]`.

The computation certifies only that the relators hold and that the named words have the stated
images. Completeness is Steps 0-5.

## 4. Trust surface

- `leavitt-unit-group-steinberg-weyl-presentation`: the in-repo spare-index theorem and Khanh's
  Theorem 5.4.
- Bleak--Quick Theorem 2.1, and their statement that (2.4) and (2.3) have the same normal closure.
  That statement is a KBMAG computation reported in the published paper. The proof also runs with
  the (2.3) relators, which are Theorem 2.1 itself (verified here too), at total length above 322.
- Simplicity of `V` (Cannon--Floyd--Parry).
