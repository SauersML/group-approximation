---
rg: 2
id: kms-hc1-a2-pro-p-completion-is-iwahori-criterion-proof
kind: route
title: Vertex restriction, the certification lemma and the Iwahori completion of the A~2 root-word quotient
target: kms-hc1-a2-pro-p-completion-is-iwahori-criterion
requires: []
---

Conventions: `p` is an odd prime, `[x,y]=x^-1y^-1xy`, and commutators are
left-normed. `Gamma=Gamma^A2_p` is the group from
`kms-hc1-root-word-infinite-in-a2-quotient`. All cohomology has `F_p`
coefficients, and for profinite groups it is continuous cohomology.
`r(G)=dim H^2(G)`. `Gamma^` is the pro-p completion of `Gamma`. `P_k` is the
lower p-central series, `P_1=G` and `P_{k+1}=[P_k,G]P_k^p`, for discrete and
for pro-p groups. `gr_k(G)=dim P_k/P_{k+1}`. `Q_k=I_1/P_k(I_1)`.

## 1. The map (D)

**Homomorphism.** Put `A=x_12(1)`, `B=x_23(1)` and `C=x_31(t)`. Each has order
`p`. `[A,B]=x_13(+-1)` commutes with `A` and `B`. `[B,C]=x_21(+-t)` commutes
with `B` and `C`, because `E_21E_23=E_23E_21=E_21E_31=E_31E_21=0`.
`[C,A]=x_32(+-t)` commutes with `C` and `A`, for the same reason. So every
relator holds and `phi` is a homomorphism. `<A,B>`, `<B,C>` and `<C,A>` are
Heisenberg groups of order `p^3` (exponent `p` since `p` is odd), so `phi` is
injective on each vertex group `U_v`.

**phi kills w_p.** `phi(r)=I+uE_13` and `phi(s)=I+vtE_21`, with `u,v` in
`{+-1}`. So `phi(rs)=I+N` with `N=uE_13+vtE_21`, because `E_13E_21=0`. Then
`N^2=uvt E_23` and `N^3=0`, so `(I+N)^p=I+pN+binom(p,2)N^2=I`.

**Filtration.** Give `t^m E_ij` (with `i!=j`) and `t^m h`, for `h` diagonal
traceless, the height `3m+(j-i)`. Put `U_{>=k}` equal to the elements of `I_1`
congruent to `I` modulo height `>=k`. Then
`[U_{>=i},U_{>=j}] <= U_{>=i+j}` and `U_{>=i}^p <= U_{>=pi} <= U_{>=i+1}`. So
the lower p-series `P_k(I_1)` lies in `U_{>=k}`. The graded pieces are the
height-`k` parts of `n^+ + t sl_3[t]`. Their dimensions are `3,3,2`
repeating: `{E_12,E_23,tE_31}`, then `{E_13,tE_21,tE_32}`, then `t h`. The group
commutator induces the Lie bracket. For odd `p`, `gr` is generated in degree
1, as the following brackets show:

- `[t^m h_12, E_12]=2t^m E_12`, `[t^m h_23, E_23]=2t^m E_23` and
  `[t^m h_13, tE_31]=-2t^{m+1}E_31`;
- `[t^m E_12,E_23]=t^m E_13`, `[t^m E_23,tE_31]=t^{m+1}E_21` and
  `[t^{m+1}E_31,E_12]=t^{m+1}E_32`;
- `[t^m E_13,tE_31]=t^{m+1}h_13` and `[t^{m+1}E_21,E_12]=t^{m+1}(E_22-E_11)`.

The last two span `t^{m+1}h`. Here `h_ij=E_ii-E_jj`. The first bullet is used
for `m>=1`, and the other two for `m>=0`.

By induction on `j`, `U_{>=j} <= P_j U_{>=j+1}`, as follows. Generation in
degree 1 gives
`U_{>=j+1} <= [U_{>=j},U_{>=1}]U_{>=j+2} <= [P_jU_{>=j+1},I_1]U_{>=j+2} <= P_{j+1}U_{>=j+2}`.
Chaining these inclusions gives `U_{>=j} <= P_j U_{>=N}` for every `N`. The
`U_{>=N}` form a base of neighbourhoods of `1`, and `P_j` is closed. So
`P_k(I_1)=U_{>=k}`, and `gr_k(I_1)` is `3,3,2` repeating. In particular
`d(I_1)=3`. `phi(Gamma)` maps onto `I_1/Phi(I_1)`, so it is dense and
`phi^: Gamma^ -> I_1` is onto.

## 2. Lemma A: `H^2(Gamma^) -> H^2(Gamma)` is injective

A class `chi` in `H^2(Gamma^)` is a continuous central extension
`1 -> F_p -> E -> Gamma^ -> 1` with `E` pro-p. Suppose its pullback to `Gamma`
splits. Then there is a homomorphism `s: Gamma -> E` lifting
`Gamma -> Gamma^`. Since `E` is pro-p, `s` extends to a continuous
`s^: Gamma^ -> E`. Its composite with `E -> Gamma^` is the identity on the
dense subgroup `Gamma`, so it is the identity everywhere, and `chi=0`.

## 3. Lemma B: `H^2(Gamma)` embeds in `+_v H^2(U_v)`, and `r(Gamma)=9`

`Gamma` is the fundamental group of a triangle of groups with vertex groups
`U_ab`, `U_bc` and `U_ca`, edge groups `<a>`, `<b>` and `<c>`, and a trivial
face group. In each Heisenberg vertex group, the two edge groups meet in the
link with girth 6 (angle `pi/3`). So the triangle of groups is nonpositively
curved and developable, with a CAT(0), hence contractible, development `X`
(Gersten--Stallings; Bridson--Haefliger II.12). `Gamma` acts on `X` without
inversions and with the triangle as a strict fundamental domain. The
equivariant spectral sequence (Brown, VII.7) is

```text
E_1^{q,r} = +_{sigma in Sigma_q} H^r(Gamma_sigma)  =>  H^{q+r}(Gamma).
```

Here there are 3 vertices, 3 edges and 1 face. `E_1^{2,r}=0` for `r>=1`, and
`E_2^{q,0}` is the cohomology of a triangle, so `E_2^{1,0}=E_2^{2,0}=0`.

- **`E_2^{1,1}=0`.** Restriction `H^1(U_ab) -> H^1(<a>)+H^1(<b>)` is an
  isomorphism `F_p^2 -> F_p^2`. So `d_1: F_p^6 -> F_p^3` is onto and
  `E_2^{1,1}=0`.
- **`E_2^{0,2}` has dimension 9.** `dim H^2(U_v)=d(U_v)+d(M(U_v))=2+2=4`. The
  Bockstein of the dual basis of `H^1(U_ab)` restricts to generators of
  `H^2(<a>)` and `H^2(<b>)`. So `d_1: F_p^12 -> F_p^3` is onto, and
  `E_2^{0,2}=ker d_1` has dimension 9.

Every differential out of `E^{0,2}` lands in a zero group. So
`H^2(Gamma)=E_infty^{0,2}=E_2^{0,2}`, which gives the embedding and
`r(Gamma)=9`. By Lemma A, `r(Gamma^)<=9`.

## 4. The criterion (R)

**(1) implies (2).** If `phi^` is an isomorphism, the restriction
`H^2(I_1) -> +_v H^2(U_v)` equals `H^2(Gamma^) -> H^2(Gamma) -> +_v H^2(U_v)`.
That composite is injective by Lemmas A and B.

**(2) implies (1).** Let `K=ker phi^`. The five-term sequence of
`1 -> K -> Gamma^ -> I_1 -> 1` is

```text
0 -> H^1(I_1) -> H^1(Gamma^) -> H^1(K)^{Gamma^} -> H^2(I_1) -> H^2(Gamma^).
```

The first map is an isomorphism `F_p^3 -> F_p^3`. So `H^1(K)^{Gamma^}` is
the kernel of inflation `H^2(I_1) -> H^2(Gamma^)`. Composing inflation with
`H^2(Gamma^) -> H^2(Gamma) -> +_v H^2(U_v)` gives the restriction along
`phi|U_v`, which is injective by (2). So `H^1(K)^{Gamma^}=0`. If `K!=1`, then
`H^1(K)=Hom(K,F_p)` is a nonzero discrete `F_p`-module for the pro-p group
`Gamma^`, and so it has nonzero fixed points. Hence `K=1`.

**(1) is equivalent to (3).** `phi` maps `P_k(Gamma)` into `P_k(I_1)` and
induces surjections `Gamma/P_k(Gamma) -> Q_k`. The `P_k` are open and form a
base in both `Gamma^` and `I_1`. So (3) makes every level an isomorphism,
and then the inverse limit is an isomorphism. The converse is immediate.

**Consequence.** If (R) holds and `Gamma -> Q` is onto a finite p-group, the
map extends to `Gamma^ = I_1` and factors through `phi`. So it kills `w_p`.
Since `w_p!=1` in `Gamma` (`kms-hc1-root-word-infinite-in-a2-quotient`), (R)
also implies that `Gamma^A2_p` is not residually p.

## 5. Lemma C (certification) and the reduction to `r(I_1)<=9`

**Lemma C.** Suppose, for some `j>=2`:

- inflation `H^2(Q_j) -> H^2(I_1)` is onto; and
- `|Gamma/P_{j+1}(Gamma)|=|Q_{j+1}|`.

Then `phi^` is an isomorphism.

*Proof.* Suppose `K=ker phi^ != 1`. Then `M=[K,Gamma^]K^p` is a proper closed
normal subgroup of `K`, and there is a closed normal subgroup `M'` of
`Gamma^` with `M <= M' < K` and `K/M'=F_p` central in `E=Gamma^/M'`. The
central extension `1 -> F_p -> E -> I_1 -> 1` does not split. A split `E`
would be `I_1 x F_p`, which has `d=4`, while `E` is a quotient of `Gamma^`
and so has `d<=3`. Its class `chi!=0` is inflated from a class of `Q_j`. So
`E` is the fibre product `I_1 x_{Q_j} Et` for a central extension
`1 -> F_p -> Et -> Q_j -> 1`.

`Et` is a finite p-group of p-class `<=j`. The projection `E -> Et` is onto
and sends the central `F_p` injectively. The composite `Gamma -> E -> Et` is
onto, so it factors through `Gamma/P_{j+1}(Gamma)`. By the second hypothesis,
`phi` identifies that group with `Q_{j+1}`. So `Gamma -> Et` equals
`psi o phi` for some `psi: Q_{j+1} -> Et`. By density, `Gamma^ -> Et` equals
`psi o phi^ mod P_{j+1}`, which kills `K`. But `K` maps onto the central
`F_p` of `Et`. This is a contradiction.

**Kernel of inflation.** For `k>=2`, the five-term sequence of
`1 -> P_k(I_1) -> I_1 -> Q_k -> 1` has an isomorphism on `H^1`. So
`ker(H^2(Q_k) -> H^2(I_1))` is `Hom(P_k/[P_k,I_1]P_k^p, F_p)`, which has
dimension `gr_k(I_1)`. So

```text
img_k := dim H^2(Q_k) - gr_k(I_1) = 3 + #invariants of M(Q_k) - gr_k
```

is the dimension of the image of inflation from `Q_k`. The images are nested
and exhaust `H^2(I_1)`, so `r(I_1)=sup_k img_k`.

**Computing `img_k`.** Put `Q_k=F/R_k` with `F` free of rank 3. Because
`H_1(F)->H_1(Q_k)` is an isomorphism, `R_k/[R_k,F]R_k^p = H_2(Q_k,F_p)`.
While the towers agree, `Q_k=Gamma/P_k(Gamma)` and `R_k=R_Gamma P_k(F)`.
Since `[P_k(F),F]P_k(F)^p <= P_{k+1}(F)`, the covering group
`F/[R_k,F]R_k^p` is the class-`k` p-quotient of
`F/[R_Gamma,F]R_Gamma^p`. That quotient is presented by `[r,x]` and `r^p`
for the nine relators `r` and `x=a,b,c`. `mu.g` compares its order with
`|Q_k|` and `|Q_{k+1}|`.
Results (`mu.out`):

- `dim H^2(Q_k)` is 6 at `k=2`;
- for `k>=3` it is `11,12,12` according to `k mod 3`;
- `img_2=3`;
- `img_k=9` for `3<=k<=16` (`p=5`), `3<=k<=12` (`p=7`) and `3<=k<=8`
  (`p=11,13`).

On the `Gamma` side, `img_k<=r(Gamma^)<=9` automatically. The relators lie in
`P_3(F)`, so `img_3=9` is expected. Beyond `k=3` the table is only a
cross-check of the towers.

**Reduction.** Let `p` be `5`, `7`, `11` or `13`. For each of these the
towers agree through class 4, which is all the argument uses. The following
are equivalent:

- (R), i.e. `phi^` is an isomorphism;
- `r(I_1)<=9`;
- inflation `H^2(Q_3)->H^2(I_1)` is onto, where `Q_3=I_1/U_{>=3}` has order
  `p^6`.

The argument:

- *First implies second.* If `phi^` is an isomorphism, then
  `r(I_1)=r(Gamma^)<=9` by Lemmas A and B.
- *Second and third are equivalent.* Since
  `Q_4(Gamma)=Q_4(I_1)`, `img_3(I_1)=img_3(Gamma)=9`. So `r(I_1)>=9`, with
  equality exactly when inflation from `Q_3` is onto.
- *Third implies first.* The towers give `|Gamma/P_4|=|Q_4|`, so Lemma C
  applies with `j=3`.

`r(I_1)` is finite by CLR Theorem 0.1. Because the towers agree through class
31 for `p=5,7`, `img_k(I_1)=img_k(Gamma)=9` for `k<=30`. So for these primes
any minimal relation of `I_1` beyond nine has p-central degree `>=31`.

**Corollary (`p=3`): the pro-3 Iwahori needs at least ten relations.** Let
`I_1` be the pro-3 Iwahori of `SL_3(F_3[[t]])`. Then `dim H^2(I_1,F_3)>=10`,
and it may be infinite. So no pro-3 presentation of `I_1` on its three
generators has nine relations. The value `9` is the formal `A~2` case
of CLR's bound. It fails at `q=3`, below CLR's threshold `q>=4`.

*Proof.* For `p=3` the tower agrees with `I_1` through class 5 (`pqA2.out`,
increments `3,3,2,3,3`). So `Q_k(Gamma)=Q_k(I_1)` for `k<=6`. `mu3.out` gives
`img_3=11-2=9`. Suppose `r(I_1)<=9`. Then `r(I_1)=9` and inflation from `Q_3`
is onto. Lemma C with `j=3`, which holds for every odd `p`, then makes `phi^`
an isomorphism. But the `p=3` tower leaves the `I_1` pattern at class 6 (the
increment is 8, not 2), so `phi^` is not an isomorphism. This is a
contradiction.

## 6. Congruence form (K)

`phi(Gamma)` is the group `U_+` generated by the positive real root groups of
`SL_3(F_p[t,t^-1])`. Every positive real root of height `>=2` is a sum of two
positive real roots `alpha+beta` with `[x_alpha(1),x_beta(1)]=x_{alpha+beta}(+-1)`
exactly. For example, `[I+t^aE_13, I+t^bE_32]=I+t^{a+b}E_12` since
`E_32E_13=0`, and the other types are similar. So the three simple root
elements generate all positive real root groups over `F_p`.

CLR (arXiv:1508.00526, section 3.3, citing Rémy--Ronan Theorem 1.C) identify
`I_1` with the closure of `U_+`. Their Key Lemma, `I_1=(G(F_p[t]) cap I_1)^_p`,
uses only CSP for `G(F_p[t])`. That holds for `SL_3` (Bass--Milnor--Serre),
and any metaplectic kernel has order prime to `p`. With `U_+` taken as
`SL_3(F_p[t]) cap I_1`, as in CLR, `U_+^_p=I_1`. A surjection `Gamma -> U_+`
with kernel `N` induces `Gamma^ -> U_+^_p` with kernel the closure of the
image of `N`. So (R) holds iff `N` lies in every normal subgroup of `Gamma`
of p-power index. `N` is never trivial, since `w_p` lies in `N`.

The Devillers--Mühlherr amalgam theorem would present `U_+` as the amalgam of
its rank-2 root subgroups. That amalgam is exactly `Gamma`, so it would give
`N=1`, which is false. The theorem needs a 3-spherical diagram and `q>=16`,
and `A~2` fails the first condition. This is why CLR's upper bound
`r(P)<=(a^2(l+1)^2+3a(l+1))/2` covers only type `A_l` with `l>=3`. Formally,
`l=2`, `a=1` gives 9, which equals `r(Gamma)`.

**Unverified remark.** `X` should be the universal cover of the opposite
complex `Opp(c_+)` of the twin building, so `N=pi_1(Opp)`. This is not used
above.

## 7. Computations

The following are in `experiments/kms-hc1-cross-char-reps-2026-09-17`.

- **Towers.** `pqdeep2.out` (and `pqdeep3.out` for the deeper runs) records
  `|Gamma/P_31|=p^80` with increments `3,3,2` repeating, for `p=5,7`. The
  `p=3` tower deviates at class 6. `pqdeep3.out` also records the same
  pattern for `p=11` through class 24 and for `p=13` through class 20. The
  attempts at `p=5` class 50 and `p=11` class 40 hit the time limit.
- **Serre centre.** `serre_center.out` records the height-`3p` Serre centre.
- **Multiplier check.** `mu.g` and `mu.out` record `dim H^2(Q_k)`, `gr_k` and
  `img_k`, as in §5. `mu3.g` and `mu3.out` do the same for `p=3`, `k<=7`.
- **Complex representation searches.** `batch2.out` records complex
  block-normal-form representation searches for `p=5`. Every converged
  solution has `[R,S]=1`, and there are no detections. This is weak
  evidence only. `newton.py` and `blocksearch.py` are the solvers.
