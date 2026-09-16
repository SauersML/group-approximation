# HC1 reflected root word: the A~2 quotient, local reductions and finite-image scans

Date: 2026-09-16. Lane: frontier swarm on `hyperbolic-groups-virtually-torsion-free`,
hole `kms-hc1-finite-images-kill-reflected-root-word`.

This artifact supports the claim `kms-hc1-root-word-infinite-in-a2-quotient`
(Section 2 is its complete proof) and records elementary lemmas and exactly
scoped computations about finite images of `Gamma_p` (Sections 3 to 5). Only
Section 2 is used by a `requires: []` route. Sections 3 and 4 are proved here but
are not graph nodes. Section 5 is evidence only.

## 1. Conventions

`[x,y]=x^-1 y^-1 x y`, left-normed iterated commutators. For a prime `p`,

```text
Gamma_p      = < a,b,c | a^p, b^p, c^p, [a,b,a], [a,b,b], [b,c,b], [b,c,c],
                          [a,c,a], [a,c,c,a], [a,c,c,c] >
Gamma^A2_p   = < a,b,c | a^p, b^p, c^p, [a,b,a], [a,b,b], [b,c,b], [b,c,c],
                          [a,c,a], [a,c,c] >
r = [b,a],  s = [b,c],  w_p = (r s)^p.
```

The relators `[a,c,c,a]` and `[a,c,c,c]` are consequences of `[a,c,c]=1`, so the
identity on `a,b,c` induces a surjection `Gamma_p -> Gamma^A2_p`
(equivalently `Gamma^A2_p = Gamma_p / <<[a,c,c]>>`). `Heis(p)` denotes the group
of upper unitriangular `3x3` matrices over `F_p`.

## 2. The root word survives in the A~2 quotient

**Proposition 2.3.** For every prime `p`, the subgroup `<r,s>` of `Gamma^A2_p`
is the free product `<r> * <s> = C_p * C_p`. The element `rs` has infinite
order, so `w_p=(rs)^p` is nontrivial.

**Lemma 2.1 (Heisenberg presentation).** For every prime `p`,
`<x,y | x^p, y^p, [x,y,x], [x,y,y]>` is isomorphic to `Heis(p)` via
`x -> I+E_12` and `y -> I+E_23`. The commutator `z=[x,y]` generates the centre,
and every element has the form `x^i y^j z^k`.

*Proof.* The relators make `z` commute with `x` and `y`, so `z` is central.
From `y^-1 x y = xz`, one gets `[x^i,y^j]=z^(ij)`, and `z^p=[x,y^p]=1`. Hence
every element is `x^i y^j z^k`, and the group has order at most `p^3`. The
matrices satisfy the relators and generate `Heis(p)`, of order `p^3`, so the map
is an isomorphism. The centre of `Heis(p)` is `{I+tE_13}=<z>`. []

**Lemma 2.2 (local geometry).** Let `V=Heis(p)` with `A=<x>`, `B=<y>` as in
Lemma 2.1. Let `Gr(V;A,B)` be the bipartite coset graph with vertex set
`V/A ⊔ V/B` and one edge `{gA,gB}` for each `g in V`.

1. `A ∩ B = 1`, and `Gr(V;A,B)` has girth at least `6`.
2. For `k ≢ 0 (mod p)`, `z^k ∉ BAB` and `z^k ∉ ABA`. Hence the vertices `B` and
   `z^k B`, and likewise `A` and `z^k A`, are at distance at least `4` in `Gr(V;A,B)`.

*Proof.* (1) The normal form gives `A ∩ B = 1`, so there are no double
edges. A 4-cycle is a relation `x^i y^j x^m y^n = 1` with nonzero exponents.
In the abelianisation `F_p^2` this forces `m=-i` and `n=-j`, so the relation
reads `[x^-i, y^-j] = z^(ij) = 1`, which is false.

(2) The abelianisation sends `y^i x^m y^j` to `(m, i+j)` and `z^k` to `0`, so
`z^k in BAB` forces `m ≡ 0`, and then `z^k in B ∩ <z> = 1`. That is a
contradiction, and `ABA` is symmetric. A path of length `2` from `B` to `gB`
passes through some `hA` with `h in B` and `hA ∩ gB ≠ ∅`. That means `g in BAB`.
The graph is bipartite, and `z^k B ≠ B`, so the distance is at least `4`. []

*Proof of Proposition 2.3.*

**The triangle of groups.** Let `T` be the triangle of groups with:

- vertex groups `V_ab=<a,b>`, `V_bc=<b,c>` and `V_ac=<a,c>`, each presented as in Lemma 2.1;
- edge groups `<a>`, `<b>` and `<c>`, each `C_p`;
- trivial face group;
- the obvious inclusions.

Its fundamental group, the colimit, has the union of the three vertex
presentations as a presentation, and that is `Gamma^A2_p`.

**Non-positive curvature.** By Lemma 2.2(1), the Gersten--Stallings angle at
each vertex is at most `pi/3`. The angle sum is at most `pi`, so `T` is
non-positively curved. By the Gersten--Stallings theorem:

- `T` is developable;
- the vertex groups inject into `Gamma^A2_p`;
- `Gamma^A2_p` acts on the simply connected development `X`, a triangle
  complex whose fundamental triangle has vertices `v_ab, v_bc, v_ac` with
  stabilisers `V_ab, V_bc, V_ac` and edges with stabilisers `<a>,<b>,<c>`;
- the edge `e_b=[v_bc,v_ab]` has stabiliser `<b>`.

**The metric.** Metrise every triangle as a Euclidean equilateral triangle
with side `1`. The link of `v_ab` is `Gr(V_ab;<a>,<b>)` with edges of length
`pi/3`, and similarly at the other vertices. Girth at least `6` gives link
systole at least `2pi`. By the link condition `X` is locally CAT(0), and it is
simply connected, so it is CAT(0) by Cartan--Hadamard.

**Angle at a vertex.** The Alexandrov angle at a vertex between two edges
equals `min(pi, d_Lk)` in the link. The element `r=[a,b]^-1` is a nonzero power
of the central generator of `V_ab` and fixes `v_ab`. For `k ≢ 0` it sends the
link vertex `<b>` of `e_b` to `r^k<b>`. Lemma 2.2(2), applied with
`(x,y)=(a,b)`, puts these at link distance at least `4`, so

```text
angle at v_ab between [v_ab, v_bc] and [v_ab, r^k v_bc]  =  pi.
```

In the same way `s=[b,c]` fixes `v_bc`. Lemma 2.2(2), applied with
`(x,y)=(b,c)` and `A=<b>`, gives angle `pi` at `v_bc` between `[v_bc,v_ab]` and
`[v_bc, s^l v_ab]` for `l ≢ 0`.

**The local geodesic.** Let `g = r^(k_1) s^(l_1) ... r^(k_n) s^(l_n)` with
`n>=1` and all exponents nonzero mod `p`. Let `h_0=1` and let `h_j` be the
product of the first `j` syllables of `g`, so `h_(2n)=g`. Let `sigma` be the
edge from `v_bc` to `v_ab`, and consider the concatenation

```text
gamma = sigma . h_1 sigma^-1 . h_2 sigma . h_3 sigma^-1 ... h_(2n-1) sigma^-1 .
```

Consecutive segments match up: `r` fixes `v_ab` and `s` fixes `v_bc`. So
`gamma` runs from `v_bc` to `h_(2n-1) v_bc = g v_bc` and has length `2n`.
Translating by `h_j^-1`:

- the breakpoints `h_(2j) v_ab` have angle `pi` by the case of `r^(k_(j+1))`;
- the breakpoints `h_(2j+1) v_bc` have angle `pi` by the case of `s^(l_(j+1))`.

A concatenation of geodesic segments with angle `pi` at every breakpoint is a
local geodesic. In a CAT(0) space a local geodesic is a geodesic. Hence
`d(v_bc, g v_bc) = 2n > 0` and `g ≠ 1`.

**Conclusion.** The natural map `<r>*<s> -> Gamma^A2_p` is well defined, since
`r^p=s^p=1`. Any nontrivial element of its kernel is conjugate, inside the free
product, to either a nontrivial `r^k`, a nontrivial `s^l`, or a cyclically
reduced `g` as above. Now `r` and `s` have order `p`, because `V_ab` and `V_bc`
inject, and `g ≠ 1`. So the map is injective. Taking `g=(rs)^m` gives
`d(v_bc,(rs)^m v_bc)=2m`, so `rs` has infinite order. []

**Corollary 2.4 (independent proof for `Gamma_p`).** For every prime `p`,
`<[b,a],[b,c]> = C_p * C_p` in `Gamma_p`.

*Proof.* The surjection `Gamma_p -> Gamma^A2_p` sends `r` to `r` and `s` to `s`.
In `Gamma_p` the subgroup `<r,s>` is a quotient of `C_p*C_p`, and it maps onto
`C_p*C_p` generator to generator. The composite
`C_p*C_p -> <r,s> -> C_p*C_p` is the identity, so the first map is injective.
This does not use Caprace--Marquis Theorem 6.9 or the hyperbolicity of
`Gamma_p`. []

**Corollary 2.5 (what the hole forces).** Fix a prime `p`.

- If every finite image of `Gamma_p` kills `w_p`, then every finite quotient of
  `Gamma^A2_p` kills `w_p`, which is nontrivial there. So `Gamma^A2_p` is not
  residually finite.
- Conversely, suppose that for every prime `p>=7` some finite quotient of
  `Gamma^A2_p` does not kill `w_p`. Then `kms-hc1-finite-images-kill-reflected-root-word`
  is false.

*Proof.* Finite quotients of `Gamma^A2_p` are finite images of `Gamma_p`. []

**Remark 2.6.** The map `a -> I+E_12`, `b -> I+E_23`, `c -> I+tE_31` into
`SL_3(F_p[t])` satisfies all relators of `Gamma^A2_p`. The product of the two
commutators is `I+N` with `N = ±E_13 ± tE_21` and `N^2 = ±tE_23`, so `N^3=0`.
For `p>=3` this map kills `w_p`. So `Gamma^A2_p` is a finitely presented
CAT(0) triangle-complex group with an infinite-order element killed by a
linear representation over `F_p[t]`.

The development `X` is not a building. Its vertex links are biaffine-plane
graphs with `2p^2` vertices, not incidence graphs of `PG(2,p)`. Under the
`SL_3` image, two parallel affine lines at link distance `4` in `X` become
lines at distance `2` in `PG(2,p)`. That folding is where `w_p` dies.

**Sources for the geometric input** (standard, theorem numbers not
re-verified in this lane): Bridson--Haefliger, *Metric spaces of non-positive
curvature*:

- Part II Chapter 12: complexes of groups, triangles of groups, the
  Gersten--Stallings theorem;
- Part II Chapter 5: the link condition for 2-complexes;
- Part II Chapter 4: Cartan--Hadamard;
- Part I Chapter 7: angles in `M_kappa`-polyhedral complexes;
- Part II Chapter 1: local geodesics in CAT(0) spaces.

Also J. Stallings, *Non-positively curved triangles of groups* (1991),
unverified in this lane.

## 3. Local reductions for a detecting finite image

Call a finite image `(A,B,C)` of `Gamma_p` *detecting* if `([B,A][B,C])^p ≠ 1`.

**Lemma 3.1.** In a detecting image, `[A,B] ≠ 1` and `[B,C] ≠ 1`. Hence
`<A,B>` and `<B,C>` are both isomorphic to `Heis(p)`.

*Proof.* Suppose `[A,B]=1`. Then `r=1` and `w=s^p`. Since `s=[B,C]` commutes
with `C`, one has `[B,C^k]=s^k`, so `s^p=[B,C^p]=1`. The case `[B,C]=1` is
symmetric. The group `<A,B>` is a quotient of `Heis(p)` by Lemma 2.1. Every
nontrivial normal subgroup of the `p`-group `Heis(p)` meets its centre `<z>`,
which has order `p`, so every proper quotient is abelian. A nonabelian image
is therefore faithful. []

**Lemma 3.2 (reduction to the A~2 quotient is one-sided).** A detecting image
with `[A,C,C]=1` is a finite quotient of `Gamma^A2_p`. So a detecting image of
`Gamma^A2_p` refutes the hole for that `p`, by Corollary 2.5. The hole cannot be
*proved* inside `Gamma^A2_p`: images with `[A,C,C] ≠ 1` also have to be
controlled.

**Remark 3.3 (vertex-injectivity certificate used by the searches).** The
local vertex group `V_ac` of `Gamma_p` is the unipotent radical `U_B2(p)`: `a`
is long and `c` is short. This is the CCKW Theorem 1.3 local data, not
re-verified in this lane. The element `[a,c,c]` spans the highest root group,
which is the centre for odd `p`. As in Lemma 3.1, a triple is injective on
`V_ac` iff `[A,C,C] ≠ 1`. The searches in Section 5.2 use `[A,B] ≠ 1`,
`[B,C] ≠ 1` and `[A,C,C] ≠ 1` as the injectivity certificate on all three
vertex groups.

**Not proved here.** When `[A,C]=1`, the quotient
`Gamma_p/<<[a,c]>>` is expected to be `UT_4(F_p)`, which would kill `w_p`. This
lane did not prove that for general `p`.

## 4. Linear-algebra constraints on detection

**Lemma 4.1 (unipotent dimension bound).** Let `k` have characteristic `p`,
let `V` be a `k`-space of dimension `d <= 2p`, and let `rho: Gamma_p -> GL(V)`
have `p`-group image. Then `rho(w_p)=1`.

*Proof.* A `p`-group in characteristic `p` fixes a full flag
`V=V_0 > V_1 > ... > V_d = 0` with `(rho(g)-1)V_i ⊆ V_(i+1)`. Let `Phi_m` be the
set of `g` with `(g-1)V_i ⊆ V_(i+m)` for all `i`. Write `g=1+X` and `h=1+Y` with
`g in Phi_m` and `h in Phi_n`. Then `g^-1 h^-1 g h - 1 = g^-1 h^-1 (XY-YX)`, so
`[Phi_m,Phi_n] ⊆ Phi_(m+n)`. Hence `rho(r)` and `rho(s)` lie in `Phi_2`, and so
does `rho(rs)=1+X`. In characteristic `p`, `(1+X)^p = 1+X^p`, and `X^p` maps
`V_i` into `V_(i+2p)`, which is `0` because `2p >= d`. []

The same argument shows that `w_p` lies in the `2p`-th Zassenhaus (mod-`p`
dimension) subgroup `D_(2p)(Gamma_p)`: one has `rs in D_2` and
`D_n^p ⊆ D_(np)`. So every `p`-group image `F` with `D_(2p)(F)=1` kills `w_p`.
This is classical Jennings--Lazard material and was not re-fetched. It does not
bound the `p`-group images that could detect `w_p`: those need
`D_(2p)(F) ≠ 1`, for example nilpotency class at least `2p` or
`gamma_2(F)^p ≠ 1`.

**Lemma 4.2 (affine lifts).** Let `rho: Gamma_p -> GL(M)` be a finite image
with `rho(w_p)=1`, and let `delta in Z^1(Gamma_p;M)`. Then
`g -> (rho(g), delta(g))` is a finite image `M ⋊ rho(Gamma_p)` in which `w_p`
maps to the translation

```text
delta(w_p) = (1 + T + ... + T^(p-1)) delta(rs),     T = rho(rs).
```

- **Characteristic `p` and `T=1+N` unipotent.** In `F_p[x]` one has
  `sum_(i<p) (1+x)^i = x^(p-1)`, so `delta(w_p) = N^(p-1) delta(rs)`. This
  needs a Jordan block of `T` of size at least `p` on `M`.
- **Characteristic `l ≠ p`.** `T^p=1` makes `T` semisimple, so
  `delta(w_p) = p·pi_fix(delta(rs))`, where `pi_fix` is the projection onto
  `M^T`.

`Z^1` is the kernel of the stacked Fox-derivative matrices of the ten
relators. *Proof:* the cocycle identity iterated along the word `(rs)^p`. []

**Lemma 4.3 (homological criterion).** `w_p` survives in some finite image of
`Gamma_p` iff some finite-index `H <= Gamma_p` with `w_p in H` has
`[w_p] ≠ 0` in `H_1(H;Z)`.

*Proof.*

- **Only if.** Suppose `w_p -> x ≠ 1` in a finite image `F`. Let `H` be the
  preimage of `<x>` and `l` a prime dividing the order of `x`. Then
  `H -> <x> -> C_l` detects `w_p`.
- **If.** A homomorphism `H -> H_1(H;Z)`, a finite group because `Gamma_p` has
  (T) and `H` has finite index, detects `w_p`. Its kernel has finite index in
  `Gamma_p`, and the normal core of that kernel gives a finite image of
  `Gamma_p` not killing `w_p`. []

For a permutation image with point stabiliser `H`, the covering 2-complex with
vertex set the orbit gives `Z^E / im(d_2) = H_1(H;Z) ⊕ Z^(|orbit|-1)`, and
`[w_p]` is the class of the closed walk. The test in Section 5.4 is exact over
`Z`, so it also sees `l^k`-torsion classes that are invisible mod `l`.

## 5. Computations (evidence only; exact scope)

The scripts are in
`experiments/kms-hc1-root-word-finite-images-2026-09-16/`, with outputs `output_*.txt`.
All arithmetic is exact (integers mod `q`, or Python integers).

### 5.1 Affine lifts over the `SL_3(F_7)` image (`scan_sl3_modules.py`)

The representation is `a=I+E_01`, `b=I+E_12`, `c=I+E_20`, the `t=1`
specialisation of Remark 2.6. All relators hold and `rho(w_7)=I`.
`rho(rs)-I` has nilpotency index `3`. The modules tested:

- `Sym^m(F_7^3)` and its dual, for `m=1..8`;
- permutation modules `F_l[P^2(F_7) points]`, `F_l[P^2 lines]` and
  `F_l[F_7^3 \ 0]`, for `l in {2,3,7}`.

For every module the rank of `delta -> delta(w_7)` on `Z^1` is `0`. The `dim Z^1`
values are in `output_scan_sl3_modules_p7.txt`.

### 5.2 Small vertex-injective `SL_4(F_7)` images (`search_vertex_injective.py 7 4 2`)

The search space is exhaustive within these bounds:

- `a` is `I` plus one off-diagonal elementary term with coefficient `±1`,
  normalised to `a=I+E_01` up to signed-permutation conjugation, which
  preserves the space;
- `c` is `I` plus at most two such terms;
- `b` is `I` plus at most two such terms.

Of the `(a,c)` pairs, 576 are `U_B2`-injective, and 24 of those have
`a=I+E_01`. There are 672 triples satisfying all relators and the Remark 3.3
certificate. All of them have `rho(w_7)=I`. The nilpotency indices of
`rho(rs)-I` are `1` (32 triples), `2` (448) and `3` (192).

### 5.3 Affine lifts over two of these images (`scan_sl4_modules.py 7 5`)

The images are `R1: a=I+E_01, b=I+E_20, c=I+E_12+E_23` and
`R2: a=I+E_01, b=I+E_12, c=I+E_12+E_23`. For `Sym^m(F_7^4)` and its dual,
`m=1..5`, the rank is `0` in every case.

### 5.4 Exact integral `H_1` test (`h1_detect.py`)

For each orbit, `[w_p]=0` in `H_1(H;Z)` for the stabiliser `H`, in every case
below.

- **`SL_3(F_7)` image, `p=7`:**
  - stabilisers of a point (index 57), a line (57) and a nonzero vector (342);
  - positive controls: `[a]` and `[c]` are nonzero in `H_1` of the point
    stabiliser.
- **`R1`, `p=7`:**
  - point orbits of size 343 and 57;
  - hyperplane orbits of size 1 and 399. The size-1 orbit gives
    `H=Gamma_7`, and the echelon pivots are `7,7,7`, consistent with
    `Gamma^ab = (Z/7)^3`.
- **`R2`, `p=7`:**
  - point orbits of size 343, 49, 7 and 1;
  - hyperplane orbits of size 1, 7, 49 and 343.
- **`SL_3(F_11)` image, `p=11`:** stabilisers of a point and of a line (index 133).

In every case the free rank of `Z^E/im d_2` equals `|orbit|-1`, as property
(T) predicts.

**What this does and does not show.** These are all finite-index subgroups
coming from a handful of small linear images. The kernels of the two
`SL_3` images contain the kernel of the canonical map of Remark 2.6 (for
`Gamma^A2`, and via `Gamma_p -> Gamma^A2_p`). Detection there needs `H_1` of
subgroups much deeper than a point stabiliser. Nothing here constrains
arbitrary finite images.

## 6. Where these approaches stop

1. **Positive Kac--Moody type images.** Anything factoring through
   `Gamma^A2_p -> SL_3(F_p[t])`, or through the canonical positive KM image of
   `Gamma_p`, kills `w_p`. The small searches in 5.2 and 5.3 only find such
   "folded" images.
2. **`p`-group images.** Lemma 4.1 rules out unipotent images of dimension at
   most `2p`, and any image with `D_(2p)(F)=1`. Suppose the pro-`p` completion of
   `Gamma_p` coincides with the completed positive KM group, as suggested by
   Ershov-type presentations of `hat U^+` (unverified in this lane). Then *all*
   `p`-group images kill `w_p`, and a detecting image must have order divisible
   by another prime.
3. **Affine lifts in characteristic `l ≠ p`.** These need `delta(rs)` to have a
   nonzero component fixed by `rho(rs)` (Lemma 4.2). The permutation modules
   tested give none.
4. **The A~2 route to refutation (Corollary 2.5).** This needs a finite quotient
   of the CAT(0) triangle group `Gamma^A2_p` separating `w_p`, for every
   `p>=7`. Residual finiteness of such non-building `A~2`-type triangle
   groups is, as far as this lane could check, not known.
