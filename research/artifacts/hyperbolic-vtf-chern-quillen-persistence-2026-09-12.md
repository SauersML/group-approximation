# Invisible torsion is never invisible to cohomology: Chern–Quillen classes and Lück's question

Lane `ex-hyperbolic-vtf`, 2026-09-12. Status: complete argument, **unreviewed**. No
novelty is claimed for the technique (Quillen's power-lifting in a multiplicative
spectral sequence, 1971); the point is that it needs no virtual torsion-freeness,
and that is exactly what turns it into a reformulation of Lück 11.1(i).

## 0. Setting

`G` is a group with a contractible `G`-CW complex `X` such that

- (A1) `dim X = d < infinity` and `X` has finitely many `G`-orbits of cells;
- (A2) cell stabilizers are finite and fix their cells pointwise;
- (A3) every finite subgroup of `G` fixes a point of `X`.

Put `M = M(G) = lcm { |G_sigma| : sigma a cell }` (finite by A1).
By (A2)–(A3) a finite `F <= G` fixes a point, hence the open cell containing it,
hence pointwise its closure and a vertex `v`: `F <= G_v`, so `|F|` divides `M`, and
the vertex stabilizers of orbit representatives carry all finite subgroups up to
conjugacy.

**Word-hyperbolic groups satisfy (A1)–(A3).** D. Meintrup and T. Schick, *A model for
the universal space for proper actions of a hyperbolic group*, New York J. Math. 8
(2002) 1–7, arXiv:math/0209163v3, **Theorem 1** (read from the PDF 2026-09-12): "Let
`G` be a `δ`-hyperbolic group relative to a set of generators `S`, `P_d(G,S)` its Rips
complex, with `d ≥ 32δ + 20`, and `P` its second barycentric subdivision. Then `P` is
a finite `G`-CW-model for the universal space `\underline{E}G` of proper actions, i.e.
`P` consists of finitely many `G`-equivariant cells, `P` has only finite stabilizers
and `P^H` is contractible for any finite subgroup `H ⊂ G`." Their `G`-CW convention
fixes a cell pointwise when it is mapped to itself, and `P^H` contractible means
nonempty; so `P` satisfies (A1)–(A3) (graph node
`hyperbolic-rips-complex-models-proper-actions`). Groups acting properly and
cocompactly on CAT(0) cube complexes also satisfy (A1)–(A3); only these three
conditions are used.

## 1. The Chern family of regular representations

For a finite group `F` let `rho_F` be its complex regular representation and
`cbar(rho_F) in prod_i H^{2i}(F;F_p)` the mod-`p` reduction of its total Chern
class. For every finite `F <= G` define

```text
y_F := cbar(rho_F)^(M/|F|)          (a total, inhomogeneous class)
```

**Lemma 1 (compatibility).** (a) For `K <= F`: `res^F_K y_F = y_K`.
(b) For `g in G` and `c_g : F -> gFg^-1`, `c_g^* y_{gFg^-1} = y_F`.

*Proof.* (a) `rho_F|_K = [F:K] rho_K`; naturality and the Whitney formula give
`res c(rho_F) = c(rho_K)^[F:K]`; raising to `M/|F|` gives exponent
`[F:K] M/|F| = M/|K|`. (b) `rho_{gFg^-1} o c_g = rho_F`. `QED`

Restriction preserves degree, so every homogeneous component `y_F^(m)` is again a
compatible family.

**Lemma 2 (value on a subgroup of prime order).** Let `P = Z/p`. Write
`M/p = p^a m` with `p` not dividing `m`, and put `n = 2(p-1)p^a`.

- `p` odd: `H^*(P;F_p) = Lambda(u) (x) F_p[beta]`, `|beta| = 2`, and
  `y_P^(n) = -m beta^((p-1)p^a)`.
- `p = 2`: `H^*(P;F_2) = F_2[u]`, `|u| = 1`, and `y_P^(n) = m u^(2^(a+1))`.

In both cases `y_P^(n)` is non-nilpotent.

*Proof.* `c_1 : Hom(P,U(1)) -> H^2(P;Z) = Z/p` is an isomorphism, and reduction
`H^2(P;Z) -> H^2(P;F_p)` is injective (multiplication by `p` on `Z/p` is zero), with
image spanned by `beta` (resp. `u^2`). So the characters `chi_i`, `i in F_p`, have
`cbar_1(chi_i) = i lambda beta` for a unit `lambda`. By Whitney,
`cbar(rho_P) = prod_{i in F_p} (1 + i lambda beta)`. In `F_p[beta][t]`,
`prod_i (t + i lambda beta) = t^p - lambda^(p-1) beta^(p-1) t`, whose roots are
the `-i lambda beta` by Fermat. At `t = 1`: `cbar(rho_P) = 1 - beta^(p-1)`.
Frobenius gives `(1 - beta^(p-1))^(p^a) = 1 - w` with `w = beta^((p-1)p^a)`, of
degree `n`, and the degree-`n` part of `(1-w)^m` is `-m w`, nonzero as `p` does not
divide `m`. For `p = 2`, `cbar(rho_P) = 1 + u^2`, `(1+u^2)^(2^a m) = (1 + u^(2^(a+1)))^m`,
with degree-`2^(a+1) = n` part `m u^(2^(a+1))`. `QED`

## 2. Theorem A (detection without virtual torsion-freeness)

**Theorem A.** Let `G, X, d, M` be as in §0, `p` a prime dividing `M`, `n` as in
Lemma 2, and `N = n p^(max(d-1,0))`. There is `c in H^N(G;F_p)` with

```text
res^G_F c = (y_F^(n))^(p^(max(d-1,0)))     for every finite subgroup F <= G.
```

In particular `res^G_P c != 0` for **every** subgroup `P` of order `p`, by Lemma 2.
Call any such `c` a *Chern–Quillen class* of `G` at `p`. So are all its powers
`c^(p^k)`, in degrees `N p^k`.

*Proof.* Order each simplex of the barycentric subdivision `X'` by inclusion of the
original simplices; `G` preserves these orderings, so the Alexander–Whitney diagonal
of `C_*(X')` is `G`-equivariant and filtration-compatible. With the bar resolution
`B_*` of `Z` over `ZG`, the cochain algebra `Hom_G(B_* (x) C_*(X'), F_p)`, filtered by
the `C_*`-degree `s`, has the equivariant cohomology spectral sequence
(Brown, *Cohomology of Groups*, VII.7)

```text
E_1^{s,t} = prod_{sigma in Sigma_s} H^t(G_sigma; F_p)  =>  H^{s+t}_G(X; F_p) = H^{s+t}(G; F_p),
```

where `Sigma_s` represents the orbits of `s`-cells; orientation twists are trivial by
(A2), and `H_G^*(X) = H^*(G)` because `X` is contractible. The spectral sequence is
multiplicative, `d_r` is a derivation on `E_r`, and `E_r` is graded commutative for
`r >= 2` (Quillen, Ann. of Math. 94 (1971), §2, for the Leray form of the same
spectral sequence). On column `0` the `E_1` product is the componentwise cup product,
because the diagonal of a vertex is `v (x) v`. Since `E_1^{s,t} = 0` for `s > d`,
`E_{d+1}^{0,*} = E_infinity^{0,*}`, and `E_infinity^{0,t}` is the image of the edge
map `H^t(G) -> prod_{v in Sigma_0} H^t(G_v)`, which is restriction to the vertex
stabilizers.

The family `z = (y_{G_v}^(n))_{v in Sigma_0}` lies in `E_1^{0,n}`. For an edge `e`
with endpoints `g_0 v_0`, `g_1 v_1` (`v_i in Sigma_0`), `d_1 z` at `e` is the difference
of the two restrictions to `G_e` after conjugating by `g_i`; by Lemma 1 both equal
`y_{G_e}^(n)`. So `d_1 z = 0` and `z in E_2^{0,n}`.

`n` is even, so `z` is central in `E_r` and `d_r(z^p) = p z^(p-1) d_r(z) = 0`.
Inductively `[z^(p^k)]` is a permanent cycle through `E_{k+2}`: if `[z^(p^(k-1))]`
survives to `E_{k+1}`, its `p`-th power is a `d_{k+1}`-cycle. Taking `k = d-1` (and no
power when `d <= 1`, since then `d_r` out of column `0` land in zero columns for
`r >= 2`), `z^(p^(max(d-1,0)))` survives to `E_infinity`. Hence there is
`c in H^N(G;F_p)` with `res^G_{G_v} c = (y_{G_v}^(n))^(p^(max(d-1,0)))` for every
vertex. Every finite `F` lies in some `G_v` (§0), and Lemma 1 gives the formula for
`res^G_F c`. `QED`

**Remark.** For groups of finite virtual cohomological dimension this detection is
classical (Quillen; Brown X), proved with a representation of `G/N`, `N` torsion-free
normal of finite index, which exists exactly when `G` is virtually torsion-free.
The Chern family of regular representations, normalised by the exponents `M/|F|`,
replaces that global representation by a compatible local one, so Theorem A needs
only (A1)–(A3).

## 3. Theorem F: virtual torsion-freeness is non-persistence of one class

**Theorem F.** Let `G` satisfy (A1)–(A3). The following are equivalent.

1. `G` is virtually torsion-free.
2. For every prime `p | M`, some Chern–Quillen class of `G` at `p` restricts to zero
   on some finite-index subgroup.
3. For every prime `p | M`, every Chern–Quillen class at `p` restricts to zero on
   some finite-index subgroup.

Moreover, if `R_f(G)` contains an element of order `p`, every Chern–Quillen class
`c` at `p` is **persistent**: `res^G_H c != 0` for every finite-index `H <= G`, and so
is every power `c^(p^k)`.

*Proof.* (1 => 3) Let `H` be torsion-free of finite index. By (A2) `H` acts freely on
`X`, so `X/H` is a `K(H,1)` of dimension `d` and `H^q(H;F_p) = 0` for `q > d`. If
`d >= 1` then `N >= 2p^(d-1) >= 2^d > d`; if `d = 0` then `G` is finite and `H = 1`.
So every class of degree `N` dies on `H`. (3 => 2) is trivial.

(2 => 1) and persistence. `G` has finitely many conjugacy classes of finite
subgroups (§0), so by `finite-torsion-carrier-virtual-torsionfree-criterion`, if `G`
is not virtually torsion-free then `R_f(G)` contains some `x` of prime order `p`,
and `p | M`. A finite-index `H` contains its normal core, hence `R_f(G)`, hence
`P = <x>`. For a Chern–Quillen class `c` at `p`,
`res^H_P (res^G_H c) = res^G_P c != 0` by Theorem A, and likewise for `c^(p^k)`.
So no Chern–Quillen class at `p` dies on any finite-index subgroup. `QED`

**Reformulation of Lück 11.1(i).** Some word-hyperbolic group is not virtually
torsion-free if and only if some word-hyperbolic group carries a persistent
Chern–Quillen class at some prime.

*Contrast with the degree-two persistent classes already in the graph.*
`finite-hyperbolic-residual-iff-persistent-class` and
`persistent-degree-two-class-on-hyperbolic-group` concern a degree-two class on a
residually finite hyperbolic *base*. They capture only counterexamples with a finite
nontrivial finite residual, and by `hyperbolic-group-trivial-radical-residual-prime-torsion`
that shape is not forced. The Chern–Quillen class lives on the counterexample itself,
in degree `N >= 2(p-1)`, and captures **every** counterexample.

## 4. Corollary G: goodness forces virtual torsion-freeness

Serre: `G` is *good* if `H^q(G_hat;A) -> H^q(G;A)` is an isomorphism for every finite
`G`-module `A` and every `q`. By `good-groups-have-no-persistent-finite-cohomology`, in
a good group every positive-degree class with finite coefficients dies on a
finite-index subgroup. With Theorem F:

**Corollary G.** Every good group satisfying (A1)–(A3) is virtually torsion-free. In
particular every good word-hyperbolic group is virtually torsion-free.

The hypothesis can be weakened to trivial coefficients in large degrees:

**Corollary G'.** If `G` satisfies (A1)–(A3) and, for every prime `p | M`, inflation
`H^q(G_hat;F_p) -> H^q(G;F_p)` is surjective for all sufficiently large `q`, then `G`
is virtually torsion-free.

*Proof.* `H^q(G_hat;F_p)` is the colimit of `H^q(G/U;F_p)` over finite quotients. If
`x in R_f(G)` has order `p`, choose `k` with `q = N p^k` in the surjective range, and
write `c^(p^k) = phi^* e` for a finite quotient `phi : G -> F` and `e in H^q(F;F_p)`.
Then `res^G_P c^(p^k) = (phi|_P)^* e` factors through `H^q(1;F_p) = 0`, contradicting
Theorem A. So `R_f(G)` has no element of prime order and the criterion applies. `QED`

**Corollary H (universal).** If every word-hyperbolic group satisfies the hypothesis of
G' (for instance, if every word-hyperbolic group is good), then every word-hyperbolic
group is virtually torsion-free, hence residually finite by Wise, *Complete square
complexes*, Comment. Math. Helv. 82 (2007), Proposition 9.2
(`universal-hyperbolic-vtf-iff-rf`). Contrapositively, one non-residually-finite
hyperbolic group gives, through `hyperbolic-rf-question-equals-vtf-question`, a
hyperbolic group whose inflation from its profinite completion is non-surjective with
trivial `F_p` coefficients in unboundedly many degrees.

## 5. Calibration

- **Trivial models fail persistence.** `G = Z/p x F_2` is hyperbolic and virtually
  torsion-free; every Chern–Quillen class has degree `N > 1 = cd F_2` and dies on
  `F_2`. A finite group has `X = pt`, `d = 0`, and its classes die on `H = 1`.
- **A real object with persistent classes (sketch, not hyperbolic).** Let `Gamma` be an
  infinite simple torsion-free group acting properly and cocompactly on a
  finite-dimensional contractible complex, with an element `h` of infinite order (for
  example a torsion-free simple lattice in a product of two trees, Burger–Mozes; not
  re-read here). Let `K = <s,t | s^p, t s t^-1 = s^2>` with `p >= 3`, and
  `G = Gamma *_{h = t} K`. A finite quotient kills `Gamma`, hence `t`, hence `s = s^2`;
  so `s in R_f(G)` has order `p`. The tree of spaces built from the complex of `Gamma`
  and the line on which `K` acts through `t` gives (A1)–(A3) after subdivision. So
  `G` carries persistent Chern–Quillen classes at `p` and is not good. The whole
  difficulty of Lück's question is to do this inside the hyperbolic class.

## 6. What this does not claim

- No counterexample and no decision of Lück 11.1(i). The results reformulate it as
  persistence of one explicit class and show every counterexample is non-good.
- The detection technique is Quillen's, and the regular-representation family is
  elementary. Bounded literature check on 2026-09-12: web searches, and the introduction
  of Henn, Duke Math. J. 91 (1998), which treats profinite groups. It found neither the
  detection theorem without virtual torsion-freeness nor Corollaries G, G', H stated.
  No priority is claimed.
- Unreviewed, not Lean-verified.
