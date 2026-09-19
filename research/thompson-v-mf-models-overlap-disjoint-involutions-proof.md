---
rg: 2
id: thompson-v-mf-models-overlap-disjoint-involutions-proof
kind: route
title: Free proper involutions of V are all conjugate, so exact commuting roundings of disjoint pairs are Klein groups with three equal ranks, forcing half overlap
target: thompson-v-mf-models-overlap-disjoint-involutions
requires: [thompson-v-finitely-presented-infinite-simple]
---

Lane proof (swarm-0917-w17-w17-ptm-pull, 2026-09-19), not independently
reviewed. Elementary: Cantor-space combinatorics, finite-dimensional
functional calculus, and the character table of `(Z/2)^k`.

## Step 0. Rounding

**(R1) One involution.** If `U` is unitary with `||U^2-1||<=eps<1`, the
spectrum of `U` lies within `eps` of `{1,-1}` (spectral mapping), so
`u = f(U)` (continuous functional calculus for the normal `U`), with `f(z)=1` for `Re z>0`
and `-1` for `Re z<0`, is an exact self-adjoint unitary with
`||u-U|| <= eps` (each eigenvalue `z` with `|z^2-1|<=eps` is within `eps` of
`f(z)`, since `|z-f(z)| |z+f(z)| = |z^2-1|` and `|z+f(z)|>=1`).

**(R2) Rank is locally constant.** Two exact self-adjoint unitaries `u,u'`
with `||u-u'||<1` have `-1` projections `p=(1-u)/2`, `p'=(1-u')/2` with
`||p-p'||<1/2<1`, hence `rank p = rank p'`. So `M_n(x)` in the statement is
well defined as soon as `||pi_n(x)^2-1||` is small, which holds for
`omega`-almost every `n` because `pi_n(x)^2 -> pi_n(x^2)=pi_n(e) -> 1`.

**(R3) Commuting family.** Let `u_1,...,u_k` be exact involutions with
`||[u_i,u_j]|| <= eta`. Put `u_1'=u_1`. Having exact commuting involutions
`u_1',...,u_{j-1}'` with `||u_s'-u_s|| <= c_s eta`, let `Q_1,...,Q_m`
(`m <= 2^(j-1)`) be their joint eigenprojections, polynomials
`Q_i = prod_s (1 +- u_s')/2`, so `||[Q_i,u_j]|| <= sum_s ||[u_s',u_j]||/2
<= b_j eta` with `b_j` depending only on `j` and the `c_s`. The pinching
`T = sum_i Q_i u_j Q_i` is self-adjoint, commutes with every `u_s'`, and
`u_j - T = sum_i [Q_i,u_j](1-Q_i)` has norm `<= m b_j eta`. By Weyl's
inequality the spectrum of `T` lies within `m b_j eta` of `{1,-1}`, so for
`eta` small `u_j' = f(T)` (`f=sign`) is an exact involution, commutes with
`u_1',...,u_{j-1}'`, and `||u_j'-u_j|| <= 2 m b_j eta =: c_j eta`.

Consequence: for commuting `a_1,...,a_k in V` generating `E ~ (Z/2)^k`,
for `omega`-almost every `n` there is an exact representation
`rho_n : E -> U(d_n)` with `||rho_n(g)-pi_n(g)|| -> 0` for all `g in E`
(define `rho_n` on the basis by `R1`+`R3`, extend multiplicatively; for
`g = a_{i_1}...a_{i_r}` asymptotic multiplicativity of `pi_n` gives the
estimate). By `R2`, `rank(rho_n(g) = -1) = M_n(g)` for every `g in E\{e}`.

## Step 1. All free proper involutions are conjugate in V

Every element of `V` is given by a finite cylinder partition `P` of `C` on
whose pieces it acts by prefix replacement `[w]u -> [w']u`; any common
refinement of `P` by splitting cylinders `[w]=[w0] sqcup [w1]` is again such
a partition.

**(C1) Nonempty clopens are V-homeomorphic.** A nonempty clopen set is a
finite disjoint union of `r>=1` cylinders, and splitting one cylinder raises
`r` by one. So two nonempty clopens `X,Y` can be written with the same
number of cylinders, and the piecewise prefix replacement matching them is a
homeomorphism `X -> Y` by prefix replacements. Given also `X^c,Y^c`
nonempty, the same on complements yields `g in V` with `gX=Y`.

**(C2) Fundamental domain.** Let `x` be a free proper involution with
support `A`, and `P` a cylinder partition on whose pieces `x` acts by prefix
replacement. The common refinement `Q = P wedge xP` is a cylinder partition
(two cylinders meet in a cylinder or not at all), and `x` maps the piece
`c cap xc'` (`c,c' in P`) onto `xc cap c'` by prefix replacement, again a
piece of `Q`. So `x` permutes the pieces of `Q`, each image a cylinder. If
`xq` meets `q`, the two cylinders are nested; if `xq` is a proper subset of
`q` then `q = x(xq) subset xq` by `x^2=1`, and symmetrically, so `xq=q`, and
a prefix replacement of a cylinder onto itself is the identity, contradicting
freeness on `A`. Hence the pieces of `Q` inside `A` come in disjoint pairs
`{q, xq}`; one piece per pair gives a clopen `D` with `A = D sqcup xD`.

**(C3) Conjugacy.** Let `x,y` be free proper involutions with supports
`A = D sqcup xD`, `B = E sqcup yE`, and `A^c, B^c` nonempty. By `C1` choose
prefix-replacement homeomorphisms `g_0 : D -> E` and `g_1 : A^c -> B^c`.
Define `g = g_0` on `D`, `g = y g_0 x` on `xD`, `g = g_1` on `A^c`. Each
piece is a prefix replacement, so `g in V`, and `g x g^{-1} = y`: on
`E`, `g x g^{-1}(e) = g(x g_0^{-1} e) = y e`; on `yE` it follows by
`x^2=y^2=1`; on `B^c` both sides are the identity.

Hence all free proper involutions form one conjugacy class `K_V`. Since
`pi_n(g x g^{-1})` is within `o(1)` of `pi_n(g) pi_n(x) pi_n(g)^*`, `R2`
gives `M_n(gxg^{-1}) = M_n(x)` for `omega`-almost every `n`, for each fixed
pair. This is **part 1** (for any finite set of elements of `K_V`, which is
all any statement at a fixed coordinate uses).

## Step 2. Klein four groups of disjoint free proper involutions

Let `a,b in K_V` with disjoint supports `A,B` and `A cup B != C`. They
commute, and `ab` is an involution with support `A sqcup B != C` and no
fixed point there, so `ab in K_V`. Round `(pi_n(a),pi_n(b))` by `R1,R3` to
commuting exact involutions `(alpha,beta)`, and write `m_{st}`
(`s,t in {+,-}`) for the ranks of the joint eigenspaces. Then

```text
M_n(a)  = m_{-+} + m_{--},
M_n(b)  = m_{+-} + m_{--},
M_n(ab) = m_{+-} + m_{-+},        (alpha beta has eigenvalue -1 iff s != t)
```

and by Step 1 all three equal `M_n`. Solving,
`m_{--} = m_{-+} = m_{+-} = M_n/2` and `m_{++} = d_n - (3/2) M_n`. The
projection onto the nontrivial part of `<alpha,beta>` is
`1 - e = 1 - (1+alpha)(1+beta)/4` of rank `m_{+-}+m_{-+}+m_{--} = (3/2)M_n`.
This is **part 2**.

## Step 3. Regular blocks

Fix `k>=1` and let `E_k=(Z/2)^k` act by `0wu -> 0(w XOR e)u` (`|w|=k`) on
`[0]` and trivially on `[1]`. Each `e != 0` moves every point of `[0]` and
fixes `[1]`, so it is a free proper involution, and the `E_k` elements
commute. By Step 0 there is an exact `rho_n : E_k -> U(d_n)` near `pi_n`
with character `chi(0)=d_n` and, by Step 1, `chi(e)=d_n-2M_n` for `e != 0`.
For a nontrivial character `lambda` of `E_k`, `sum_{e!=0} lambda(e) = -1`,
so its multiplicity is
`2^(-k) (d_n - (d_n-2M_n)) = M_n/2^(k-1)`, which must be an integer. The
trivial multiplicity is `2^(-k)(d_n+(2^k-1)(d_n-2M_n)) = d_n-(2-2^(1-k))M_n`.
Collecting one copy of each character into a regular block gives
`rho_n = trivial^(d_n-2M_n) + (M_n/2^(k-1)) regular(E_k)`. This is **part 3**.
The case `k=2` is consistent with Step 2 (`m_{++} = (d_n-2M_n) + M_n/2`),
though the generators of `E_2` do not have disjoint supports.

## Step 4. The class obstruction

Support additivity for a disjoint pair `a,b` as in Step 2 means
`rank(1-e_{<a,b>}) = M_n(a)+M_n(b)`, i.e. `(3/2)M_n = 2M_n`, i.e. `M_n=0`.
Conversely, if `M_n=0` for `omega`-almost every `n`, the exact rounding of
`pi_n(a)` is `1`, so `pi_n(a) -> 1` along `omega`. The set
`N = {g : pi_n(g) -> 1 along omega}` is a normal subgroup of `V` (asymptotic
multiplicativity), contains `a != 1`, and so equals `V` by simplicity
(`thompson-v-finitely-presented-infinite-simple`). Hence additivity is
equivalent to asymptotic triviality of `pi`, which is what one wants to
prove, at every scale: nothing here refers to `M_n/d_n`.

Consistency of the finite-subgroup data. Let `W_N ~ Sym(2^N)` permute the
level-`N` cylinders by prefix replacement, so `W_N < W_{N+1}` injectively. In
`sigma = trivial^a + b regular(W_N)` every nonidentity involution has
`-1`-multiplicity `b (2^N)!/2`, independent of the involution. So parts 1–3
hold for all free proper involutions and all `E_k` inside `W_N`. Restricting
`regular(W_{N+1})` to `W_N` gives a multiple of `regular(W_N)`, so these
models are compatible along the tower. Rank data of finite subgroups
therefore cannot give a contradiction. A surviving proof must use
infinite-order elements, or the relative position of the eigenspaces of
non-commuting finite subgroups.
