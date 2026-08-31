---
rg: 2
id: finite-lamp-target-groupoid-gluing-proof
kind: route
title: Induce regular isotropy carriers and count character-boundary loss
target: finite-lamp-targets-glue-after-action-groupoid-completion
requires:
  - moving-lamp-refinement-cocycle-has-diffuse-fibers
  - lamp-charts-recover-set-action
  - finite-quotient-blindness
---

## Step 1: exact transport from a completed finite groupoid

Work first in one connected component `O).  Choose a root `o` and one
arrow `a_i:o->i` for every object, with `a_o=1_o`.  Put
`H=Aut_C(o)`.  Let `K` be a disjoint union of

```text
floor(min_i r_i / |H|)
```

copies of the left regular `H`-set.  Thus `|K|=k_O).  For an arrow
`g:i->j`, define

```text
h_g=a_j^(-1) g a_i in H,
T_g(i,x)=(j,h_g x),       x in K.                       (FTP1)
```

If `g:i->j` and `f:j->l`, then

```text
h_(fg)
 =a_l^(-1) f g a_i
 =(a_l^(-1) f a_j)(a_j^(-1) g a_i)
 =h_f h_g.                                              (FTP2)
```

The left action on `K` therefore gives `T_(fg)=T_fT_g), and inverses
work by taking inverses in `H`.  If `g:i->i` is a nonidentity isotropy
arrow, then `h_g` is nonidentity.  Its action on every regular `H`-orbit
has no fixed point.  This proves `(FTG1)--(FTG3)`.

Let `m_O=min_i r_i` and root a spanning tree at an object attaining that
minimum.  Along the tree path from the root to `i`,

```text
r_i-m_O
 <=sum_(e in path(o,i)) |r_(t(e))-r_(s(e))|.            (FTP3)
```

After summing over `i`, every tree edge occurs in at most `|O|-1` paths.
Also `0<=m_O-k_O<=|H|-1`.  Hence

```text
sum_i(r_i-k_O)
 =sum_i(r_i-m_O)+|O|(m_O-k_O)
 <=(|O|-1)sum_(e in T)|r_(t(e))-r_(s(e))|
   +|O|(|H|-1).                                        (FTP4)
```

This is `(FTG4)`.  If fixed-point freeness is not requested, take a
trivial `H`-set of size `m_O`; then `k_O=m_O` and the last term is
zero.

This construction is target-side.  It does not compare the new transports
with any supplied unitary blocks and therefore has none of the conjugacy
obstructions in
`finite-schreier-holonomy-is-the-simultaneous-lamp-gauge-obstruction`.

## Step 2: Fourier balance on a common union window

Let `N=|B_S|=2^m`.  Fourier inversion for the character projections gives

```text
p_chi=tau(P_chi)
     =N^(-1) sum_(b in B_S) chi(b) tau(rho(b)).          (FTP5)
```

The Fourier transform of `p=(p_chi)` is

```text
hat(p)(b)=sum_chi p_chi chi(b)=tau(rho(b)).              (FTP6)
```

The uniform vector `u_chi=N^(-1)` has transform `1` at `b=0` and
`0` elsewhere.  Parseval, with this unnormalized Fourier transform, yields

```text
sum_chi |p_chi-u_chi|^2
 =N^(-1)sum_(0!=b in B_S)|tau(rho(b))|^2,               (FTP7)
```

which is `(FTG5)`.  Cauchy--Schwarz gives

```text
sum_chi |p_chi-u_chi|
 <=sqrt(N)(sum_chi |p_chi-u_chi|^2)^(1/2)
 =(sum_(0!=b)|tau(rho(b))|^2)^(1/2).                    (FTP8)
```

Dividing by two proves `(FTG6)`.

If every nontrivial trace is bounded by `epsilon`, the final expression is
at most `sqrt(N-1)epsilon`.  Adding `b` sites replaces the rough scale
`sqrt(N)epsilon` by `sqrt(2^bN)epsilon`.  Thus the loss factor at fixed
uniform trace tolerance is `2^(b/2)`.  In an ultraproduct argument one may
choose accuracy after fixing `S`; the estimate gives no uniform control
when `S` grows before the tolerance is decreased.

Refinement itself introduces no inconsistency.  The projection for a coarse
character is the sum of its fine extensions, as proved in
`moving-lamp-refinement-cocycle-has-diffuse-fibers`.  Once all windows have
been refined to `S`, Step 1 applies to the fine atom capacities.  What it
assumes, and does not produce, is a finite groupoid containing all actor
multiplication arrows on those atoms.

## Step 3: one site error becomes macroscopic on characters

A character of `B_S` is a sign assignment `x:S->{+1,-1}`.  Put
`delta=theta^(-1)eta`.  The equality

```text
hat(theta)x=hat(eta)x
```

holds exactly when `x` is constant on every cycle of `delta`.  If
`c(delta)` counts all cycles, there are exactly `2^(c(delta))` such sign
assignments out of `2^|S|).  This proves `(FTG7)`.

If `delta` is nonidentity, some cycle has length at least two, so
`c(delta)<=|S|-1` and the Hamming defect is at least `1/2`.  If its
support has size `q`, all cycles on the support have length at least two.
There are at most `q/2` of them, whence

```text
c(delta)<=|S|-q/2,
d_H(hat(theta),hat(eta))>=1-2^(-q/2).                   (FTP9)
```

For a disjoint union of regular character blocks, Hamming distance is the
weighted average of the block distances.  Therefore a vanishing actor
relation defect forces the density of blocks with any site-level relation
error to vanish.

Now fix a tested multiplication cell `sh=k`.  Let
`theta_k^0=theta_s theta_h` be a coherent site completion on `S`.
Assume two boundary sites `u,v` lie outside every prescribed target
coordinate for the coarse `k`-window, and let `tau=(u v)`.  Set

```text
theta_k=tau theta_k^0.                                  (FTP10)
```

Because `tau` fixes the prescribed target window pointwise,
`theta_k` and `theta_k^0` induce the same map on every named coarse
character restriction.  All individual generator covariance and overlap
tests on those windows are identical.  But

```text
theta_k^(-1)theta_s theta_h
```

is a conjugate of one transposition, so the induced relation defect is
exactly `1/2`.  Pairwise restriction couplings therefore do not determine
the multiplication cell.

Individual scalar mixed traces do not repair this.  If desired, tensor the
three candidate permutations with the left regular action of a finite actor
quotient separating the tested nonidentity generators.  Every individual
nonidentity actor and lamp--actor trace is then zero, while the relation
defect in `(FTP10)` is unchanged.  The trace of the relation word itself
does detect the defect; preserving that trace is precisely the missing joint
multiplication constraint.

## Step 4: exact finite action blocks cannot be the missing completion

A general compression pair already shows why exact quotients cannot fill the
groupoid objects needed above.  Suppose

```text
c Gamma c^(-1) proper-subset Gamma.
```

Choose `gamma in Gamma minus c Gamma c^(-1)` and put
`x=c^(-1)gamma c`.  Then `x notin Gamma`.  For every homomorphism
`q:G->Q` to a finite group,

```text
q(c Gamma c^(-1)) subset q(Gamma).                      (FTP11)
```

The two subgroups in `(FTP11)` are conjugate in `Q`, so they have the
same finite cardinality and must be equal.  Hence
`q(x) in q(Gamma)` for every finite quotient: `x` lies in the profinite
closure of `Gamma`.

Equivalently, in every exact finite `G`-set, any point fixed by all of
`Gamma` is also fixed by `x`.  The real coset point `Gamma in G/Gamma`
is fixed by `Gamma` but moved by `x`.  Thus no disjoint union of exact
finite pointed action blocks can complete even this finite separation
pattern.  For the pinned Kun--Thom mark, the stronger exact and approximate
two-point obstructions are already recorded by
`finite-quotient-blindness` and `two-point-approximation-fails`.

Step 1 proves that integer transport is easy after a finite action groupoid
has been supplied.  Steps 3 and 4 show that neither boundary extension nor
exact finite quotients supply it.  Extracting an approximately
multiplicative classical groupoid from arbitrary matrix microstates would
produce the forbidden lamp charts of
`lamp-charts-recover-set-action`.  That extraction, rather than rank
balancing or overlap gluing, is the direct-target theorem still missing.
