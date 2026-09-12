# Finite trace tests correct both Leavitt finite-factor profiles

2026-09-08. Written finite-dimensional spectral and Fourier proof.
No code, build, or new Lean verification is asserted.

All traces and Hilbert--Schmidt norms are normalized by the matrix
dimension. Words below are literal words in `c,b_1,b_2,b_3` and
their inverses; length counts these letters, not free-product
syllables. The group is `H=L_(F_2)(1,2)^x`, with the native
`C_3` and `C_2^3` factors from
[the generation theorem](../binary-leavitt-units-generated-by-c3-and-c2-cubed.md).

## 1. Explicit finite correction theorem

Suppose `n` is a positive multiple of `24` and
`C,B_1,B_2,B_3 in U(n)`, with `C^3=I`. Put

```text
alpha=|tr C|,
beta=max( max_i ||B_i^2-I||_2,
          max_(i<j) ||[B_i,B_j]-I||_2 ).               (1)
```

The commutator convention is `[X,Y]=XYX^(-1)Y^(-1)`; its defect
has the same norm as the additive commutator `XY-YX`.

For each nonzero `v in F_2^3`, prescribe the word
`w_v=b_1^(v_1)b_2^(v_2)b_3^(v_3)`. These are seven nonidentity
elements of `H`. Choose `N_0,M_0>=2`, `r>=1`, and take the finite
native certificate of
[the single-cycle trace theorem](../leavitt-single-cycle-trace-controls-finite-sets.md)
for these seven words. Assume defect at most `epsilon` on its
literal rows. That theorem gives

```text
|tr w_v(C,B)|<=eta_0 for v!=0,
eta_0=sqrt(1/N_0+sqrt(1/M_0+3^(-r)+alpha+18 epsilon)).  (2)
```

Define

```text
d_C=sqrt(2 alpha),
d_B=10 beta+sqrt((9/2) (eta_0+30 beta)).               (3)
```

There are exact regular-multiple representations `C'` of `C_3`
and `(B_1',B_2',B_3')` of `C_2^3`, on the original `C^n`, with

```text
||C'-C||_2<=d_C,
max_i ||B_i'-B_i||_2<=d_B.                            (4)
```

Here regular means that each of the three eigenvalues of `C'`
has multiplicity `n/3`, and each joint sign character of the
second factor has multiplicity `n/8`. There is no requirement
that the two factors commute with one another.

If `w` has `ell_c` cycle letters and `ell_b` second-factor letters,
including inverse letters, then

```text
||w(C',B')-w(C,B)||_2<=ell_c*d_C+ell_b*d_B.            (5)
```

Thus a length-`L` relator of initial defect `zeta` has corrected
defect at most `zeta+L*max(d_C,d_B)`. Equations (2)--(5) are
finite, dimension-independent bounds; their certificate list
depends on the chosen parameters.

## 2. Three approximate involutions can be rounded at linear cost

We prove a purely matrix statement, requiring none of the Leavitt
identities. For each `B_i`, let `T_i` be its nearest spectral sign,
choosing either sign consistently at ties. For a unit scalar `z`,

```text
dist(z,{1,-1})^2 <= |z^2-1|^2/2.
```

Indeed the two sides reduce to `2(1-|Re z|)` and
`2(1-|Re z|^2)`. Therefore

```text
||T_i-B_i||_2<=beta/sqrt(2),
||T_i T_j-T_j T_i||_2<=gamma,
gamma=(1+2 sqrt(2))*beta.                             (6)
```

The second inequality follows by telescoping the commutator,
which costs twice each generator movement in addition to `beta`.

We will use the following sign-pinch estimate. Let `T` be a
self-adjoint involution and `E` the trace-preserving averaging
projection onto the commutant of finitely many commuting
self-adjoint involutions. Set `A=E(T)`, a self-adjoint contraction,
and `S=sign(A)`, with `sign(0)=1`. Then

```text
||T-S||_2^2 = 2-2 tr |A|
            <=2(1-tr A^2)
            =2||T-A||_2^2.                           (7)
```

The first equality uses that `S` belongs to the averaging algebra;
the last uses that `E` is an orthogonal projection for the tracial
inner product. The inequality is the scalar fact `|a|>=a^2` for
`a in [-1,1]`. Spectral calculus keeps `S` in that algebra.

Set `S_1=T_1`, and let `E_j(X)=(X+S_j X S_j)/2`. First take

```text
S_2=sign(E_1(T_2)),
||S_2-T_2||_2<=gamma/sqrt(2).                         (8)
```

Here `||T_2-E_1(T_2)||_2` is half the norm of its commutator
with `S_1`. Now `S_1,S_2` commute. Their commutators with `T_3`
satisfy

```text
||[S_1,T_3]_add||_2<=gamma,
||[S_2,T_3]_add||_2<=(1+sqrt(2))*gamma.
```

The two averaging maps commute and are contractions. Therefore

```text
||T_3-E_1 E_2(T_3)||_2 <= (2+sqrt(2))*gamma/2.
```

Taking `S_3=sign(E_1 E_2(T_3))`, equation (7) yields
`||S_3-T_3||_2<=(1+sqrt(2))*gamma`. The three `S_i` are now
exact commuting involutions. Combining with (6), the largest
original-generator movement is at most

```text
beta/sqrt(2)+(1+sqrt(2))*gamma
 =(5+7/sqrt(2))*beta <10 beta.                       (9)
```

Every word `w_v` uses at most three generators, so (2) and (9)
give

```text
|tr S_1^(v_1) S_2^(v_2) S_3^(v_3)|
 <=eta_0+30 beta=:eta.                              (10)
```

When the input involutions already commute, this construction can
be taken to do nothing, and `beta=0` throughout.

## 3. Exact Fourier multiplicity correction for the second factor

Let `S(v)` be any exact representation of `F_2^3` on `C^n`,
where `8|n`. For a sign character `chi`, write `P_chi` for its
joint eigenspace projection and `p_chi=tr P_chi`. Fourier inversion
gives

```text
p_chi=(1/8) sum_v chi(v) tr S(v).                    (11)
```

If all seven traces have modulus at most `eta`, the sharp surplus
bound is

```text
f_B=(1/2) sum_chi |p_chi-1/8|
 <=9 eta/8.                                         (12)
```

Here is a proof requiring no enumeration. Each `a_v=tr S(v)` is
real, since `S(v)` is an involution. The expression in (12) is a
convex function of the seven variables `a_v in [-eta,eta]`.
Writing points of this cube as convex combinations of vertices,
its maximum is attained at a sign choice `a_v=eta sigma_v`.
It is harmless here to maximize over the whole cube, including
vertices that might not give nonnegative proportions.

For such a vertex set

```text
F(x)=sum_(v!=0) sigma_v (-1)^(v dot x),
sum_x F(x)=0,       sum_x F(x)^2=56.
```

All eight values are odd and have absolute value at most seven.
Moreover they are congruent modulo four: for distinct `x,y`,
the difference changes exactly four sign summands, so it is
twice the sum of four signs. Up to negating all values, they
therefore lie in `{-7,-3,1,5}`. Let `d,b,c,a` be the respective
counts. The cardinality and the two displayed moments imply

```text
b=a-2d+2,       a+d=1.
```

Thus either the multiset is `{-7,1,1,1,1,1,1,1}`, of absolute
sum `14`, or it is `{5,-3,-3,-3,1,1,1,1}`, of absolute sum
`18`. Fourier inversion gives `f_B=eta sum_x |F(x)|/16` at
the vertex. This proves (12), including `eta=0` directly.

The constant is attained. Take `sigma_v=1` for singleton and
pair supports and `sigma_(111)=-1`. Then `F(x)` equals `5`
at Hamming weight zero, `-3` at weight two, and `1` at weights
one and three. The proportions `p_x=(1+eta F(x))/8` are
nonnegative for `0<=eta<=1/3` and attain `f_B=9 eta/8`.
For rational such `eta` they are realized in finite dimension
after clearing denominators and, if needed, repeating to a
multiple of `24`. At `eta=1/3`, dimension `24` already suffices:
the multiplicities are `8` at weight zero, `0` at weight two,
and `4` at weights one and three.

The target multiplicity `n/8` is an integer. Choose bases of the
joint eigenspaces, match each surplus basis vector to a deficit
character, and change its three sign labels accordingly. Exactly
`n f_B` basis vectors are relabeled. The resulting `B_i'` are
exact commuting involutions of the regular joint profile. A
generator changes by either zero or a sign flip on each relabeled
vector, so

```text
||B_i'-S_i||_2^2<=4 f_B<=(9/2)*eta.                 (13)
```

Combining (9), (10), and (13) proves the second inequality in (4).
This relabeling concerns the joint eight-character profile, so it
preserves all second-factor laws exactly. The sharpness just
proved concerns the total surplus fraction, not the optimal
largest generator movement: relabeling can distribute bit changes
differently among the three generators.

## 4. The cycle profile and the exact fixed-C boundary

For `C^3=I`, let `omega=exp(2 pi i/3)`, let `p_j` be the
proportion of the eigenvalue `omega^j`, and put `z=tr C`. Then

```text
p_j-1/3=(2/3) Re(omega^(-j) z).                     (14)
```

The three real deviations sum to zero. For three such numbers,
their sum of positive parts is their maximum absolute value:
there is at most one positive term or at most one negative term,
and the two total masses agree. Thus

```text
f_C=(1/2) sum_j |p_j-1/3|
    =max_j |p_j-1/3| <=2|z|/3.                      (15)
```

Because `3|n`, relabel exactly `n f_C` surplus eigenvectors to
deficit cube-root eigenvalues. Any two distinct cube roots are
at squared distance three. The resulting regular `C'` satisfies

```text
||C'-C||_2^2=3 f_C<=2 alpha.                        (16)
```

This proves the first inequality in (4). If `z=0`, (14) says
that `C` was already regular, and one can set `C'=C` literally.
Conversely, if `z!=0`, an exactly regular correction cannot keep
the same matrix `C`, since its trace must become zero. These
statements concern exact profiles, not only an estimate.

## 5. Word bounds, dimensions, and the final relative-unitary form

For unitary letters, replacing one letter changes a product by
at most that letter's HS movement. Also
`||V^(-1)-W^(-1)||_2=||V-W||_2`. Telescoping proves (5).
For a word with at most `m` free-product syllables, each cycle
syllable is `c` or `c^(-1)` and each second-factor syllable is a
product of at most three `b_i`. Thus its chosen literal length
is at most `3m`.

After the corrections, a global unitary conjugation puts `C'`
in the prescribed cycle form `C_k`, where `n=24k`. The corrected
second factor is a regular `C_2^3` representation, so in this
basis it equals `U D_(i,k) U^*` for one common `U`. This is the
existing relative-unitary normal form. The final global conjugation
preserves every word defect. No movement bound relative to the
old basis is asserted for this last basis choice.

The divisibility requirement is necessary for exact regular
profiles in the same dimension: both `3` and `8` must divide it.
For an arbitrary input dimension `n`, there are two explicit
dimension adjustments:

* Repeat every input matrix `q=24/gcd(n,24)` times on the diagonal.
  The new dimension `qn<=24n` is divisible by `24`, and all
  normalized traces, word defects, `alpha`, and `beta` are
  unchanged. Equations (2)--(5) apply with the same constants,
  relative to the repeated input tuple.
* Alternatively, put `N=24 ceil(n/24)` and `t=N-n<=23`, and
  append an identity block of size `t` to every input matrix.
  Then `C^3=I` remains exact,
  `alpha_pad<= (n alpha+t)/N`, and each word defect, including
  the factor-law defects, scales by `sqrt(n/N)`. Apply the
  theorem at dimension `N` with these new parameters. This
  yields a bound relative to the padded tuple, with the displayed
  trace penalty; it is not the unchanged-parameter option.

If `tr C=0` initially, then `3|n`. For the second option one may
append a regular `C_3` block of size `t` to `C` instead of the
identity block, since `3|t`, leaving the old cycle summand fixed
and retaining trace zero. This alternative padding need not make
the appended tuple satisfy the other native relations: its
contribution to any word defect is at most `2 sqrt(t/N)`.
The repetition option avoids that extra defect entirely.

## 6. The precise consequence for full-kernel feasibility

Here a native kernel word means a literal generator word whose
value in `H` is the identity. Consider the following relaxed
condition: for every finite set `T` of these words and every
tolerance `h>0`, there are a
dimension and unitary matrices with

```text
C^3=I,       |tr C|<h,       beta<h,
max_(w in T) ||w(C,B)-I||_2<h.                       (17)
```

Here `beta` is (1); equivalently one can append the six true
second-factor relators `b_i^2` and `[b_i,b_j]` to every test set.
No exact second-factor law or prescribed multiplicity is required
of the input in (17).

Condition (17) is equivalent to full-kernel feasibility with the
two regular profiles frozen in dimensions `24k`. One direction
is immediate from frozen models. For the other, fix a desired
finite target set and its maximum literal length `L`. First choose
`N_0,M_0,r` so the floor in (2) is as small as desired. Enlarge
the target set by the finite seven-word trace certificate and the
second-factor relators. Then use (17) with `h` sufficiently small.
Equations (2)--(4) make both generator movements as small as
desired; the target word defects remain small by (5). If needed,
the repetition operation makes the dimension divisible by `24`
without changing any input tolerance. Finally use the common
basis change described in Section 5.

All choices are finite at each desired accuracy. In particular,
if the original second factor is already exact, the same argument
works with `beta=0`; and if `tr C=0` and `24|n`, it corrects only
the second factor while leaving `C` literally fixed.

The certificate list varies with the target accuracy. This proof
does not replace the full kernel by a single fixed finite packet,
and it gives no example satisfying (17). It compares two complete
feasibility formulations rather than deciding either one.

## 7. Why trace information alone does not replace factor laws

The small second-factor defect in (1) is a real input. For a
concrete counterexample to omitting it on the strength of seven
trace values alone, take the Pauli matrices `X,Z` on `C^2` and
on `C^4` put

```text
B_1=X tensor I,    B_2=Z tensor I,    B_3=I tensor Z.
```

All seven prescribed nonempty ordered products have trace zero,
and every `B_i` is an involution. But `B_1` and `B_2` anticommute,
so their additive commutator has normalized HS norm two.
For any commuting unitaries `S_1,S_2`, telescoping gives

```text
2<=2||B_1-S_1||_2+2||B_2-S_2||_2.
```

Thus at least one of those movements is at least `1/2`. Tensor
with a regular cycle on `C^3` and an identity on `C^2` to obtain
dimension `24`, with an exact trace-zero cycle as well. This
example concerns trace data and finite-factor laws only; it is
not asserted to satisfy the other finite native certificate rows.

The correction theorem proves no nonhyperlinearity statement.
Feasibility and a dimension-independent full-kernel obstruction
remain the alternatives in the existing criterion.
