# Expanding root characters: exact rank interface and the positive-root boundary

The square-root rank argument is already established in
`expander-pvm-transport-forces-dimension-or-mass-collapse`. This audit does
not introduce another copy of that theorem. It derives the precise Fourier
normalization for finite abelian root tables, locates its actors in the
Leavitt presentation, and identifies a locally finite image that retains
the entire positive-root/aggregate-actor interface.

## 1. Full covariance pays spectral rank without a table-size factor

Let `H=F_p^n`, `q=p^n`, and let `U:H->U(d)` be an exact representation,
with character projections `P_chi`, allowing arbitrary multiplicities and
zero projections. Let automorphisms `alpha_s` generate a subgroup acting
transitively on the `N=q-1` nonzero dual characters. Assume the symmetric
generator multiset has the counting-measure gap

```text
avg_s sum_(chi!=0)|f(chi)-f(s.chi)|^2
 >= kappa sum_(chi!=0)|f(chi)-avg f|^2.                 (ECR1)
```

For arbitrary unitaries `D_s`, define the full root-covariance energy

```text
epsilon^2=avg_s avg_(h in H)
 ||D_s U_h D_s^* - U_(alpha_s h)||_2^2.                (ECR2)
```

The induced dual permutation is `s.chi=chi composed_with alpha_s^(-1)`.
Fourier orthogonality gives the exact identity

```text
epsilon^2=avg_s sum_chi
 ||D_s P_chi D_s^* - P_(s.chi)||_2^2.                  (ECR3)
```

There is no factor `q` in this conversion: the normalized average over
root elements becomes an unnormalized sum over orthogonal spectral atoms.

Put `mu=sum_(chi!=0)tr_d(P_chi)` and
`f(chi)=sqrt(tr_d(P_chi))` on nonzero characters. For projections,

```text
||D P D^*-Q||_2^2
 >= (sqrt(tr_d(P))-sqrt(tr_d(Q)))^2.
```

Thus `(ECR1)--(ECR3)` bound the variance of `f` by
`epsilon^2/kappa`. If only `K` nonzero character projections occur, then

```text
(sum f)^2 <= K mu,
sum|f-avg f|^2 = mu-(sum f)^2/N >= mu(1-K/N).
```

Every occurring character consumes at least one matrix dimension. Hence

```text
d >= K >= (q-1)(1-epsilon^2/(kappa mu)).               (ECR4)
```

Only one nontrivial root anchor is needed to bound `mu`. If
`||U_(h_0)-I||_2>=rho>0`, its trivial-character component contributes zero
and every other component contributes at most four to the squared norm.
Therefore `mu>=rho^2/4`, and

```text
d >= (q-1)(1-4epsilon^2/(kappa rho^2)).                (ECR5)
```

With fixed positive `rho,kappa` and `epsilon=o(1)`, this is the requested
`d>=(1-o(1))(|H|-1)`. It needs neither regular multiplicity nor a canonical
trace requirement on every root. The actors need not form a representation;
only their individual covariance errors in `(ECR2)` are used.

This genuinely uses finite matrix rank at the last inequality `d>=K`.
All previous inequalities also hold for equal-trace computations in finite
factors, where nonzero spectral projections have no minimum trace.

## 2. Coordinate covariance retains a sum of row energies

Let `h_1,...,h_n` be a basis of `H` and put
`gamma_p=2sin(pi/p)`. Then

```text
epsilon^2 <= (2/gamma_p^2) avg_s sum_(j=1)^n
 ||D_s U_(h_j) D_s^* - U_(alpha_s h_j)||_2^2.          (ECR6)
```

To see this, for each `s` let `pi(h)=D_s U_h D_s^*` and
`sigma(h)=U_(alpha_s h)`. The operators
`T_h(X)=pi(h)X sigma(h)^*` form an exact unitary representation of the
finite abelian group on Hilbert--Schmidt matrix space. If `E` projects onto
its invariants, the average displacement of `I` is
`2||I-EI||_2^2`. Every nontrivial character is nontrivial on at least one
basis element, so the sum of its squared basis displacements is at least
`gamma_p^2`. Applying this spectral observation to `I` proves `(ECR6)`.

In particular, bounding each displayed coordinate row by `eta` gives
`epsilon<=sqrt(2n)eta/gamma_p`. The sum is essential. A bound on the
maximum row error alone loses `sqrt(n)`; `(ECR6)` does not supply a
constant-test presentation theorem. A bounded actor set is a constant
number of unitaries, but `(ECR2)` remains a growing family of checks until
an additional theorem authenticates its full average.

## 3. The Leavitt actors and anchor are actual group words

In the native relative Leavitt algebra, write the depth-`r` prefix pairs
as `s_a,t_a`, indexed by binary words `a` of length `r`. They obey

```text
t_a s_b=delta_(a,b)A,       sum_a s_a t_a=A.
```

Put `n=2^r`. The coefficients `e_(a,b)=s_a t_b` form matrix units for
`M_n(F_p)` in the active corner. The unital coefficient ring

```text
B_r=F_p(1-A) + span_(F_p){e_(a,b)}
```

is finite; its two displayed summands annihilate one another. For
`g in GL_n(F_p)`, the coefficient

```text
c_g=(1-A)+sum_(a,b)g_(a,b)s_a t_b
```

is a unit, with inverse `c_(g^(-1))`. Its right action is

```text
t_a c_g=sum_b g_(a,b)t_b.                              (ECR7)
```

The root subgroup

```text
H_r={x_12(sum_a z_a t_a):z_a in F_p}
```

is an exact copy of `F_p^n`: a vanishing linear combination of the `t_a`
would, after right multiplication by `s_b`, give `z_b A=0` for every `b`.

The elementary diagonal

```text
D_g=diag(1,c_g^(-1),c_g,1,1)
```

is an ordinary Whitehead word. Explicitly, if
`w_23(u)=x_23(u)x_32(-u^(-1))x_23(u)`, then the elementary image of
`w_23(c_g^(-1))w_23(-1)` is `D_g`. Conjugation on `H_r` is exactly
right multiplication in `(ECR7)`. Thus any chosen expanding matrix
generator set has literal actor words; actor existence is not an
unspecified additional coefficient object. A uniform gap for the chosen
sets is a separate hypothesis in `(ECR1)`.

The fixed mark supplies the single root separation anchor through

```text
[x_12(t_a),x_23(s_a)]=x_13(A)=w_A.                    (ECR8)
```

For unitaries `X,Y`, `||[X,Y]-I||_2<=2||X-I||_2`. Hence an approximate
instance of `(ECR8)` with error `b` and marked separation `rho` forces
`||x_12(t_a)-I||_2>=(rho-b)/2`. No canonical character distribution of
the whole table is needed for this anchor.

These formulas do not bound the required van Kampen areas. The balanced
root-word construction in `leavitt-steinberg-quadratic-radius-pressure`
gives a crude actor word-length bound `O(n^2(r+1)^2)` by summing the
`n^2` matrix coefficients. Word length is not relator area. As in
`affine-leavitt-profile-computable-checkpoints`, one can find a finite
defect-transfer constant at every fixed depth by enumerating proofs of
the relevant finite identities. No uniform bound, nor a usable relation
between that constant and the dimension of a hypothetical microstate,
follows from the displayed words.

If `n` is chosen comparable to `log_p d` to make `p^n>d`, even a
coordinate ledger with row bound `C_r delta` needs approximately

```text
C_r delta sqrt(log d) << 1.
```

Hyperlinearity gives no such relation between model dimension and relator
defect. At fixed depth the resulting theorem is a dimension-profile lower
bound, not a contradiction.

## 4. The aggregate actor/positive-root interface has a locally finite image

There is a sharper algebraic reason that shortening these words alone
cannot complete the route. The rings `B_r` increase with depth:

```text
s_a t_b=sum_i s_(ai)t_(bi).
```

Thus `B_infty=union_r B_r` is locally finite, and its unit group is
locally finite. Let `T` be the group of invertible upper triangular
five-by-five matrices over the full Leavitt coefficient algebra whose
diagonal entries belong to `B_infty^*`. It contains every aggregate actor
`D_g`, every positive root `x_ij(a)` with `i<j`, and the nonidentity mark
`x_13(A)`.

The diagonal image of `T` is a subgroup of `(B_infty^*)^5`, hence locally
finite. Its kernel is `UT_5(R)`, a nilpotent torsion group in characteristic
`p`, hence also locally finite. To make the last assertion explicit, its
nilpotence class is at most four and `(I+N)^(p^a)=I` whenever `p^a>=5`.
A finitely generated nilpotent group of bounded exponent is finite: each
successive lower-central quotient is generated by finitely many basic
commutators and has bounded exponent.

An extension of locally finite groups is locally finite. Indeed, a
finitely generated subgroup has finite diagonal image; its kernel has
finite index and is finitely generated, so it is finite as well. Therefore
`T` is locally finite.

Every finite collection of the above aggregate actors, root packets, and
positive-root anchor relations consequently lies in an actual finite
elementary-matrix group with surviving mark. Its regular permutation
representation satisfies all those relations exactly and has canonical
trace on the injected root packet. Increasing the inspected depth chooses
a larger finite subgroup and leaves this mechanism intact.

This statement concerns the elementary image and the specified interface.
It does not assert that the whole Steinberg preimage is locally finite or
that the full presentation admits such a marked model. In particular, a
Whitehead word has negative-root factors even though its aggregate image
is diagonal. Additional relations involving those factors separately,
rather than merely the aggregate actor, can leave `T`.

The next eligible input is therefore specific: a mixed negative-root or
opposite-root occurrence outside this upper triangular elementary image
must force the covariance/table authentication on a matrix-size-dependent
window with a uniform total error bound. More aggregate prefix actors,
positive-root identities, and fixed-depth canonical root moments all
remain compatible with the locally finite marked image. This is the same
structural boundary that the Jacobson raw nonmonomial/opposite-root audits
locate from their monomial marked-MF subsystem.
