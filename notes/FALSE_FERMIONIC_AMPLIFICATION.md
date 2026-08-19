# Fermionic amplification of an operator-norm witness

Date: 2026-08-10

This note gives a profile-sensitive but completely explicit conversion from
operator-norm approximate representations to normalized Hilbert--Schmidt
approximate representations. It applies to a single element in the full
sofic radical, so no faithfulness of the output representation is needed.

The construction is the full exterior algebra, tensored with its conjugate
representation. Its useful feature is that one exceptional eigenvalue, even
on a one-dimensional input subspace, changes the normalized output trace by
a fixed amount. Conjugate doubling cancels the determinant phase and reduces
the exact cost to the square root of the input dimension in normalized
Hilbert--Schmidt defect.

## 1. Full exterior amplification

For `U in U(d)`, put

`F_d(U)=directSum_(k=0)^d wedge^k U`                       `(FFA1)`

on the fermionic Fock space

`F(C^d)=directSum_(k=0)^d wedge^k C^d`,
`dim F(C^d)=2^d`.                                         `(FFA2)`

The assignment is exactly multiplicative:

`F_d(UV)=F_d(U)F_d(V)`.                                   `(FFA3)`

It has the following two quantitative properties.

**Lemma 1 (operator-norm Lipschitz bound).** For `U,V in U(d)`,

`||F_d(U)-F_d(V)||_op <= d ||U-V||_op`.                   `(FFA4)`

**Proof.** On the `k`th exterior power, insert `V` one tensor factor at a
time. The usual tensor telescoping estimate gives

`||wedge^k U-wedge^k V||_op <= k||U-V||_op`.

Take the maximum over `0<=k<=d`. End proof.

**Lemma 2 (fermionic trace identity).** With normalized traces,

`tr_(2^d)(F_d(U))=det((I+U)/2)`.                          `(FFA5)`

Consequently, if `||U-I||_op>=c`, where `0<c<=2`, then

`|tr_(2^d)(F_d(U))| <= sqrt(1-c^2/4)`.                   `(FFA6)`

**Proof.** If the eigenvalues of `U` are `lambda_1,...,lambda_d`, the
eigenvalues of the full exterior algebra are the products over all subsets
of `{1,...,d}`. Summing those products gives

`Tr(F_d(U))=product_j(1+lambda_j)=det(I+U)`,

which proves `(FFA5)`. Choose an eigenvalue `lambda` with
`|lambda-1|>=c`. Every other factor in

`|det((I+U)/2)|=product_j |(1+lambda_j)/2|`

is at most one, while

`|(1+lambda)/2|^2=1-|1-lambda|^2/4<=1-c^2/4`.

This proves `(FFA6)`. End proof.

The estimate is rank-free: one exceptional eigenvalue suffices. In
particular, if `-1` is an eigenvalue, the amplified normalized trace is
exactly zero.

For the approximation theorem use the phase-cancelled amplification

`G_d(U)=F_d(U) tensor conjugate(F_d(U))`                  `(FFA7)`

on a space of dimension `4^d`.

**Lemma 3 (phase-cancelled Hilbert--Schmidt bound).** For `U,V in U(d)`,

`||G_d(U)-G_d(V)||_2 <= sqrt(d/2) ||U-V||_op`.           `(FFA8)`

Moreover

`tr_(4^d)(G_d(U))=|det((I+U)/2)|^2`.                    `(FFA9)`

**Proof.** Put `W=U^*V`, and write its eigenvalues as `exp(i theta_j)`.
Exact functoriality and `(FFA5)` give

`tr(G_d(U)^*G_d(V))`
` =|det((I+W)/2)|^2`
` =product_j (1-|1-exp(i theta_j)|^2/4)`.               `(FFA10)`

This number is real and belongs to `[0,1]`. Since

`1-product_j(1-a_j)<=sum_j a_j`, `0<=a_j<=1`,

and `|1-exp(i theta_j)|<=||I-W||=||U-V||`, we obtain

`||G_d(U)-G_d(V)||_2^2`
` =2-2tr(G_d(U)^*G_d(V))`
` <=(d/2)||U-V||_op^2`.                                 `(FFA11)`

The trace identity is `(FFA10)` with `V=I`, equivalently the tensor-product
trace formula. End proof.

## 2. A dimension--defect criterion for FALSE

Let `Rad_sof(H)` denote the intersection of the kernels of all homomorphisms
from `H` to sofic groups.

**Theorem 4 (fermionic FALSE criterion).** Let `H` be countable and let

`1!=x in Rad_sof(H)`.                                    `(FFA12)`

Suppose there are maps

`phi_n:H->U(d_n)`                                        `(FFA13)`

and a constant `c>0` such that

`liminf_n ||phi_n(x)-I||_op >= c`,                       `(FFA14)`

and, for every fixed `g,h in H`,

`sqrt(d_n) ||phi_n(g)phi_n(h)-phi_n(gh)||_op -> 0`.      `(FFA15)`

Then there is a hyperlinear nonsofic group. In particular, not every
hyperlinear group is sofic.

**Proof.** Define

`Psi_n(g)=G_(d_n)(phi_n(g)) in U(4^(d_n))`.              `(FFA16)`

By exact functoriality and the Hilbert--Schmidt estimate `(FFA8)`,

`||Psi_n(g)Psi_n(h)-Psi_n(gh)||_2`
` <=sqrt(d_n/2)||phi_n(g)phi_n(h)-phi_n(gh)||_op ->0`.   `(FFA17)`

Thus `(Psi_n)` induces a homomorphism `Psi` from `H` to a normalized
Hilbert--Schmidt matrix ultraproduct. It remains to see that `x` survives.
After decreasing `c` slightly, `(FFA14)`, `(FFA6)`, and `(FFA9)` give
eventually

`0<=tr(Psi_n(x))<=a:=1-c^2/4<1`.                        `(FFA18)`

Therefore

`||Psi_n(x)-I||_2^2`
` =2-2 tr(Psi_n(x)) >=2-2a=c^2/2>0`,                    `(FFA19)`

so `Psi(x)!=1`.

Let `Q=Psi(H)`. It is hyperlinear because it is a subgroup of a tracial
matrix ultraproduct. If `Q` were sofic, the quotient homomorphism
`H->Q` would kill every element of `Rad_sof(H)`, contradicting
`Psi(x)!=1`. Hence `Q` is nonsofic. End proof.

No separation hypothesis is imposed on elements other than `x`. The
output is allowed to be a proper quotient of `H`; the radical condition is
exactly what makes that sufficient.

## 3. What this adds to the live routes

For an ordinary weak-MF model only the unweighted defects

`||phi_n(g)phi_n(h)-phi_n(gh)||_op ->0`                  `(FFA20)`

are known. The stronger rate `(FFA15)` is not automatic. Conjugate
fermionic amplification turns an operator-norm error `epsilon_n` into a
normalized Hilbert--Schmidt error at most
`sqrt(d_n/2) epsilon_n`, and there is no general relation between matrix
dimension and approximation error.

Nevertheless `(FFA15)` is a concrete sufficient target for either explicit
candidate already in the repository:

1. the Kun--Thom symmetric double, with `x` any explicit nontrivial radical
   word; or
2. the cyclic shear quotient models before adjoining the central phase.

For the symmetric double, Shulman's lifting proof has two independent
indices: an asymptotic-homomorphism index controlling the norm defect and a
matrix-coordinate index realizing the lifted representation. A successful
quantitative diagonal choice satisfying `(FFA15)` would now finish the main
problem immediately through Theorem 4. Merely knowing strong convergence
of each lift does not supply that choice; its visibility threshold may grow
faster than the reciprocal defect.

The criterion also explains why tensor/exterior amplification was close but
not yet complete in earlier notes. One does **not** need the amplified trace
to converge to zero or the input witness to occupy positive rank. A single
outlying eigenvalue gives the uniform gap `(FFA19)`. The only remaining
cost is the square-root-dimension-weighted multiplicative error `(FFA15)`.

## 4. Sanity checks

* Direct-sum amplification of the input does not help `(FFA15)`: it leaves
  the defect unchanged and increases `d_n`.
* The construction does not conflict with the rank-spiky example
  `diag(lambda_n,1,...,1)`. Fermionic amplification makes its trace
  visible, but a group multiplication error is simultaneously amplified by
  the input dimension.
* If the maps in `(FFA13)` are honest representations, `(FFA15)` is automatic.
  The theorem then says that an honest finite-dimensional representation
  detecting `x` contradicts `x in Rad_sof(H)`, as it should: a countable
  linear group is a directed union of finitely generated residually finite
  groups and hence is sofic.

Thus the theorem is a genuine approximate regime, not a disguised use of
finite-image representations.

## 5. The square-root loss is functorially optimal

The factor `sqrt(d)` in `(FFA8)` is not an artifact of taking every exterior
power. It is forced, up to a universal constant, for any exact continuous
unitary functor which makes a rank-one outlier visible in normalized
Hilbert--Schmidt norm.

Let

`R:U(d)->U(N)`                                             `(FFA21)`

be a continuous homomorphism. Equip the Lie algebras with operator norm on
`u(d)` and normalized Hilbert--Schmidt norm on `u(N)`, and put

`Lip_2(R)=sup_(||X||_op<=1) ||dR(X)||_(2,N)`.              `(FFA22)`

More generally, for `1<=r<=d`, let

`s_r=diag(-I_r,I_(d-r)) in U(d)`,
`Delta_(R,r)=||R(s_r)-I||_(2,N)`.                         `(FFA23)`

**Theorem 5 (functorial square-root lower bound).** Every `(FFA21)`
satisfies

`Lip_2(R) >= (sqrt(floor(d/r))/pi) Delta_(R,r)`            `(FFA24)`

for every `1<=r<=d`. In particular, at `r=1`,

`Lip_2(R) >= (sqrt(d)/pi) Delta_(R,1)`.                    `(FFA24a)`

**Proof.** Put `m=floor(d/r)` and choose pairwise orthogonal coordinate
projections `P_1,...,P_m`, each of rank `r`. Put

`X_j=i P_j in u(d)`, `A_j=dR(X_j) in u(N)`.               `(FFA25)`

The element `exp(pi X_j)` is a rank-`r` involution conjugate to `s_r`.
Consequently its image under `R` has normalized Hilbert--Schmidt distance
`Delta_(R,r)` from the identity. Since a continuous Lie-group homomorphism
intertwines exponentials,

`R(exp(pi X_j))=exp(pi A_j)`.                              `(FFA26)`

For every skew-adjoint matrix `A`, spectral calculus and
`|exp(i t)-1|<=|t|` give

`||exp(A)-I||_2<=||A||_2`.                                 `(FFA27)`

Equations `(FFA26)--(FFA27)` therefore imply

`||A_j||_(2,N) >= Delta_(R,r)/pi` for every `j`.           `(FFA28)`

Choose independent Rademacher signs `epsilon_1,...,epsilon_m`. Because the
normalized Hilbert--Schmidt norm is a Hilbert-space norm,

`E ||sum_j epsilon_j A_j||_(2,N)^2`
`   =sum_j ||A_j||_(2,N)^2`
`   >=m Delta_(R,r)^2/pi^2`.                              `(FFA29)`

Hence some deterministic choice of signs satisfies

`||sum_j epsilon_j A_j||_(2,N)`
`   >=sqrt(m) Delta_(R,r)/pi`.                            `(FFA30)`

But `X=sum_j epsilon_j X_j` has operator norm one, and linearity of the
differential gives `dR(X)=sum_j epsilon_j A_j`. Taking the supremum in
`(FFA22)` proves `(FFA24)`. End proof.

For the phase-cancelled fermionic functor `G_d`, the rank-one involution has
normalized trace zero and hence `Delta_(G_d)=sqrt(2)`. Its differential at
the identity satisfies

`sup_(||X||_op<=1)||dG_d(X)||_2=sqrt(d/2)`.                `(FFA31)`

Indeed, for eigenvalues `i alpha_j` of `X`, expanding `(FFA10)` at
`W=exp(tX)` gives

`||G_d(exp(tX))-I||_2^2`
`   =(t^2/2) sum_j alpha_j^2+O(t^4)`.                     `(FFA32)`

The upper bound is attained when every `|alpha_j|=1`. Comparing
`(FFA24)` and `(FFA31)` shows that `G_d` is within the universal factor
`pi/2` of the best possible local Lipschitz constant among all continuous
homomorphisms which give the same rank-one visibility.

Writing `delta=r/d` for the relative input rank, `(FFA24)` says that fixed
visibility on a rank-`r` involution costs at least order
`1/sqrt(delta)` whenever `r<=d/2`. This is the same density scaling as the
corner-normalization estimate `error/sqrt(delta)` in the shrinking-Clifford
criterion. Thus the rank-one `sqrt(d)` phenomenon and the sparse-sector
threshold are two instances of one unavoidable functorial law.

Thus no replacement of the full exterior algebra by another exact
finite-dimensional representation of `U(d)` can remove the square-root
dimension gate while still uniformly amplifying a single spectral outlier.
A rate-free FALSE proof has to use additional structure of the candidate
group--for example a central corner, a Kazhdan corner, or a special
nonfunctorial projective sector--rather than a better universal matrix
functor.
