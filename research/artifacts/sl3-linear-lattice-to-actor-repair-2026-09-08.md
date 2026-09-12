# Linear correction from the exact SL3 lattice to its arithmetic actor

2026-09-08. This proof consumes the all-prime quadratic primary-mass
theorem. It strengthens the sector conclusion to actual correction of
the denominator generator in the original matrix dimension.

## 1. Input and the only group identities used

Fix a prime `p`, put `C=SL_3(Z)`, `A=SL_3(Z[1/p])`,
`h=diag(p,1,p^-1)`, and `D=C cap h^-1 C h`. Fix a finite Kazhdan
generating set `S_D`, with constant `kappa_D`. For signed permutation
matrices `w_12,w_23 in C`, set

    h'=w_12 h w_12^-1=diag(1,p,p^-1),
    h''=w_23 h w_23^-1=diag(p,p^-1,1).

The needed Weyl identity is

    h(h'')^-1=h'.                                        (LR1)

Let `sigma:C->U(d)` be exact of finite congruence level `p^a m`, with
`gcd(m,p)=1`, and let `H` be any unitary. No full approximate actor is
assumed at this stage. Define

    epsilon_D=max_(s in S_D)
      ||H sigma(s)-sigma(h s h^-1)H||_2,
    epsilon_W=||H( sigma(w_23)H sigma(w_23)* )*
                   -sigma(w_12)H sigma(w_12)*||_2.       (LR2)

Only these finitely many local constraints are used.

## 2. Removing the primary summand without compressing the actor

Use the Chinese-remainder decomposition of the finite quotient. Let `P`
be the projection onto the subspace on which the whole primary factor
acts trivially, and put `q=tr(1-P)`. The primary theorem gives

    q<=C_p epsilon_D^2.                                  (LR3)

Because the primary and coprime factors commute, `P` commutes with all
of `sigma(C)`. Define on the original space

    sigma_0(c)=P sigma(c)P+(1-P).                         (LR4)

The right side is a genuine representation of `C`; it is the retained
coprime representation plus a trivial representation on the discarded
summand. It factors through `SL_3(Z/m)` and has the same dimension `d`.
Uniformly for all `c in C`,

    ||sigma(c)-sigma_0(c)||_2<=2 sqrt(q).                 (LR5)

The matrix `H` is kept unchanged. No assertion that `P` commutes with
`H` enters the construction. If desired, its large trace alone gives
`||[P,H]||_2<=2 sqrt(q)`, but the proof never compresses `H` and never
has to polar-correct that compression.

Replacing `sigma` by `sigma_0` changes each overlap expression in
`(LR2)` by at most `4 sqrt(q)`. Replacing either conjugation
`sigma(w_ij)H sigma(w_ij)*` costs at most `4 sqrt(q)`, so the Weyl
expression changes by at most `8 sqrt(q)`. Therefore the new defects
satisfy

    epsilon_(D,0)<=epsilon_D+4 sqrt(q),
    epsilon_(W,0)<=epsilon_W+8 sqrt(q).                  (LR6)

This is the quantitative version of the existing
`coprime-sector-collapse-is-robust-to-small-p-admixture`. There is no
new corner-invariance obligation in that passage.

## 3. A direct coprime correction estimate

The coprime reduction `A->SL_3(Z/m)` extends `sigma_0` to an exact
representation `rho:A->U(d)`. Write

    H_0=rho(h),       H_0'=rho(h'),       H_0''=rho(h''),
    W=H_0*H,         R=sigma_0(C)' cap M_d.

The subgroup `D` contains `C(p^2)` and surjects onto `SL_3(Z/m)`:
Chinese remaindering modulo `p^2m` supplies representatives equal to
the identity modulo `p^2` and arbitrary modulo `m`. Hence
`sigma_0(D)'=R`.

For every `s in S_D`, exactness of the congruence slot gives

    H_0 sigma_0(s)=sigma_0(h s h^-1)H_0.

Multiplying the new overlap residual by `H_0*` shows that

    max_(s in S_D)||[W,sigma_0(s)]||_2<=epsilon_(D,0).

Conjugation by the exact representation of `D` has fixed space `R`.
Its Kazhdan estimate therefore gives

    beta:=||W-E_R(W)||_2<=epsilon_(D,0)/kappa_D.         (LR7)

Define `W_ij=sigma_0(w_ij)W sigma_0(w_ij)*`. Since `E_R(W)` commutes
with every lattice matrix,

    ||W_ij-W||_2<=2 beta.                               (LR8)

There is no need to round `E_R(W)` to a unitary. Keep the original
unitary `W`. Substitution in the Weyl expression gives

    H( sigma_0(w_23)H sigma_0(w_23)* )*
      =H_0 W W_23* (H_0'')*,
    sigma_0(w_12)H sigma_0(w_12)*=H_0' W_12.

By `(LR1)`, `H_0(H_0'')*=H_0'`. Thus the first displayed term is
within `2 beta` of `H_0'`; the second is within `2 beta` of `H_0'W`.
Triangle inequality yields

    ||H-H_0||_2=||W-I||_2
      <=epsilon_(W,0)+4 beta
      <=epsilon_W+8 sqrt(q)
         +(4/kappa_D)(epsilon_D+4 sqrt(q)).              (LR9)

Combining `(LR3)`, `(LR5)`, and `(LR9)` proves `(LAR1)` and `(LAR2)`.
The estimate holds for all defect sizes; no small-defect cutoff is
required. The constants depend on `p` and the fixed overlap data.

## 4. All lattice-exact actor models

Let `phi_n:A->U(d_n)` be an asymptotic homomorphism. Suppose exact
congruence representations `sigma_n:C->U(d_n)` approximate
`phi_n|_C` on a fixed finite lattice generating set. For every fixed
`c in C`, word telescoping then gives
`||phi_n(c)-sigma_n(c)||_2->0`. With `H_n=phi_n(h)`, asymptotic
multiplicativity of `phi_n` gives both defects in `(LR2)` tending to
zero. The theorem produces exact full arithmetic representations
`rho_n` with

    ||phi_n(c)-rho_n(c)||_2->0       (c in C),
    ||phi_n(h)-rho_n(h)||_2->0.

Since `A=<C,h>`, fixed-word telescoping proves

    ||phi_n(g)-rho_n(g)||_2->0       for every g in A.   (LR10)

This conclusion holds at every prime, including two, with arbitrary
congruence depths and multiplicities. The same argument holds along
a given ultrafilter. No canonical trace is used; if the original
actor has canonical limiting trace, `(LR10)` preserves it.

The representation `pi=[phi_n]` therefore has the same ultraproduct
values as a coprime congruence sequence. The established coprime
commutant theorem gives

    pi(C)' cap Q=pi(A)' cap Q.                          (LR11)

The established coprime carrier-control theorem likewise excludes
every scalar relative matrix witness over this actor. Its carriers
need no modification: replacing a matrix by an `o(1)`-close one
preserves its distance to a fixed subalgebra and its conditional
expectation up to `o(1)` by contraction of the expectation.

In particular, `(LR11)` proves the conclusion of the existing open
`lambda-exact-face-closes-at-p-three` for every prime `p=3 mod 4`,
without its invalidated flux construction. The stronger theorem
also closes the exact lattice face at `p=2`. It does not change the
status of the full arithmetic commutant-collapse claim, whose actor
restriction need not be close to any exact lattice representation.

## 5. Independent audit of the primary amplification

The prerequisite is `sl3-primary-mass-has-a-uniform-quadratic-gap`.
Its qualitative proof was inspected in the evolving artifact
`independent-kirillov-primary-sector-audit-2026-09-08.md`. The external
orbit-method inputs were checked directly in
[Boyarchenko--Sabitova, Theorems 2.6 and
2.8](https://arxiv.org/pdf/math/0608126), printed pages 12 and 14.
At the prime two, the character Fourier formula is restricted to
the square subgroup; this restriction is retained at both depths.
The extra two CRT digits before conjugation and the fixed-lattice
coupling at projective infinity are also needed by that proof.

Here is an independent check of the step from qualitative to quadratic
mass control. Suppose `q_n/epsilon_n^2` were unbounded. Projecting the
original fixed-overlap intertwiner first gives uniform primary-factor
intertwining error at most `2 epsilon_n/kappa_D`. Left multiplication
through the primary representation has fixed projection of trace
`1-q_n`, so a fixed Kazhdan set for `C` supplies a generator `s` with

    ||sigma_(n,p)(s)-I||_2^2>=kappa_C^2 q_n,

after passing to a subsequence to fix `s` if necessary.

Replace the primary actor by

    theta_n=(sigma_(n,p) direct_sum 1)
               tensor conjugate(sigma_(n,p) direct_sum 1),

and apply the same operations to its intertwining unitary. For any
original unitary residual `R`, the new residual has normalized trace

    t=|(1+tr(R))/2|^2 in [0,1],
    2(1-t)<=||R-I||_2^2.                               (LR12)

For the selected generator the reverse bound is

    tr(theta_n(s))<=1-kappa_C^2 q_n/4.                  (LR13)

Take `r_n=ceil(1/q_n)` tensor powers. All new residual traces remain
nonnegative, so

    defect_squared<=4 r_n epsilon_n^2/kappa_D^2->0,
    tr(theta_n(s)^(tensor r_n))
      <=exp(-kappa_C^2/4)<1.                            (LR14)

The transformed actor still factors through a finite primary quotient.
Qualitative primary-mass vanishing would make its selected generator
converge to the identity, contradicting `(LR14)`. This proves existence
of a uniform quadratic constant. It gives no algorithm for that constant.

## 6. Research boundary and duplication check

Repository searches covered lattice-exact correction, same-dimensional
congruence repair, the existing small-admixture lemma, and the unbalanced
torus coordinate theorem. The latter already controls projective energies
when a full arithmetic reference is supplied; it does not construct that
reference from an arbitrary primary lattice packet. The result here
provides it with a linear ordinary-HS bound.

No local code, numerical search, or build was used. This is a finite
matrix argument consuming the named primary theorem. It is an exact
lattice-sector result, not a proof of full lattice stability or of the
nonhyperlinear-group objective.
