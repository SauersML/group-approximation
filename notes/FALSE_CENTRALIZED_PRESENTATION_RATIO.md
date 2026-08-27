# The universal centralized-presentation ratio

Date: 2026-08-11

## 1. Outcome

**Closure update for the explicit symmetric double.** Its universal ratio is
finite for every radical word. The full finite residual \(R\) satisfies
\(R=[D,R]\), which forces one fixed integral relator expression in every
canonical finite quotient. See
`FALSE_FINITE_RESIDUAL_COMMUTATOR_NO_GO.md`.

For a finitely presented group `P` and a nontrivial word in its sofic
radical, every finite central-relator search factors through one canonical
finitely presented group.  On each finite quotient, the radical word
automatically becomes a central product of the defining relators.

This gives a scalar finite-quotient criterion for FALSE.  One no longer has
to guess a finite central extension or unitary matrices.  It is enough to
make one character see the radical word much more strongly than it sees all
defining relators.

## 2. Universal relation centralization

Let

`P=<s_1,...,s_d | r_1,...,r_l>=F/N`,                 `(UCR1)`

where `F=F(s_1,...,s_d)` and `N` is the normal closure of the relators.
Define

`P_tilde=F/[F,N]`, `A=N/[F,N]`.                       `(UCR2)`

Then

`1->A->P_tilde->P->1`                                 `(UCR3)`

is a central extension.  Moreover `A` is generated as an abelian group by
the images of `r_1,...,r_l`.  Indeed every element of `N` is a product of
conjugates of the relators, and all conjugates become equal modulo `[F,N]`.

The group `P_tilde` has the finite presentation

`P_tilde=<s_1,...,s_d | [r_j,s_i]=1`
`                         for 1<=j<=l, 1<=i<=d>`.     `(UCR4)`

To verify `(UCR4)`, the displayed relations lie in `[F,N]`.  Conversely,
once every `r_j` commutes with every generator, the image of `N` is central,
so all of `[F,N]` vanishes.

Fix a word `w in F` whose image is a nonidentity element of
`Rad_sof(P)`.  Let

`q:P_tilde->E`                                        `(UCR5)`

be any homomorphism to a finite group.  The subgroup `q(A)` is central in
`E`.  The quotient map

`P->E/q(A)`                                           `(UCR6)`

has finite target.  Radicality of `w` therefore gives

`q(w) in q(A)`.                                       `(UCR7)`

Thus both the defining-relator values and the marked value lie in one
finite central abelian group, without any extra constraint in the search.

## 3. The character ratio

For a finite quotient `(UCR5)` and a character

`chi:q(A)->T`,                                        `(UCR8)`

put

`D_R(q,chi)^2=sum_(j=1)^l |chi(q(r_j))-1|^2`,         `(UCR9)`

`D_w(q,chi)=|chi(q(w))-1|`.                           `(UCR10)`

If `D_R(q,chi)=0`, then `chi` is trivial on the generators of `q(A)`, so
`D_w(q,chi)=0` by `(UCR7)`.  Hence a positive numerator never occurs with
zero denominator.

Define the universal central ratio

`C_cent(P,w)=sup_(q,chi) D_w(q,chi)/D_R(q,chi)`,      `(UCR11)`

where the supremum ranges over finite quotients of `P_tilde` and characters
of `q(A)`, and `0/0` is read as zero.

**Theorem 1 (centralized-presentation FALSE criterion).**  If

`C_cent(P,w)=infinity`,                               `(UCR12)`

then there exists a hyperlinear nonsofic group.

**Proof.**  Choose finite quotients `q_n` and characters `chi_n` such that

`D_R(q_n,chi_n)/D_w(q_n,chi_n)->0`,                   `(UCR13)`

with `D_w(q_n,chi_n)>0`.  Write

`chi_n(q_n(w))=exp(i theta_n)`, `0<|theta_n|<=pi`.    `(UCR14)`

Choose a positive integer `m_n` as follows.  If
`|theta_n|>=pi/2`, take `m_n=1`; otherwise take

`m_n=ceil(pi/(2|theta_n|))`.                          `(UCR15)`

Then

`|chi_n(q_n(w))^(m_n)-1|>=sqrt(2)`,                  `(UCR16)`

and

`m_n<=pi/D_w(q_n,chi_n)`.                             `(UCR17)`

The second inequality uses
`|exp(i theta)-1|<=|theta|`.  For every relator,

`|chi_n(q_n(r_j))^(m_n)-1|`
` <=m_n |chi_n(q_n(r_j))-1|`.                         `(UCR18)`

Consequently

`sum_j |chi_n(q_n(r_j))^(m_n)-1|^2`
` <=pi^2 D_R(q_n,chi_n)^2/D_w(q_n,chi_n)^2 ->0`.      `(UCR19)`

Apply the multi-central relator-separation theorem from
`FALSE_CENTRAL_RELATOR_SEPARATION_CRITERION.md` to the finite groups
`q_n(P_tilde)`, the central subgroups `q_n(A)`, and the powered characters
`chi_n^(m_n)`.  Equations `(UCR16)` and `(UCR19)` are exactly its marked
separation and vanishing-relator hypotheses.  Its tracial-ultraproduct
image is hyperlinear, retains `w`, and cannot be sofic.  QED

## 4. Universality among finite central-relator models

Conversely, suppose elements `u_1,...,u_d` of a finite group `E` have the
property that every

`r_j(u_1,...,u_d)`                                    `(UCR20)`

is central in the subgroup `E_0=<u_1,...,u_d>`.  Sending `s_i` to `u_i`
kills every relation in `(UCR4)`, so it defines a homomorphism

`P_tilde->E_0`.                                       `(UCR21)`

Thus every finite central-relator certificate is already a finite quotient
of `P_tilde`.  The search space in Theorem 1 loses no such models.

This also identifies the collision mechanism.  In every finite quotient,
`q(w)` is a product of the central relator values:

`q(w)=product_j q(r_j)^(c_j(q))`.                     `(UCR22)`

The coefficient vector depends on the quotient.  If the ratio `(UCR11)`
diverges, these quotient-dependent coefficients amplify characters which
are almost trivial on every fixed relator into a nontrivial marked phase.
No fixed integral expression can do this.

## 5. Computational form

The group in `(UCR4)` is explicit and finitely presented.  A finite search
stage needs only:

1. a finite quotient `q` of `(UCR4)`;
2. the finite abelian group `q(A)` generated by the relator images;
3. the marked element `q(w) in q(A)`; and
4. the maximum of `(UCR11)` over the finite dual group `q(A)^hat`.

The fourth item is an exact finite Fourier calculation.  If the maximum
grows without bound along a quotient family, Theorem 1 is the complete
FALSE proof.  If it stays uniformly bounded, that family satisfies the
central scalar domination inequality

`D_w(q,chi)<=C D_R(q,chi)`                            `(UCR23)`

and cannot support the frozen-clock extension.

For the fold-aligned Kun--Thom double, the existing integral
Baumslag--Solitar class gives natural `p^k`-primary quotient data, but its
order alone does not prove divergence of `(UCR11)`.  What must be computed
is the position of the marked collision vector relative to the fixed
relator-generator vectors in the finite central module.  This is the exact
finite discriminant/incidence problem left by the cyclic-wall no-go.
