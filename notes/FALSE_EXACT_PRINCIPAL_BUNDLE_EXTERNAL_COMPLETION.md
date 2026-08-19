# The radical clock has an exact principal-bundle external completion

Date: 2026-08-11

## 1. Outcome

The abstract external-group gate left in
`FALSE_RADICAL_BS_Q_BIMODULE_EXTENSION.md` has an exact finite solution.
No unitary optimization or Plancherel deletion is needed if one allows the
external transvection to carry a commuting finite-quotient permutation
factor.

Let `F,K` be finite groups and let `a in F`, `b in K` have the same finite
order.  There is an exact permutation representation of `K` on the trivial
principal `F`-bundle `F times K` which commutes with the left `F`-action and
sends `b` to

`R_F(a) tensor L_K(b)`.                                `(PBE1)`

For the radical clock take

`F=SL_3(Z/p^(k+1)Z)`,
`a=diag(1+p,1,(1+p)^(-1))^(-1)`,                      `(PBE2)`

and

`K=SL_d(Z/p^k Z)`, `b=I+e_12`.                       `(PBE3)`

Both selected elements have order exactly `p^k`.  Pulling the construction
back along `SL_d(Z)->K` gives two exact external representations on the same
space:

* the untwisted finite-quotient action, where `b` acts as
  `1 tensor L_K(b)`; and
* the gauged action, where `b` acts as `(PBE1)`.

Tensor the coefficient representation from
`FALSE_RADICAL_BS_Q_BIMODULE_EXTENSION.md` with `ell^2(K)`.  The two
external actions commute exactly with the common left `F` action and satisfy
every relation of `SL_d(Z)` exactly.  On the common coefficient operator
`Gamma=D(e_1) tensor 1`, their two compressor images give

`Gamma` and `Gamma^(1+p)`                              `(PBE4)`

for the two copies of the marked Laurent element.  Their fold is
`Gamma^p`, with

`tr(Gamma^p)=0`, `||Gamma^p-1||_2^2=2`.               `(PBE5)`

Thus the following parts of the frozen-clock extension are now simultaneous
and exact:

1. the additive coefficient square-zero relations;
2. the coefficient `SL_3` covariance;
3. every abstract external `SL_d` relation;
4. every cross-commutator between the coefficient `SL_3` group and the
   external `SL_d` group;
5. the selected `t,s` covariance needed by the marked BS slice; and
6. the macroscopic marked fold.

The second commuting transvection `s=I+e_13` can simultaneously be assigned
no fiber holonomy.  This makes the marked Baumslag--Solitar relation exact,
not only the abstract external presentation.  The remaining gate is the
covariance of the other Laurent-labelled tangent operators and the base
elementary group.  The principal-bundle gauge below gives an explicit finite
`F`-valued cocycle for that next calculation; it does not by itself define
those operators.

## 2. Exact prescribed-fiber theorem

Use left multiplication `L_F` and right multiplication `R_F` on `F`.  Let
`m` be the common order of `a` and `b`.  Left multiplication by `b` splits
`K` into cycles of length `m`.  Choose one point in each cycle and define

`phi(b^j x)=phi(x)a^j`, `0<=j<m`,                     `(PBE6)`

with `phi(x)=1` on the chosen representatives.  The equality `a^m=1`
makes `(PBE6)` well-defined.

Let `P(k)` be the ordinary left regular action of `K` on the second
coordinate of `F times K`, and define the fiber gauge

`W delta_(f,x)=delta_(f phi(x),x)`.                   `(PBE7)`

Put

`Psi(k)=W P(k) W^(-1)`.                               `(PBE8)`

This is an exact representation because it is a conjugate of `P`.  Directly,

`Psi(k)delta_(f,x)`
` =delta_(f phi(x)^(-1)phi(kx),kx)`.                  `(PBE9)`

Every fiber multiplier in `(PBE9)` is on the right, so `Psi(K)` commutes
with the whole left regular action `L_F(F)`.  Equation `(PBE6)` gives

`phi(x)^(-1)phi(bx)=a`,                               `(PBE10)`

and hence

`Psi(b)=R_F(a) tensor L_K(b)`.                        `(PBE11)`

This proves the theorem.

There is a subgroup version which will be needed below.  Let `H<=K` and let

`theta:H->F`                                           `(PBE11a)`

be an antihomomorphism, so
`theta(h_1 h_2)=theta(h_2)theta(h_1)`.  Choose one representative `x` of
each left `H`-orbit in `K` and put

`phi(hx)=theta(h)`.                                   `(PBE11b)`

Left multiplication is free, so this is well-defined.  Repeating
`(PBE7)--(PBE9)` gives

`Psi(h)=R_F(theta(h)) tensor L_K(h)` for every `h in H`. `(PBE11c)`

For an abelian `H` with abelian image, an ordinary homomorphism is also an
antihomomorphism.

The construction has a useful cocycle form.  Define

`zeta(k,x)=phi(x)^(-1)phi(kx) in F`.                  `(PBE12)`

Then

`zeta(k ell,x)=zeta(ell,x)zeta(k,ell x)`,             `(PBE13)`

and `zeta(b,x)=a` at every point.  Therefore the desired fixed clock
increment is already an exact nonabelian coboundary on a finite
`SL_d`-set.  The unresolved issue is not the external group law; it is how
to make the tangent characters transform under the varying values
`zeta(k,x)` while agreeing on the fixed polynomial window.

## 3. Matching orders in the radical construction

Fix an odd prime `p` and put `q=1+p`.  In

`F_k=SL_3(Z/p^(k+1)Z)`,                               `(PBE14)`

let

`c_k=diag(q,1,q^(-1))`.                               `(PBE15)`

The lifting-the-exponent formula gives

`v_p(q^j-1)=1+v_p(j)`                                 `(PBE16)`

for nonzero `j`.  Consequently `c_k` has order exactly `p^k`.

In

`K_k=SL_d(Z/p^k Z)`,                                  `(PBE17)`

the elementary transvection

`t_k=I+e_12`                                          `(PBE18)`

satisfies `t_k^j=I+j e_12`, so it also has order exactly `p^k`.  Put

`s_k=I+e_13`.                                         `(PBE18a)`

The two transvections commute and generate

`H_k=<t_k,s_k>~=(Z/p^k Z)^2`.                         `(PBE18b)`

Apply the subgroup theorem with

`theta_k(t_k^i s_k^j)=c_k^(-i)`.                     `(PBE18c)`

Its image is cyclic, so `(PBE18c)` is both a homomorphism and an
antihomomorphism.  In particular, the resulting gauge satisfies

`Psi(t_k)=R_F(c_k^(-1)) tensor L_K(t_k)`,
`Psi(s_k)=1 tensor L_K(s_k)`.                         `(PBE18d)`

Let `rho_k:SL_d(Z)->K_k` be reduction modulo `p^k`.  On

`ell^2(F_k) tensor ell^2(K_k)`, define

`Phi_(0,k)(s)=1 tensor L_K(rho_k(s))`,
`Phi_(1,k)(s)=Psi(rho_k(s))`.                         `(PBE19)`

Both are exact representations of the full external group, and both
commute with `L_F(F_k) tensor 1`.  At the distinguished transvection,

`Phi_(0,k)(t)=1 tensor L_K(t_k)`,
`Phi_(1,k)(t)=R_F(c_k^(-1)) tensor L_K(t_k)`.          `(PBE20)`

The common factor `L_K(t_k)` is harmless for the fold calculation: it
commutes with every coefficient operator.

## 4. The exact two-sector fold

Use the coefficient operator from the `Q`-bimodule construction,

`Gamma_k=D_k(e_1) tensor 1`.                          `(PBE21)`

For the untwisted external action, conjugation by the first matrix in
`(PBE20)` fixes `Gamma_k`.  For the gauged action, equation `(QBE14)` gives

`Phi_(1,k)(t)^(-1) Gamma_k Phi_(1,k)(t)`
` =Gamma_k^q`.                                        `(PBE22)`

Thus the two images of

`h=t^(-1) gamma t`                                    `(PBE23)`

are precisely the sectors in `(PBE4)`.  The extra permutation factor in
`(PBE20)` cancels from `(PBE22)`.

The stable external transvection `s=I+e_13` commutes with `t` in
`SL_d(Z)`.  Equation `(PBE18d)` also makes its gauged image act trivially on
the `F_k` coordinate.  Hence it commutes with `Gamma_k`, not merely with the
compressor.  Combining this with the left coefficient action of `c_k` proves
the exact stable-letter identity

`pi_i(c) pi_i(h) pi_i(c)^(-1)=pi_i(h)^q`              `(PBE23a)`

in both sectors.  Left/right regular commutation supplies the remaining
coefficient/external cross-commutators.  Therefore all abstract `Q times L`
relations used by the marked Baumslag--Solitar slice are exact.

Finally, `(QBE6)` is unchanged by tensoring with `ell^2(K_k)`, so `(PBE5)`
follows.

## 5. Paired Fourier-cell splice

The unitary-fiber form of the same bundle argument and its application to
the two finite-order Fourier compressors are proved in
`FALSE_PAIRED_FOURIER_PRINCIPAL_BUNDLE_SPLICE.md`.  It gives two honest
external `SL_d(Z)` representations whose distinguished transvection fibers
are the two paired compressors and whose commuting stable transvection has
trivial fiber holonomy.  Consequently the entire marked Fourier cell and
every abstract external relation are exact simultaneously.  The separate
note also proves the required finite-order Clifford statement, so it is the
canonical source for that splice.

## 6. What remains

The theorem closes the finite optimization `(QBE29)` in a stronger form:
its defect can be taken to be exactly zero after the harmless common
finite-quotient permutation factor is included.

It does **not** yet define the images of

`sl_r(V_k[x_1^(+-1),...,x_d^(+-1)])`                  `(PBE24)`

or of the base elementary group.  Those operators must satisfy three
conditions simultaneously:

1. the two vertex models agree asymptotically on every fixed polynomial
   generator;
2. conjugation by `(PBE19)` implements monomial substitution; and
3. the marked negative monomial retains `(PBE5)`.

For external generators outside the selected commuting subgroup
`<t,s>`, the fiber cocycle in `(PBE12)` can also move the coefficient
diagonal.  Correcting that motion is part of the same tangent-covariance
problem; only the precise marked `t,s` slice has been made exact here.

Equation `(PBE12)` is the exact finite cocycle which has to be absorbed by
the tangent-character model.  A useful next reduction is therefore to work
in the dual of the finite square-zero tangent module and ask for two orbit
measures whose restrictions to the fixed positive window approach one
another, while their `t`-transport differs by the constant fiber holonomy
`c_k^(-1)`.  Generic external-unitary optimization is obsolete.
