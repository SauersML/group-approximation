# Regular bundles free the relative holonomy table, but expose the kernel gate

Date: 2026-08-12

## 1. Outcome

There are two distinct issues in the external globalization problem, and they
should not be conflated.

First, if a finite group `K` genuinely acts on the fiber group, then passing
to the regular base `K` removes every cocycle constraint on the relative
holonomy table.  An arbitrary table

`t:K -> U(V)`

is realized by two exact external representations.  Pointwise Pauli walls
from `FALSE_POSITIVE_COMMUTANT_CHARACTER_MATCHING.md` may therefore be chosen
independently at all regular-base points.  There is no residual twisted-CSP
condition in this case.

Second, the actual Laurent action is an action of the infinite external group
`L`, and generally does **not** factor through the chosen finite quotient

`q:L -> K`.

After choosing a section `sigma:K -> L`, the discrepancy is the kernel-valued
Schreier carry

`kappa(s,x)=sigma(q(s)x)^(-1) s sigma(x) in ker(q)`.       `(RBF1)`

The covariance defect of the induced matrix model is exactly the averaged
failure of the basepoint map to intertwine the automorphisms
`alpha_(kappa(s,x))`.  Thus regularization frees the **relative wall table**,
but it does not erase the real Schreier transition problem.  It separates it
from the wall choice.

There is also a useful tensor-atlas observation.  One local wall assigned to
one tensor factor retains its full normalized-Hilbert--Schmidt marked energy;
it is not diluted by the number of charts.  Multiplicativity defects add.
Consequently a finite family of chartwise models with total defect `o(1)` can
be combined without nonorthogonal fusion.  What remains is to produce the
models with sufficiently small kernel-covariance defect.  This is precisely
where the three Schreier moments, or a genuinely non-scalar replacement,
enter.

## 2. Exact regular-bundle construction

Let `K` be a finite group acting by automorphisms

`alpha:K -> Aut(G)`.                                      `(RBF2)`

Let `V` be a finite-dimensional Hilbert space.  For `i=0,1`, let

`pi_i:G -> U(V)`                                          `(RBF3)`

be arbitrary maps with `pi_i(1)=1`; they need not be homomorphisms.  Choose
arbitrary unitary tables

`u_i:K -> U(V)`.                                          `(RBF4)`

On

`H=ell^2(K) tensor V`                                     `(RBF5)`

define block-diagonal fiber maps by

`Phi_i(g)|_x`
` =Ad(u_i(x)) pi_i(alpha_(x^(-1))g)`, `x in K`,            `(RBF6)`

and define external unitaries by

`U_i(k)(delta_x tensor xi)`
` =delta_(kx) tensor u_i(kx)u_i(x)^* xi`.                 `(RBF7)`

### Theorem 1 (free-table regular completion)

The maps `U_i` are exact representations of `K`, and

`U_i(k) Phi_i(g) U_i(k)^*=Phi_i(alpha_k g)`               `(RBF8)`

for every `k in K`, `g in G`.  Moreover, with normalized
Hilbert--Schmidt norm,

`||Phi_i(gh)-Phi_i(g)Phi_i(h)||_2^2`
` =(1/|K|) sum_(x in K)`
`   ||pi_i(alpha_(x^(-1))(gh))`
`     -pi_i(alpha_(x^(-1))g)pi_i(alpha_(x^(-1))h)||_2^2.` `(RBF9)`

Put

`t(x)=u_1(x)^*u_0(x)`.                                    `(RBF10)`

Then

`||Phi_0(g)-Phi_1(g)||_2^2`
` =(1/|K|) sum_x`
` ||Ad(t(x))pi_0(alpha_(x^(-1))g)`
`                  -pi_1(alpha_(x^(-1))g)||_2^2.`          `(RBF11)`

Every unitary table `t:K->U(V)` occurs in `(RBF10)`; for example take
`u_0(x)=1` and `u_1(x)=t(x)^*`.

### Proof

Equation `(RBF7)` is conjugate to the left regular representation by the
block-diagonal unitary with `x`-block `u_i(x)`.  Hence it is an exact
representation.  On the block indexed by `kx`, conjugating `(RBF6)` by
`(RBF7)` gives

`Ad(u_i(kx)) pi_i(alpha_(x^(-1))g)`.

But

`alpha_(x^(-1))g=alpha_((kx)^(-1))(alpha_k g)`,

which is exactly the `kx`-block of the right side of `(RBF8)`.

The difference in `(RBF9)` is block diagonal.  Conjugation by `u_i(x)`
does not change normalized Hilbert--Schmidt norm, and the normalized trace
on `(RBF5)` averages the normalized traces of the `|K|` blocks.  This proves
`(RBF9)`.  Conjugating the `x`-block of the difference in `(RBF11)` by
`u_1(x)^*` gives the displayed summand, proving `(RBF11)`.  The last claim
is immediate from the stated choice of `u_0,u_1`.  End proof.

This theorem strengthens the regular-base part of the principal-bundle
splice: exactness of the external group imposes no relation at all among the
different values of the relative table.

## 3. Exact pointwise character matching on the regular base

Take one common basepoint representation `pi_0=pi_1=pi`.  Let `P subset G`
be the tested positive window and let `m in G` be marked.  If, for every
`x in K`, one can choose `t(x)` with

`[t(x),pi(alpha_(x^(-1))p)]=0`, `p in P`,                `(RBF12)`

then `(RBF11)` gives literal agreement

`Phi_0(p)=Phi_1(p)`, `p in P`.                           `(RBF13)`

At the same time the marked energy is exactly

`||Phi_0(m)-Phi_1(m)||_2^2`
` =(1/|K|) sum_x`
` ||Ad(t(x))pi(alpha_(x^(-1))m)`
`                    -pi(alpha_(x^(-1))m)||_2^2.`         `(RBF14)`

For a regular representation of a finite abelian tangent module, the
assignment theorem in
`FALSE_POSITIVE_COMMUTANT_CHARACTER_MATCHING.md` chooses each `t(x)` as a
Pauli character multiplier.  If the transformed marked class survives the
transformed positive subgroup at every `x`, every summand in `(RBF14)` is at
least `3`.  The choices are independent: no further cocycle congruence has
to be solved.

This does not contradict the natural finite-ring absorption theorem.  In
those honest finite quotient representations the positive image already
contains the marked Laurent image, so `(RBF12)` forces every summand in
`(RBF14)` to vanish.  Free choice of walls helps only after the local
positive/marked separation has been created.

## 4. The exact kernel-carry formula for the real action

Now let the infinite group `L` act on `G` by `alpha`, let

`q:L -> K`                                               `(RBF15)`

be a finite quotient, and choose a set-theoretic section

`sigma:K -> L`, `sigma(e)=e`.                            `(RBF16)`

For `s in L`, `x in K`, define `(RBF1)`.  It belongs to `ker(q)` because

`q(sigma(q(s)x))=q(s)x=q(s sigma(x))`.

For one basepoint map `pi:G->U(V)`, put

`Psi(g)|_x=pi(alpha_(sigma(x)^(-1))g)`.                  `(RBF17)`

Let `S(s)` be the plain permutation of the `K` blocks by `x |-> q(s)x`.

### Theorem 2 (kernel-carry identity)

For every `s in L`, `g in G`,

`||S(s)Psi(g)S(s)^*-Psi(alpha_s g)||_2^2`
` =(1/|K|) sum_(x in K)`
` ||pi(z_(x,g))-pi(alpha_(kappa(s,x))z_(x,g))||_2^2`,   `(RBF18)`

where

`z_(x,g)=alpha_(sigma(x)^(-1))g`.                        `(RBF19)`

More generally, if a unitary transition `v(s,x)` is placed on the edge
`x -> q(s)x`, then the corresponding summand is

`||Ad(v(s,x))pi(z_(x,g))`
`               -pi(alpha_(kappa(s,x))z_(x,g))||_2^2`. `(RBF20)`

### Proof

At the block `q(s)x`, the conjugated operator on the left of `(RBF18)` is
`pi(z_(x,g))`.  The target block is

`pi(alpha_(sigma(q(s)x)^(-1)) alpha_s g)`
` =pi(alpha_(sigma(q(s)x)^(-1)s sigma(x))`
`            alpha_(sigma(x)^(-1))g)`
` =pi(alpha_(kappa(s,x))z_(x,g))`.

Average the squared block norms.  Inserting an edge unitary gives `(RBF20)`
by the same calculation.  End proof.

Equation `(RBF20)` is the precise location of the real obstruction.  If the
action `alpha` factors through `K`, every `kappa(s,x)` acts trivially and
Theorem 1 applies without loss.  In the Laurent problem it does not.  The
clock coordinates of `v(s,x)` are exactly the Schreier data whose scalar
version is measured by `R_*` and `A_*`.

Thus the regular-bundle theorem corrects the endpoint as follows:

* relative Pauli walls may be selected pointwise;
* external group relations can remain exact;
* the only external-to-fiber error is the kernel-carry intertwining defect
  `(RBF20)`.

The scalar primitive-clock realization of `(RBF20)` is excluded by the
property-`(T)` moment lower bound.  A successful FALSE construction must
make `(RBF20)` small through base-dependent Fourier/Frobenius intertwiners
while keeping `(RBF14)` positive.

## 5. Tensor atlases do not dilute a local witness

The direct-sum and fusion constructions repeatedly encounter a density
loss when one good chart occupies only a small fraction of the total space.
Tensor products behave differently.

Let `rho_j:G->U(V_j)`, `1<=j<=N`, be maps and put

`rho(g)=tensor_(j=1)^N rho_j(g)`.                        `(RBF21)`

### Lemma 3 (tensor-atlas estimate)

For every `g,h in G`,

`||rho(gh)-rho(g)rho(h)||_2`
` <=sum_j ||rho_j(gh)-rho_j(g)rho_j(h)||_2.`            `(RBF22)`

If `T_j in U(V_j)` and `widehat T_j` acts as `T_j` on the `j`th factor and
as the identity elsewhere, then

`[T_j,rho_j(p)]=0`, `p in P`,                           `(RBF23)`

implies

`[widehat T_j,rho(p)]=0`, `p in P`,                     `(RBF24)`

and

`||Ad(widehat T_j)rho(m)-rho(m)||_2`
` =||Ad(T_j)rho_j(m)-rho_j(m)||_2.`                     `(RBF25)`

### Proof

Telescope the difference between the two tensor products in `(RBF22)`,
changing one factor at a time.  Tensoring an operator with unitaries leaves
its normalized Hilbert--Schmidt norm unchanged, so the triangle inequality
gives `(RBF22)`.  Equation `(RBF24)` follows because the other tensor
factors commute with `widehat T_j`.  The difference in `(RBF25)` is the
local difference tensored with unitaries, proving equality.  End proof.

Consequently one may allocate a separate factor to every finite chart or
basepoint without losing the local marked energy.  The price is the sum in
`(RBF22)`.  If the local construction can make each of `N_k` chart defects
`o(1/N_k)`, the tensor atlas has vanishing global defect and order-one
marked energy.

For the current project this is a genuine alternative to high-rank
nonorthogonal fusion, but it is conditional.  The unresolved local theorem
must supply arbitrarily accurate implementations of all kernel carries in
`(RBF20)` while preserving the Pauli wall.  Merely tensoring the existing
scalar clock cells cannot evade the property-`(T)` lower bound.

## 6. Corrected remaining gate

The principal-bundle part of the FALSE construction is now reduced to the
following exact finite-stage problem.

For each fixed word window, construct a finite-dimensional basepoint map
`pi` and transitions `v(s,x)` such that

1. the averaged multiplicativity defects in `(RBF9)` tend to zero;
2. every kernel-carry defect in `(RBF20)`, averaged over the regular base,
   tends to zero;
3. pointwise relative Pauli walls satisfy `(RBF12)` on the common positive
   window; and
4. the marked average `(RBF14)` stays bounded below.

There is no additional relative-cocycle consistency condition on the Pauli
wall table.  Conversely, replacing `(2)` by an honest quotient action makes
the natural positive image absorb the marked class.  The remaining theorem
is therefore exactly a **nonliftable kernel-carry intertwiner**, not another
external presentation or cocycle problem.
