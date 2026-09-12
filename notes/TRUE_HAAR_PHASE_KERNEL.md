# TRUE lane: the Haar law of a common-Cartan phase kernel

Started: 2026-08-10.  Updated: 2026-08-11.

This note continues `notes/TRUE_CARTAN_MONOMIAL_GATE.md`.  A common Cartan
does more than produce an abelian kernel: the phases of that kernel are
forced to be Haar-distributed characters, equivariantly for the sofic
quotient.  This identifies the exact finite-window object which still has to
be rounded.  It does **not** assert that the rounding is automatic.

## 1. Monomial ultraproduct setup

Let `Gamma` be countable and suppose that a faithful regular-trace embedding

`rho:Gamma -> product_omega Mon(d_n)`                    `(HPK1)`

has been obtained, for example from the common-Cartan hypotheses and the
Birkhoff estimate `(CTM1)--(CTM11)`.  Here

`Mon(d_n)=T^(d_n) semidirect Sym(d_n)`.

Let `A` be the tracial ultraproduct of the diagonal algebras and let

`theta:Gamma -> product_omega Sym(d_n)`                 `(HPK2)`

be the permutation-part homomorphism.  Put `K=ker(theta)` and
`Q=theta(Gamma)`.  As in Theorem 3 of the Cartan note, `Q` is sofic and `K`
is abelian.  We identify `A` with `L-infinity(X,mu)` for its Loeb probability
space.  The permutation ultraproduct acts on `X` by measure-preserving
transformations.

For `k in K`, the permutation part tends to the identity in Hamming metric.
Deleting it changes the corresponding monomial matrices by `o(1)` in
normalized Hilbert--Schmidt norm.  Consequently

`rho(k)=a_k in U(A)`,                                  `(HPK3)`

and `k |-> a_k` is a homomorphism from `K` to
`L-infinity(X,T)`.

## 2. The phase field is Haar on the dual

**Theorem 1 (Haar-dual phase law).**  In the setup above there is a measurable
map

`chi:X -> dual(K)`                                     `(HPK4)`

such that, after discarding one null set,

`a_k(x)=chi_x(k)` for every `k in K`.                  `(HPK5)`

Its pushforward measure is Haar probability on `dual(K)`.  Moreover `(HPK4)`
is equivariant for the conjugation action of `Q`: if `g in Gamma`,
`q=theta(g)`, and `k in K`, then

`chi_(q x)(g k g^(-1))=chi_x(k)`                       `(HPK6)`

for almost every `x`.  The action on the right is independent of the chosen
lift `g` of `q`.

**Proof.**  Since `K` is countable, the homomorphism identities

`a_(kl)=a_k a_l`, `a_1=1`                              `(HPK7)`

hold simultaneously off one null set.  Thus `(HPK5)` defines a character of
`K` at almost every point, giving `(HPK4)`.

Let `nu=chi_*mu`.  The embedding has the regular trace, so

`integral_(dual(K)) eta(k) dnu(eta)`
` =integral_X a_k dmu=tau(rho(k))=1_(k=1)`.            `(HPK8)`

The right side is the Fourier transform of Haar probability on `dual(K)`.
Finite linear combinations of the characters `eta |-> eta(k)` are uniformly
dense in `C(dual(K))`; hence probability measures are determined by these
coefficients.  Therefore `nu` is Haar.

Conjugation by `rho(g)` preserves `A`.  Its diagonal phase cancels in this
conjugation, so its action on `A` is exactly the Loeb action of the
permutation part `q`.  Hence

`rho(g) a_k rho(g)^(-1)=a_(gkg^(-1))`.                 `(HPK9)`

Writing `(HPK9)` pointwise gives `(HPK6)`.  If two lifts differ by an element
of `K`, their conjugation actions on `K` agree because `K` is abelian; this
also proves lift independence.  End proof.

Thus a common-Cartan counterexample cannot use an arbitrary collection of
canceling phases.  It must carry an equivariant copy of the full Haar dual
of its phase kernel.

### The extension class becomes a measurable coboundary

The phase field also remembers the extension, not only its kernel.  Choose a
normalized section `s:Q->Gamma` and define

`v(q,r)=s(q)s(r)s(qr)^(-1) in K`.                      `(HPK9a)`

Let `u_q` be the permutation ultraproduct represented by `theta(s(q))`.
There is a unique `b_q in U(A)` such that

`rho(s(q))=b_q u_q`, `b_1=1`.                         `(HPK9b)`

Write `beta_q=Ad(u_q)|A`.  Since the permutation parts multiply exactly in
the ultraproduct, multiplication of `(HPK9b)` gives

`b_q beta_q(b_r)=a_(v(q,r)) b_(qr)`.                  `(HPK9c)`

Pointwise, with the usual action convention, this is

`b_q(x)b_r(q^(-1)x)`
`  =chi_x(v(q,r))b_(qr)(x)`.                          `(HPK9d)`

Thus the `T`-valued 2-cocycle obtained by evaluating the extension cocycle
against the Haar character at `x` is a measurable coboundary on the Loeb
`Q`-space.  Changing the section changes both sides by the corresponding
1-coboundary, so the assertion is intrinsic.

This is stronger than Haar genericity.  A finite rounding must approximate
the character field, its quotient transport, and the primitive `b_q`
simultaneously.  Rounding the Haar labels while discarding `(HPK9c)` loses
the multiplication law of the total group.

### A Bockstein criterion for bounded-exponent kernels

Suppose now that `K` has exponent `m`.  Then `a_k^m=1` for every `k`, so
`(HPK9c)` implies that

`lambda_q=b_q^m`                                      `(HPK9e)`

is a measurable `T`-valued 1-cocycle:

`lambda_q beta_q(lambda_r)=lambda_(qr)`.              `(HPK9f)`

Indeed, raise `(HPK9c)` to the `m`th power inside the abelian algebra `A`.
The factor `a_(v(q,r))^m` disappears.

For the coefficient sequence

`1 -> mu_m -> T --(z |-> z^m)--> T -> 1`,

the class of `lambda` has a connecting class

`partial_m[lambda] in H^2(Q action X,mu_m)`.           `(HPK9f')`

Exactness says that this class vanishes precisely when `[lambda]` is
`m`-divisible in measurable `H^1`.  Because measurable circle-valued
0-cochains have measurable `m`th roots, vanishing is also equivalent to an
exact cocycle root as in `(HPK9g)` below.

There is also a direct representative formula.  The cochain `b` is already
an `m`th root of `lambda`, and `(HPK9c)` says that its coboundary is the
`mu_m`-valued evaluated extension cocycle.  Hence

`partial_m[lambda]=[a_(v(q,r))]`
`  in H^2(Q action X,mu_m)`.                           `(HPK9f'')`

Its image in circle-valued `H^2` is zero, with primitive `b`.  Consequently,
if the coefficient inclusion induces an injection

`H^2(Q action X,mu_m) -> H^2(Q action X,T)`,           `(HPK9f''')`

then `(HPK9f'')` vanishes and Theorem 2 applies.  This is an exact
cohomological sufficient condition, not a stability assumption: the missing
general statement is precisely that the particular class in `(HPK9f'')`
need not lie in the kernel of `(HPK9f''')` nontrivially.

**Theorem 2 (vanishing phase Bockstein implies soficity).**  In the common-Cartan
setup, assume `K` has finite exponent `m`.  If there is a measurable
1-cocycle `r_q in U(A)` satisfying

`r_q^m=lambda_q` for every `q in Q`,                  `(HPK9g)`

then `Gamma` is sofic.

**Proof.**  Put

`p_q=b_q r_q^(-1)`.                                   `(HPK9h)`

Equations `(HPK9e)--(HPK9g)` give `p_q^m=1`, and division of `(HPK9c)` by
the cocycle identity for `r` gives

`p_q beta_q(p_r)=a_(v(q,r))p_(qr)`.                   `(HPK9i)`

Using `(HPK6)` for covariance and `(HPK9i)` for multiplication, the formula

`rho'(k s(q))=a_k p_q u_q`                            `(HPK9j)`

is a homomorphism: the product of the formulas for `k s(q)` and `l s(r)` is
the formula for
`k (s(q)l s(q)^(-1)) v(q,r) s(qr)`.  Its diagonal phases all lie in
`mu_m`.  Represent these
finite-spectrum diagonal elements by `mu_m`-valued functions at the matrix
levels.  Equality in the tracial ultraproduct then means equality away from
`o(d_n)` coordinates, because distinct `m`th roots have a fixed positive
separation.  The skew action

`mu_m^(d_n) semidirect Sym(d_n) -> Sym([d_n] times mu_m)` `(HPK9k)`

therefore turns `(HPK9j)` into a permutation-ultraproduct homomorphism.

It is injective.  If `q!=1`, its base permutation `u_q` is nonidentity in
the metric ultraproduct by the definition of `Q`; the skew permutation moves
at least the same positive proportion.  If `q=1` and `k!=1`, Haar regularity
gives `integral_X a_k=0`.  If `r` is the measure of `{x:a_k(x)=1}`, then

`r <= |integral_X a_k|+(1-r)=1-r`,

so `r<=1/2`; the skew action of `a_k` moves at least half of its points.
Hence every nonidentity element has positive permutation length.  Fixed
finite-window diagonal product amplification converts this
positive-separation model to the usual asymptotically free normalization:
on a prescribed finite set, take the minimum of the finitely many positive
lengths and then choose one product power.  End proof.

Conversely, a `mu_m`-valued primitive `p_q` for `(HPK9c)` exists exactly when
`(HPK9g)` does: set `r_q=b_qp_q^(-1)`.  Therefore the obstruction is the
class of `lambda` modulo `m`th powers in measurable degree-one cocycles.  It
is the Bockstein residue of the evaluated extension class, not a choice of
section or of the primitive `b`.

This is the measurable-action, degree-one counterpart of the
`H^1(L,T)` ambiguity isolated in the earlier theorem “virtual divisibility
equals projective realizability” in `notes/NOTEPAD.md`.  There the same
coefficient sequence distinguishes a circle-valued trivialization from a
finite-phase trivialization of a degree-two multiplier; here `(HPK9f')`
distinguishes them for the section primitive of the common-Cartan phase
extension.

In particular the criterion holds whenever `lambda` is a measurable
coboundary.  If

`lambda_q=f beta_q(f)^(-1)`,                           `(HPK9l)`

choose a measurable `m`th root `h` of `f` and put
`r_q=h beta_q(h)^(-1)`.  Then `r` is a 1-cocycle and `r_q^m=lambda_q`.
More generally it is enough that the class of `lambda` in measurable
`H^1(Q action X,T)` be `m`-divisible.  Thus a cocycle-superrigidity theorem
which makes `lambda` cohomologous to a character of `Q` finishes this gate
whenever that character is `m`-divisible; for a perfect `Q` it is trivial.
No such superrigidity statement is known here for the arbitrary Loeb action
produced by a common-Cartan model.

The theorem is deliberately conditional.  Although `U(A)` is pointwise
divisible, roots chosen independently for the functions `lambda_q` need not
satisfy the 1-cocycle law.  Claiming otherwise would incorrectly solve the
finite-kernel extension problem.  The cocycle-stability argument
`(CS1)--(CS8)` is one finite-level mechanism which can force the needed
divisibility after approximation.

The obstruction is already nonzero on one point.  Let `Q=C_m` act trivially
and let `lambda:Q->T` send a generator to a primitive `m`th root.  Every
1-cocycle is then a character, and the `m`th power of every character of
`C_m` is trivial.  Hence `lambda` has pointwise roots as a function but no
root in `Z^1(Q,T)`.  This is the carry class of
`1->C_m->C_(m^2)->C_m->1` after evaluating the kernel by a faithful
character.

More importantly, the obstruction can survive all the regular-trace and
Haar hypotheses of Theorem 1.

**Proposition (regular trace does not kill the phase Bockstein).**  Let
`Gamma=C_4=<g>` and represent its generator on four coordinates by

`rho(g)=[[0,1],[1,0]] directSum [i] directSum [-i]`.    `(HPK9m)`

With the diagonal Cartan, the permutation-part exact sequence is

`1 -> K=<g^2>=C_2 -> C_4 -> Q=C_2 -> 1`,              `(HPK9n)`

the kernel phase field is Haar, and the class `(HPK9f'')` is nonzero.

**Proof.**  The eigenvalues in `(HPK9m)` are `1,-1,i,-i`, each once.  Thus
`rho` is the regular representation: its normalized trace is one at the
identity and zero at `g,g^2,g^3`.  Its permutation part swaps the first two
coordinates and fixes the last two, so its kernel is exactly `<g^2>`.  The
nontrivial kernel element is

`a_(g^2)=diag(1,1,-1,-1)`,                            `(HPK9o)`

which has the Haar distribution on `dual(C_2)`.

For the section sending the nontrivial element of `Q` to `g`, let `u` be
the displayed transposition.  Then

`b=rho(g)u^(-1)=diag(1,1,i,-i)`,
`lambda=b^2=diag(1,1,-1,-1)=a_(g^2)`.                `(HPK9p)`

The `Q`-action fixes the last two atoms.  At either such atom, any
circle-valued `C_2` 1-cocycle `r` satisfies `r(q,x)^2=1`, whereas an exact
square root of `lambda` would satisfy `r(q,x)^2=-1`.  No cocycle root exists,
so `(HPK9f'')` is nonzero.  End proof.

Of course `C_4` is sofic, for example through its regular permutation
action.  The proposition therefore shows that the Bockstein is intrinsic to
the chosen common-Cartan monomial model, but not to the abstract group.
Regular trace, finite dimensionality, exact multiplicativity, and the Haar
kernel law do not force `(HPK9f''')`; a general TRUE proof would have to
replace the model or round through the nonzero class.

### Slow tensor amplification removes quotient isotropy

There is a canonical model change which kills the point-stabilizer mechanism
in the proposition while preserving the phase kernel.

**Lemma (essentially-free quotient amplification).**  From `(HPK1)` one can
construct another faithful regular-trace monomial ultraproduct embedding

`rho_tilde:Gamma -> product_omega Mon(D_n)`            `(HPK9q)`

whose permutation-part kernel is the same subgroup `K`, but for which every
nonidentity element of `Q=Gamma/K` moves almost every point.  Equivalently,
the induced pmp `Q`-action on the new Loeb diagonal is essentially free.

**Proof.**  Enumerate `Gamma` and choose matrix representatives so that all
relations, traces, and permutation-kernel identities on the first `n`
elements have defects tending to zero.  Choose integers `L_n->infinity` so
slowly that multiplying any of these first-`n` defects by `L_n` still gives
zero in the limit.  Set

`rho_tilde_n(g)=rho_n(g)^(tensor L_n)`.                `(HPK9r)`

Tensor products of monomial matrices are monomial for the product basis.
For unitary matrices, telescoping gives

`||A^(tensor L)-B^(tensor L)||_2 <= L ||A-B||_2`,     `(HPK9s)`

so `(HPK9r)` remains asymptotically multiplicative.  Its trace is
`tr(rho_n(g))^(L_n)`, hence still tends to `1_(g=1)`.

If `ell_n(g)` is the Hamming length of the permutation part, the product
permutation has length

`1-(1-ell_n(g))^(L_n)`.                               `(HPK9t)`

For `k in K`, slow growth ensures this is at most `L_n ell_n(k)->0`.  For
`g notin K`, `ell_n(g)` has a positive ultralimit, so `(HPK9t)` tends to one.
The same diagonal choice preserves equality of permutation parts for two
lifts of one quotient element.  Thus the new kernel is exactly `K` and the
quotient action is essentially free.  End proof.

When `K` has exponent `m`, Theorem 1 and `(HPK9a)--(HPK9f'')` apply anew to
`rho_tilde`.  Since the action is now free, its action groupoid is the
principal orbit equivalence relation `R_Q`.  Therefore the remaining class
has the sharper location

`partial_m[lambda_tilde] in H^2(R_Q,mu_m)`,           `(HPK9u)`

and maps to zero in `H^2(R_Q,T)`.

**Corollary (treeable quotient relation).**  If the relation `R_Q` obtained
after slow tensor amplification is treeable, then `Gamma` is sofic.

**Proof.**  A measurable treeing is a one-dimensional free groupoid
presentation.  Consequently its second cohomology with any discrete abelian
coefficient group vanishes.  Concretely, assign value one to the oriented
tree edges and integrate a normalized 2-cocycle recursively along the unique
reduced path between two points; the cocycle identity shows that the resulting
measurable 1-cochain has the prescribed coboundary.  Hence
`H^2(R_Q,mu_m)=0`, so `(HPK9u)` vanishes and Theorem 2 applies.  End proof.

For `(HPK9m)`, product amplification makes the fixed density of the
nontrivial quotient element equal to `(1/2)^(L_n)`, and the displayed
Bockstein disappears.  In general, however, essential freeness does not
make an arbitrary measured equivalence relation treeable or force its second
finite-coefficient cohomology to vanish.  The reduced open obstruction is
therefore a finite central twist of a **principal** sofic equivalence relation,
not merely isotropy at fixed atoms.

This last caution is genuine, not just a gap in the argument.

**Proposition (principal sofic relations can retain the residue).**  Fix
`m>=2`, let

`H=SL_3(Z)`, `Q=H times C_m`,                         `(HPK9v)`

and let `Q` act by its Bernoulli shift on a nonatomic base.  This action is
free, its orbit relation is sofic, and the projection character

`chi:Q -> C_m=mu_m`                                  `(HPK9w)`

is not `m`-divisible in measurable `H^1` of the action.  Moreover this
nondivisible class occurs as `(HPK9e)` in a regular-trace common-Cartan
monomial model of the sofic group

`Gamma=H times C_(m^2)`.                              `(HPK9x)`

**Proof.**  Popa's cocycle-superrigidity theorem applies to the Bernoulli
action in `(HPK9v)`: every circle-valued measurable 1-cocycle is cohomologous
to a homomorphism `Q->T`.  Suppose a cocycle `r` had `[r]^m=[chi]`.  Write
`r` as a homomorphism `psi` up to coboundary.  Then `chi` and `psi^m` are
cohomologous homomorphism cocycles.  Their quotient would be an eigencharacter
of the Bernoulli action; mixing makes it trivial.  Hence `chi=psi^m`.  But if
`c` generates the `C_m` factor, then `psi(c)^m=psi(c^m)=1`, whereas
`chi(c)` is primitive.  This is impossible.

To realize the class, write the central extension

`1 -> K=C_m -> H times C_(m^2) -> H times C_m -> 1`   `(HPK9y)`

using the usual carry cocycle `v:Q times Q->C_m`.  Choose a set-theoretic
lift `d:Q->mu_(m^2)` of `(HPK9w)`, so

`d_q^m=chi(q)`, `delta d(q,r)=zeta_m^(v(q,r))`.       `(HPK9z)`

On `dual(K) times X`, where `X` is the Bernoulli space and `Q` acts trivially
on `dual(K)`, write a character as `eta_t(k)=zeta_m^(tk)` and put

`a_k(eta_t,x)=eta_t(k)`, `b_q(eta_t,x)=d_q^t`.        `(HPK9aa)`

Then `delta b_q=eta_t(v(q,r))`, so `(HPK9j)` defines a monomial
representation of `Gamma`.  The Bernoulli action kills the trace when
`q!=1`, while Haar averaging over `dual(K)` kills it when `q=1,k!=1`.
Thus the trace is regular and the phase field of `K` is Haar.  Standard
finite Bernoulli models for the residually finite group `Q`, together with
the fixed phase alphabet `mu_(m^2)`, realize this representation in a matrix
ultraproduct.  Finally `(HPK9e)` restricts on the invariant component `t=1`
to `chi`, which was just shown nondivisible.  End proof.

The group `(HPK9x)` is nevertheless residually finite and hence sofic; its
`mu_(m^2)` phases can be untwisted by Theorem 3.  The lesson is precise:
neither regular trace, Haar kernel law, essential freeness, principality, nor
soficity of the quotient relation forces the **minimal `mu_m`** Bockstein to
vanish.  A general proof must allow a larger finite phase alphabet or solve
the finite-phase completion gate `(HPK18)` directly.

### Torsion-valued primitives already suffice

Let

`mu_infty=union_(M>=1) mu_M`                           `(HPK9ab)`

be the countable group of all roots of unity, equipped with its discrete
Borel structure.  Allowing its elements to have unbounded order gives a
strictly stronger criterion than killing the Bockstein in one fixed
`mu_M`, but it still gives finite models.

**Theorem 3 (torsion phase primitive implies soficity).**  Assume more
generally that the abelian phase kernel `K` is torsion, and first make the
quotient action essentially free by `(HPK9q)--(HPK9u)`.  Write

`omega(q,r,x)=a_(v(q,r))(x) in mu_infty`.             `(HPK9ac)`

If there are measurable functions `p_q:X->mu_infty`, with `p_1=1`, such
that

`p_q beta_q(p_r)=omega(q,r) p_(qr)`                  `(HPK9ad)`

almost everywhere for every `q,r in Q`, then `Gamma` is sofic.  Equivalently,
it is enough that

`[omega]=0 in H^2(R_Q,mu_infty)`.                    `(HPK9ae)`

**Proof.**  Formula

`rho_p(k s(q))=a_k p_q u_q`                          `(HPK9af)`

is a homomorphism by `(HPK6)` and `(HPK9ad)`.  All its diagonal factors are
torsion-valued, although there need not be one exponent which works
globally.

Enumerate `Gamma` and let the `n`th test contain the first `n` elements and
all section terms needed to multiply them.  Fix `epsilon_n->0`.  Since
`mu_infty=union_M mu_(M!)`, continuity from below gives an integer `M_n`
such that, for every one of the finitely many functions `p_q` in this test,

`mu{x:p_q(x) notin mu_(M_n)}<epsilon_n`.              `(HPK9ag)`

Enlarge `M_n`, if necessary, so that it is divisible by the orders of the
finitely many kernel elements and extension values occurring in the test.
Replace `p_q` by `1` on its exceptional set.  The resulting functions, all
tested `a_k`, and all tested values of `omega` are `mu_(M_n)`-valued.
Equation `(HPK9ad)` can now fail only where one of its three variable terms
was replaced (with one exceptional set transported by a measure-preserving
quotient map), so its failure set has measure at most `3 epsilon_n`.
Covariance `(HPK6)` is unchanged.

Every finite-valued Loeb-diagonal function has finite-level representatives
with the same finite range: lift its level-set partition to the diagonal
matrix coordinates.  Simultaneously lifting the finitely many functions in
the `n`th test and the quotient permutations therefore gives
`mu_(M_n)`-valued monomial tables satisfying `(HPK13)--(HPK14)`, with error
tending to zero.

Their traces have the required limit.  If `q!=1`, essential freeness of the
amplified quotient action makes the trace of any diagonal multiple of `u_q`
zero.  If `q=1` and `k!=1`, the trace of `a_k` is zero by the Haar law;
moreover `a_k=1` on exactly `1/ord(k)<=1/2` of the Haar character field.
Thus `(HPK15)` holds, and finite-phase skew untwisting, Theorem 4 below,
proves that `Gamma` is sofic.  End proof.

For a bounded-exponent kernel, the theorem moves the exact cohomological
obstruction from

`ker(H^2(R_Q,mu_m) -> H^2(R_Q,T))`

to the potentially smaller group

`ker(H^2(R_Q,mu_infty) -> H^2(R_Q,T)).`               `(HPK9ah)`

Both calibrations above disappear at this sharper level: the `C_4` class
has a `mu_4` primitive, and the `H times C_(m^2)` carry class has a
`mu_(m^2)` primitive.  Thus they disprove minimal-alphabet vanishing but do
not disprove `(HPK9ae)`.

There is an exact groupoid interpretation.  On a fixed finite window choose
`M` divisible by the orders of its cocycle values and push the corresponding
part of the central twist `(HPK9ac)` out to `mu_M`:

`G_(omega,M)=mu_M times_omega R_Q`,                   `(HPK9ai)`

with multiplication

`(zeta,gamma)(eta,delta)=(zeta eta omega(gamma,delta),gamma delta)`.

A groupoid splitting over `R_Q` has the form
`gamma |-> (p(gamma)^(-1),gamma)` and exists exactly when a
`mu_M`-valued `p` satisfies `(HPK9ad)` (up to the displayed inverse
convention).  The same statement with `mu_infty` says that `(HPK9ae)` is
precisely the splitting of the torsion pushout of the twist.  The original
circle primitive `b` proves only that its pushout to `T` splits.

This distinction prevents a tempting circular use of permanence for sofic
equivalence relations.  Cordeiro's finite-index theorem starts with a
**sofic subrelation already embedded in** a finite-index superrelation (and
appropriate invertible choice functions).  Here one initially has a finite
central groupoid **over** `R_Q`; producing a copy of `R_Q` inside it is the
splitting `(HPK9ad)` itself.  Finite-index permanence therefore propagates a
splitting after it is found, but does not manufacture one.

Finally, the algebraic fact that `mu_infty` is an injective abelian group
does not make the coefficient map in `(HPK9ah)` formally injective in
measurable cohomology.  Algebraic retractions `T->mu_infty` are necessarily
nonmeasurable: a Borel homomorphism from the connected Polish group `T` to
the countable discrete group `mu_infty` is continuous and hence trivial.
Applying an abstract retraction pointwise to the measurable primitive `b`
is therefore invalid.  The remaining torsion-kernel TRUE target is the
measurable torsion-splitting statement `(HPK9ae)`, or its finite-window
version, not minimal Bockstein vanishing.

### The coefficient kernel and a countable-range criterion

The obstruction in `(HPK9ah)` has a useful exact description.  For a
principal countable pmp relation `R`, let `C^j(R,A)` and `Z^j(R,A)` denote
measurable cochains and cocycles, modulo equality almost everywhere, and put

`D_R={b in C^1(R,T): delta b in C^2(R,mu_infty)}`.     `(HPK9aj)`

The map

`b |-> [delta b]`                                      `(HPK9ak)`

induces an isomorphism of abelian groups

`D_R/(Z^1(R,T) C^1(R,mu_infty))`
`  ~= ker(H^2(R,mu_infty) -> H^2(R,T)).`               `(HPK9al)`

Indeed `(HPK9ak)` lands in the displayed kernel.  Every class in the kernel
has a circle-valued primitive and hence is represented by `(HPK9ak)`.  Finally
`[delta b]=0` over `mu_infty` exactly when there is
`p in C^1(R,mu_infty)` with `delta p=delta b`; equivalently
`b p^(-1) in Z^1(R,T)`.  This proves `(HPK9al)`.

Thus the problem is a rationalization problem for a circle-valued primitive,
modulo circle-valued 1-cocycles.  It has the following positive solution as
soon as that primitive is not genuinely diffuse.

**Theorem 3A (countable-range primitive implies soficity).**  In the setup of
Theorem 3, suppose `delta b=omega` and there is a circle-valued measurable
1-cocycle `c` such that

`d=b c^(-1)`                                           `(HPK9am)`

has countable essential range as a scalar function on `R_Q`.  Then
`[omega]=0` in `H^2(R_Q,mu_infty)`, and therefore `Gamma` is sofic.

**Proof.**  After changing `d` on a null set, let `A<T` be the countable
subgroup generated by its range.  Since `delta d=omega`, every value of
`omega` belongs to

`B=A intersect mu_infty`.                              `(HPK9an)`

The group `mu_infty` is divisible, hence injective in the category of
abelian groups.  Therefore the identity homomorphism `B->mu_infty` extends
to a homomorphism

`r:A->mu_infty`.                                      `(HPK9ao)`

There is no measurability problem here: `A` is countable and has the discrete
Borel structure.  Apply `r` pointwise to `(HPK9am)` and put `p=r after d`.
Pointwise application commutes with pullback by the relation, while `r`
fixes `(HPK9an)`.  Consequently

`delta p=r(delta d)=r(omega)=omega`.                  `(HPK9ap)`

So `p` is the torsion-valued primitive required by Theorem 3.  End proof.

It is enough, equivalently, that every `d_q` have countable essential range:
there are only countably many `q`, so their ranges generate one countable
subgroup `A`.  The cocycle adjustment in `(HPK9am)` is essential because the
class in `(HPK9al)`, rather than the initially chosen section primitive, is
the invariant object.

This theorem also isolates why the naive injectivity argument fails.  The
countable subgroup generated by the **functions** `b_q` inside
`L^0(X,T)` does admit an abstract retraction to the divisible group
`L^0(X,mu_infty)`.  Such a retraction need not commute with the quotient
action `beta`, so it need not preserve the differential.  The scalar
retraction `(HPK9ao)` does commute with every pullback, but it is available
only after the scalar range has become countable.

The measurability issue is real even for a free hyperfinite relation, already
in degree one.  In additive notation let `mu_infty=Q/Z` act on
`T=R/Z` by translations and let `R_0` be its orbit relation.  The cocycle

`u(a,x)=a`                                             `(HPK9aq)`

is `mu_infty`-valued and is a `T`-coboundary, with primitive `f(x)=x`.
It is not a `mu_infty`-coboundary.  Otherwise a measurable
`p:T->mu_infty` would satisfy

`p(x+a)-p(x)=a`.                                      `(HPK9ar)`

Then `h(x)=p(x)-x` would be invariant under the dense translation subgroup
`Q/Z`.  That action is ergodic, so `h` would be constant almost everywhere.
Thus `p(x)=x+h` almost everywhere, which is torsion-valued only on a
countable Haar-null set, a contradiction.  Hence

`ker(H^1(R_0,mu_infty)->H^1(R_0,T)) != 0`.             `(HPK9as)`

This does not produce the degree-two obstruction in `(HPK9ah)`:
`R_0` is hyperfinite and treeable, so its discrete-coefficient second
cohomology vanishes.  It does prove that an arbitrary measurable circle
primitive cannot simply be “rationalized.”  Moreover `(HPK9aq)` comes from
dense **translations** of the circle.  The phase cocycle `(HPK9ac)` comes
from the automorphic action of `Q` on the profinite group `dual(K)` and has
the special evaluation form `chi_x(v(q,r))`.  Any further positive theorem
must exploit that automorphic Haar geometry, or another property forced by
the monomial model; it cannot be a coefficient-only measurable retraction.

### The unsplit twist itself is an alternate endpoint

Splitting is sufficient but not logically necessary.  Retain the essentially
free quotient action and form the countable pmp groupoid

`Sigma_omega=mu_infty times_omega R_Q`.                `(HPK9at)`

Use the target-coordinate convention: an arrow `(q,x)` has source
`q^(-1)x` and range `x`, and

`(zeta,q,x)(eta,r,q^(-1)x)`
`  =(zeta eta omega(q,r,x),qr,x)`.                     `(HPK9au)`

**Theorem 3B (sofic torsion twist implies soficity).**  If the pmp groupoid
`Sigma_omega` is sofic, then `Gamma` is sofic.

**Proof.**  For `g=k s(q)` define the full bisection

`B_g={ (a_k(x),q,x):x in X }`.                        `(HPK9av)`

This is well-defined because `K` is torsion, so `a_k` takes values in the
finite group `mu_(ord(k))`.  Equivariance `(HPK6)`, the extension law
`s(q)s(r)=v(q,r)s(qr)`, and `(HPK9ac)` give

`B_g B_h=B_(gh)`.                                     `(HPK9aw)`

Thus `g |-> B_g` is a homomorphism `Gamma->[Sigma_omega]`.

It is metrically injective.  If `q!=1`, essential freeness says that
`B_(k s(q))` differs from the unit at almost every point.  If `q=1` and
`1!=k in K`, Haar measure on `dual(K)` gives

`mu{x:a_k(x)=1}=1/ord(k) <= 1/2`.                     `(HPK9ax)`

Hence every nonidentity `g` has positive full-group distance from the unit.

A sofic embedding of the full semigroup of `Sigma_omega` restricts to a
metric permutation-ultraproduct embedding of its full group, and then to
`Gamma`.  Positive, rather than unit, separation is enough: enumerate
`Gamma` and take sufficiently slow diagonal product powers of the finite
permutation representatives.  A permutation of Hamming length `ell` has
product length `1-(1-ell)^L`; choose `L` tending to infinity slowly enough
to preserve every tested multiplication defect.  All nonidentity lengths
then tend to one.  This is a sofic approximation of `Gamma`.  End proof.

Theorem 3 is the split special case of this endpoint.  If `(HPK9ae)` holds,
the primitive identifies `(HPK9at)` with the product groupoid
`mu_infty times R_Q`.  This product is sofic: it is the increasing union of
`mu_(M!) times R_Q`, and each finite product contains `R_Q` as a finite-index
sofic subgroupoid.  Cordeiro's finite-index and increasing-union permanence
theorems apply after the splitting has been supplied.

Theorem 3B gives a potentially weaker target than a torsion primitive:

`Sigma_omega is a sofic pmp groupoid`.                 `(HPK9ay)`

It is not automatic from soficity of `R_Q`.  A theorem asserting that every
finite central twist over a sofic principal relation is sofic would, by the
same bisection construction applied to a free sofic action of the quotient,
settle the open permanence of sofic groups under finite central kernels.  At
the finite-model level the obstruction is visible as follows.  A finite pair
groupoid has trivial second cohomology, so completing the prescribed local
twist labels requires a finite primitive; allowing finite isotropy merely
moves the same holonomy into a finite extension group.  Thus `(HPK9ay)` is
an alternate exact gate, not a consequence of the existing finite-index
theorem.

The groupoid endpoint does, however, make finite-index restriction useful in
the correct direction.

**Theorem 3C (virtual torsion splitting implies soficity).**  Suppose there is
a finite-index pmp subrelation `S<R_Q` such that

`[omega|S]=0 in H^2(S,mu_infty)`.                     `(HPK9az)`

Then `Gamma` is sofic.

**Proof.**  Let `H` be the full inverse image of `S` in `Sigma_omega`.  Its
index in `Sigma_omega` equals `[R_Q:S]`: lift a finite family of full-group
transversals for `S<R_Q` through the quotient map
`Sigma_omega -> R_Q`; because `H` contains the entire isotropy group
`mu_infty` over every unit, the lifted left cosets are still disjoint and
exhaust `Sigma_omega`.  A primitive in `(HPK9az)` gives

`H ~= mu_infty times S`.                              `(HPK9ba)`

The subrelation `S` is sofic, since subgroupoids of a sofic equivalence
relation are sofic.  The countable locally finite group `mu_infty` is sofic,
so Cordeiro's product theorem makes `(HPK9ba)` sofic.  Cordeiro's finite-index
theorem now gives soficity of `Sigma_omega`, and Theorem 3B gives soficity of
`Gamma`.  End proof.

In particular, it is enough that `R_Q` have a finite-index treeable
subrelation: discrete-coefficient second cohomology vanishes on a treeing, so
`(HPK9az)` holds.  More generally the exact remaining virtual target is

`omega becomes torsion-trivial on a finite-index subrelation.` `(HPK9bb)`

This is strictly the right use of finite-index permanence.  Taking the full
preimage retains all isotropy and therefore keeps the groupoid index finite;
trying to insert the base relation itself would still require a global
splitting.

The virtual criterion removes the apparent obstruction from every cocycle
class with a finitely generated scalar-range representative, and therefore
from every character-rigid quotient action, in bounded exponent.

**Lemma (finitely generated cocycle range is virtually divisible).**  Let
`R` be a countable pmp relation, let `eta in Z^1(R,T)`, and suppose the
essential range of `eta` is contained in a finitely generated subgroup
`A<T`.  For every `m>=1` there are a finite-index pmp subrelation `S<R` and
`r in Z^1(S,T)` such that

`r^m=eta|S`.                                          `(HPK9bc)`

**Proof.**  Choose an abstract decomposition

`A ~= Z^d directSum T_0`                              `(HPK9bd)`

with `T_0` finite, and let `B<A` correspond to
`m Z^d directSum 0`.  Then `[A:B]<infinity`.  The set

`S={gamma in R:eta(gamma) in B}`                     `(HPK9be)`

is a pmp subrelation.  On each `R`-class, two points belong to the same
`S`-class exactly when their `eta`-coordinates lie in the same coset of
`B`, so `[R:S]<=[A:B]`.

There is a homomorphism `rho:B->T` with `rho(b)^m=b`: under `(HPK9bd)`, set
`rho(mz,0)` equal to the image in `T` of `(z,0)`.  Therefore
`r=rho after eta|S` is a circle cocycle and satisfies `(HPK9bc)`.  End
proof.

**Theorem 3D (virtual finitely generated-range criterion).**  Suppose the
phase kernel `K` has exponent `m` and use the essentially-free quotient
model `(HPK9q)--(HPK9u)`.  If the cocycle `lambda` in `(HPK9e)` is
cohomologous to a circle cocycle whose essential range lies in a finitely
generated subgroup of `T`, then `Gamma` is sofic.

**Proof.**  Write

`lambda_q=f beta_q(f)^(-1) eta_q`                    `(HPK9bf)`

and apply the preceding lemma to `eta`, obtaining `S` and `rho after eta`.
Choose a measurable `m`th root `h` of `f`.  On `S`, the cocycle

`r=(h beta(h)^(-1))(rho after eta)`                  `(HPK9bg)`

satisfies `r^m=lambda|S`.  Hence the restricted Bockstein
`[omega|S]` vanishes in `H^2(S,mu_m)`, and Theorem 3C applies.  End proof.

**Lemma (characters are virtually divisible).**  Let `Q` be finitely
generated, let `m>=1`, and let `chi:Q->T` be a character.  There are a
finite-index normal subgroup `L normal Q` and a character `psi:L->T` such that

`psi(l)^m=chi(l)` for every `l in L`.                  `(HPK9bh)`

**Proof.**  Write the finitely generated abelianization as

`Q_ab ~= Z^r directSum T_0`,                          `(HPK9bi)`

with `T_0` finite, and let `L` be the inverse image of
`m Z^r directSum 0`.  This subgroup has finite index.  If the image of
`l in L` is `(m z,0)`, set `psi(l)=chi_bar(z,0)`, where `chi_bar` is the
character induced on `Q_ab`.  The vector `z` is unique, so `psi` is a
well-defined character, and `(HPK9bh)` is immediate.  End proof.

**Corollary 3E (virtual character-rigidity criterion).**  In the setup of
Theorem 2, suppose that `K` has exponent `m`, that `Q` is finitely generated,
and that the cocycle `lambda` in `(HPK9e)` is cohomologous to a character of
`Q`.  Then `Gamma` is sofic.  In particular, this holds if every measurable
circle cocycle for the quotient action is cohomologous to a character.

**Proof.**  Write, using the convention of `(HPK9l)`,

`lambda_q=f beta_q(f)^(-1) chi(q)`.                   `(HPK9bj)`

Choose `L` and `psi` from `(HPK9bh)` and a measurable `m`th root `h` of `f`.
The restricted cocycle

`r_l=h beta_l(h)^(-1) psi(l)`                         `(HPK9bk)`

satisfies `r_l^m=lambda_l`.  Let `Gamma_L` be the inverse image of `L` in
`Gamma`.  Restricting the common-Cartan model to `Gamma_L` preserves the
regular trace, has the same phase kernel `K`, and has quotient `L`; hence
Theorem 2 makes `Gamma_L` sofic.  Since `Gamma_L` has finite index in
`Gamma`, ordinary finite-quotient extension permanence makes `Gamma` sofic.
Equivalently, after essentially-free amplification, the Bockstein vanishes
on the finite-index `L`-orbit subrelation and Theorem 3C applies.  End proof.

For the Popa carry calibration `(HPK9v)--(HPK9aa)`, take
`L=SL_3(Z) times {1}`.  Thus the nonzero minimal-alphabet Bockstein is not
even a virtual obstruction: it disappears on this index-`m` subrelation.
The genuinely remaining bounded-exponent case requires circle cocycles
which stay outside the character locus on every finite-index restriction.

Property `(T)` forces finitely generated range as soon as the cocycle is
countable-valued.

**Lemma (property `(T)` compresses countable cocycle range).**  Let `Q` have
property `(T)` and act ergodically and pmp on `(X,mu)`.  If

`eta in Z^1(Q action X,A)`                            `(HPK9bl)`

for a countable abelian group `A`, then `eta` is cohomologous to a cocycle
with values in a finitely generated subgroup `A_0<A`.

**Proof.**  Choose a finite Kazhdan set `F` and a tolerance `delta>0` so
that an `(F,delta)`-almost invariant unit vector in any unitary
representation has an invariant unit vector within `1/4`.  Because `F` is
finite and `A` is countable, there is a finitely generated subgroup `A_0<A`
such that

`mu{x:eta(s,x) notin A_0}`                            `(HPK9bm)`

is small enough for every `s in F`.  Put `B=A/A_0`.  The quotient cocycle
acts on

`H=L^2(X,ell^2(B))`                                   `(HPK9bn)`

by the usual skew-product representation.  For the constant section
`xi_0(x)=delta_0`,

`||pi(s)xi_0-xi_0||^2`
`  =2 mu{x:eta(s,x) notin A_0}`.                      `(HPK9bo)`

Thus there is an invariant unit vector `xi` with
`||xi-xi_0||<1/4`.  Its pointwise fiber norm is `Q`-invariant, hence is one
almost everywhere by ergodicity.  Let `E` be the set of `x` for which
`xi(x)` has a unique coordinate of modulus greater than `1/sqrt(2)`.  The
skew action only translates the `B`-coordinates, so `E` is invariant.
Moreover `E` has positive measure: otherwise
`Re <xi(x),delta_0><=1/sqrt(2)` almost everywhere, contradicting
`||xi-xi_0||<1/4`.  Ergodicity makes `E` conull.

Let `c(x) in B` be that unique coordinate.  Invariance of `xi` gives

`c(qx)=eta_bar(q,x)+c(x)`.                            `(HPK9bp)`

Choose a set-theoretic section `t:B->A`.  Gauging `eta` by `t after c`
produces a cohomologous cocycle whose image in `B` is zero by `(HPK9bp)`,
so it takes values in `A_0`.  End proof.

**Corollary 3F (countable property-`(T)` phase criterion).**  Suppose `K`
has exponent `m`, the essentially-free quotient action is ergodic, `Q` has
property `(T)`, and the class of `lambda` in `(HPK9e)` has a representative
with countable scalar range.  Then `Gamma` is sofic.

**Proof.**  Apply the lemma to the countable subgroup of `T` generated by
the representative's range, then apply Theorem 3D.  End proof.

Corollary 3I below gives a direct relation-theoretic proof without the
property-`(T)` hypothesis.  The same conclusion was already implicit in
Theorem 3A: if `lambda=b^m` has countable range, then `b` has countable
range because every scalar has only `m` roots.  The compression lemma remains
a useful rigidity statement, but it is not needed for this application.

The scalar-retraction proof of Theorem 3D cannot replace finite generation
by countability.  For a prime `p`, let `A=mu_(p^infinity)<T` be the Pruefer
`p`-group.  It has no proper finite-index subgroup because it is divisible.
There is no homomorphism `rho:A->T` satisfying

`rho(a)^p=a`.                                         `(HPK9bq)`

Indeed `rho` would be injective and would take `p`-primary torsion back into
`A`, splitting multiplication by `p` on `A`.  This would decompose
`A=A[p] directSum rho(A)`, giving at least two independent subgroups of
order `p`, whereas `A[p]` is cyclic.  Thus Theorem 3D is sharp for the
purely scalar-retraction method used in Theorem 3D.  The Pruefer calculation
does not itself produce a nonzero relation Bockstein.  Theorem 3A already
shows that countable infinite-height range of the primitive is not an
obstruction, and Corollary 3I supplies an independent subgroup-relation proof
when `lambda` has countable range.

There is also a canonical closed-range reduction which applies without
property `(T)`.  Recall that if `R` is an ergodic pmp relation and
`eta in Z^1(R,T)`, Mackey's compact-cocycle theorem gives a closed subgroup
`H_eta<T` and a cohomologous cocycle with values in `H_eta`.  One way to see
the reduction is to form the skew-product relation on `X times T`.  The
commuting right-translation action of `T` on its ergodic-component space is
ergodic; every ergodic probability action of a compact group is a homogeneous
space `T/H_eta`.  A measurable section of this homogeneous-space factor is
the required transfer function.  The subgroup is unique here because `T`
is abelian.

**Corollary 3G (Mackey-full-range obstruction).**  Suppose the phase kernel
has exponent `m` and the essentially-free quotient relation `R_Q` is
ergodic.  Let `H_lambda<T` be the Mackey group of the cocycle `(HPK9e)`.  If

`H_lambda != T`,                                      `(HPK9br)`

then `Gamma` is sofic.  More generally, the same conclusion holds if some
finite-index ergodic subrelation `S<R_Q` has

`H_(lambda|S) != T`.                                  `(HPK9bs)`

**Proof.**  Every proper closed subgroup of the circle is finite cyclic.
Mackey reduction therefore makes `lambda` (or `lambda|S`) cohomologous to a
cocycle with finite, hence finitely generated, scalar range.  Apply Theorem
3D.  In the second case its further finite-index subrelation still has
finite index in `R_Q`, so Theorem 3C applies.  End proof.

Thus a surviving bounded-exponent residue must have full circle Mackey range
on every finite-index ergodic restriction.  This condition is stronger than
having uncountable essential range in a particular gauge and is invariant
under measurable cohomology.  It is still only necessary: a cocycle with
finitely generated dense range can have Mackey group `T`, while Theorem 3D
already removes it.  In particular, the remaining class must be both
Mackey-full and non-reducible to finitely generated range after every
finite-index restriction.

At the level of the displayed primitive there is an even simpler check.  If
`lambda_q=b_q^m` is torsion-valued almost everywhere for every `q`, then
each `b_q` is torsion-valued because an `m`th root of a root of unity is a
root of unity.  Hence `b` itself is the `mu_infty`-valued primitive required
by Theorem 3, and `Gamma` is sofic.  Therefore an infinite-height torsion
group such as the Pruefer group can matter only after a genuinely
non-torsion transfer; it cannot obstruct in the original equality
`lambda=b^m`.

The full-Mackey-range case has a principal reformulation which does not ask
for a cocycle root.  For a circle cocycle `lambda in Z^1(R,T)`, write
`R(lambda)` for the skew-product relation on `X times T`:

`(x,u) R(lambda) (y,t)` iff `(x,y) in R`
`  and u=lambda(x,y)t`.                               `(HPK9bt)`

**Theorem 3H (sofic skew product closes the bounded-exponent gate).**
Suppose the phase kernel has exponent `m`, the quotient relation `R_Q` has
been made principal as above, and the pmp relation `R_Q(lambda)` is sofic.
Then `Gamma` is sofic.

**Proof.**  Put `R=R_Q` and regard `b` as a circle-valued 1-cochain on `R`,
so that

`b(gamma)^m=lambda(gamma)`, `delta b=omega in mu_m`.  `(HPK9bu)`

The fixed-alphabet twist `Sigma_m=mu_m times_omega R` is isomorphic to the
root groupoid

`G_lambda={(gamma,z):z^m=lambda(gamma)}`              `(HPK9bv)`

by

`(zeta,gamma) |-> (gamma,zeta b(gamma))`.             `(HPK9bw)`

Indeed `(HPK9bu)` makes the displayed map multiplicative, and its `mu_m`
ambiguity gives bijectivity on every arrow fiber.

Let `G_lambda` act on `Y=X times T` by

`(gamma,z):(s(gamma),t) |-> (r(gamma),zt)`.           `(HPK9bx)`

This action is free because even a nontrivial isotropy root
`zeta in mu_m` translates the circle without fixed points.  Its orbit
relation `E` is

`(x,u) E (y,t)` iff `(x,y) in R`
`  and u^m=lambda(x,y)t^m`.                           `(HPK9by)`

Choose a Borel `m`th-root map `r:T->T`.  The measure-space isomorphism

`(x,u) |-> ((x,u^m),u/r(u^m))`
`Y -> (X times T) times mu_m`                         `(HPK9bz)`

identifies `E` with `R(lambda) times (mu_m)^2`, where `(mu_m)^2` is the full
finite relation.  Cordeiro's product theorem and finite-groupoid soficity
therefore make `E` sofic.

It remains to recover the isotropy-bearing root groupoid from this principal
relation.  Every partial bisection `alpha` of `G_lambda` induces the partial
transformation of `Y`

`(s(gamma),t) |-> (r(gamma),zt)`, `(gamma,z) in alpha`. `(HPK9ca)`

This defines a multiplicative map

`[[G_lambda]] -> [[E]]`.                              `(HPK9cb)`

It preserves trace.  An induced point `(s(gamma),t)` is fixed exactly when
`r(gamma)=s(gamma)` and `zt=t`.  Principality of `R` makes `gamma` a unit,
and circle translation makes `z=1`; this is exactly the condition that
`(gamma,z)` was a unit of `G_lambda`.  Thus restricting a sofic approximation
of `E` along `(HPK9cb)` proves that `G_lambda`, hence `Sigma_m`, is sofic.
The bisection embedding `(HPK9av)--(HPK9ax)`, now with alphabet `mu_m`, and
the same product amplification prove that `Gamma` is sofic.  End proof.

When `R` is ergodic, `H_lambda=T` is equivalent to ergodicity of the
skew-product relation `(HPK9bt)`.  Corollary 3G and Theorem 3H therefore
leave a precise principal endpoint: only a Mackey-full cocycle whose
ergodic circle skew product is not yet known to be sofic can survive.  It is
not known that compact skew products of arbitrary sofic relations are sofic;
asserting that permanence here would subsume the finite-central-kernel gate.

The skew-product endpoint immediately gives a stronger countable-range
theorem than the virtual scalar-root argument above.

**Lemma (countable-range skew products are sofic).**  Let `R` be a sofic
countable pmp equivalence relation on `(X,mu)`, and let

`eta in Z^1(R,T)`.                                    `(HPK9cc)`

If `eta` is cohomologous to a cocycle with values in a countable subgroup
`A<T`, then the skew-product relation `R(eta)` is sofic.

**Proof.**  Cohomologous cocycles have isomorphic skew products.  More
explicitly, if

`eta(x,y)=f(x) eta_0(x,y) f(y)^(-1)`,                 `(HPK9cd)`

then `(x,t) |-> (x,f(x)^(-1)t)` identifies `R(eta)` with `R(eta_0)`.
We may therefore suppose that `eta` itself is `A`-valued.

Let `S_A` be the orbit relation of the translation action

`A action (T,Haar)`.                                  `(HPK9ce)`

The countable abelian group `A` is amenable, so `S_A` is hyperfinite and
hence sofic (Cordeiro, Corollary 3.4).  Cordeiro's product theorem
(Theorem 3.5) makes `R times S_A` sofic.  But

`R(eta) < R times S_A`,                               `(HPK9cf)`

because an arrow of `R(eta)` has `x R y` and
`u=eta(x,y)t`, with `eta(x,y) in A`; hence `u S_A t`.  The cocycle identity
makes this a Borel pmp subrelation on the same unit space `X times T`.
Soficity passes to subgroupoids by Cordeiro's Theorem 3.1(4), so `(HPK9cf)`
proves the claim.  End proof.

Here the use of a **subrelation** is essential.  No finite quotient of `A`
and no approximate homomorphism from the circle is being constructed.  The
ambient product relation supplies all `A`-translations, and the actual
cocycle selects a subgroupoid of it, so there is no carry or holonomy repair.

**Corollary 3I (countable cocycle range closes the bounded phase gate).**
In the setup of Theorem 3H, if the class of `lambda` has a representative
with countable scalar range, then `Gamma` is sofic.

**Proof.**  Let `A<T` be the countable subgroup generated by that range.
The lemma makes `R_Q(lambda)` sofic, and Theorem 3H applies.  End proof.

Thus any surviving bounded-exponent obstruction has no countable-range
gauge, even after finite-index restriction.  Corollary 3I recovers the
conclusions of Theorem 3D and Corollary 3F in their common-Cartan application
without finite generation, virtual divisibility, or property `(T)`.  This is
an alternative proof of a conclusion already implicit in Theorem 3A, not a
stronger torsion-splitting theorem.

Exact countable range is not necessary.  The class of such skew products is
closed under the convergence which is natural for circle cocycles, provided
the base action is essentially free.

**Theorem 3J (statistical closure of countable-range skew products).**  Let a
countable group `Q` act essentially freely and pmp on `(X,mu)`, and suppose
its orbit relation `R_Q` is sofic.  Let

`eta_n, eta in Z^1(Q action X,T)`                     `(HPK9cg)`

and suppose, for every `q in Q`,

`eta_(n,q) -> eta_q in measure`.                      `(HPK9ch)`

If every `eta_n` is cohomologous to a cocycle with values in some countable
subgroup `A_n<T`, then `R_Q(eta)` is sofic.

**Proof.**  By the countable-range lemma, every relation `R_Q(eta_n)` is
sofic.  Let `alpha_n` and `alpha` be the skew-product actions on
`X times T`; with one fixed convention,

`alpha_n(q)(x,t)=(qx,eta_(n,q)(x)t)`.                 `(HPK9ci)`

These actions converge on the measure algebra.  First take a measurable
rectangle `B times C`.  The base coordinate in `(HPK9ci)` is independent of
`n`, while the fiberwise symmetric-difference error is bounded by

`m_T(C triangle zC)`, `z=eta_(n,q)(x)eta_q(x)^(-1)`. `(HPK9cj)`

Translation is continuous on the measure algebra of the circle, so the
quantity in `(HPK9cj)` tends to zero in measure in `x`; it is bounded by
one, hence its integral tends to zero.  Finite unions of rectangles are
dense in the product measure algebra, and all the transformations preserve
measure.  Therefore, for every measurable `D subset X times T`,

`measure(alpha_n(q)D triangle alpha(q)D) -> 0`.       `(HPK9ck)`

It follows by a finite union bound that all finite Boolean statistics of
translates of a finite measurable partition converge.  Stabilizer statistics
converge as well, without any circle-rounding argument: essential freeness of
the base says that, for `q!=1`, neither `alpha_n(q)` nor `alpha(q)` fixes a
positive-measure set.  Thus the finite labelled rooted-neighborhood
statistics of `R_Q(eta_n)` converge to those of `R_Q(eta)`.

Soficity of a measured equivalence relation is exactly finite approximability
of these statistics.  Given one finite test and `epsilon>0`, first choose `n`
so that the statistics above differ by less than `epsilon/2`, and then choose
a finite sofic model of `R_Q(eta_n)` within `epsilon/2`.  The same model is an
`epsilon`-model of `R_Q(eta)`.  Diagonalizing over the countable tests proves
the theorem.  End proof.

**Corollary 3K (closure criterion for the bounded phase gate).**  In the
setup of Theorem 3H, if `lambda` belongs, in the topology `(HPK9ch)`, to the
closure of the cocycles which admit a countable-range gauge, then `Gamma` is
sofic.

**Proof.**  Theorem 3J makes `R_Q(lambda)` sofic, and Theorem 3H applies.
End proof.

The closure condition has a useful intrinsic formulation.  Give
`Z^1(Q action X,T)` the topology of convergence in measure on every group
coordinate, and let

`Z^1_cr={eta: eta is cohomologous into some countable A<T}`. `(HPK9cl)`

This is a subgroup.  Indeed, if gauges put `eta` and `theta` into countable
subgroups `A` and `B`, respectively, the product gauge puts `eta theta` into
the countable subgroup generated by `A union B`; inverses are handled in the
same way.  Consequently

`H^1_cr(Q action X,T)`
`  :=Z^1(Q action X,T)/closure(Z^1_cr)`               `(HPK9cm)`

is a well-defined topological quotient group.  It is deliberately coarser
than ordinary reduced measurable cohomology.  If `B^1` denotes the
coboundaries, then

`B^1 subset Z^1_cr`, hence
`closure(B^1) subset closure(Z^1_cr)`.                `(HPK9cn)`

**Corollary 3L (the surviving phase has nonzero countable-reduction
class).**  In the setup of Theorem 3H,

`[lambda]=0 in H^1_cr(Q action X,T)  ==>  Gamma is sofic`. `(HPK9co)`

In particular, vanishing of the class of `lambda` in reduced measurable
cohomology `Z^1/closure(B^1)` is sufficient for soficity.

**Proof.**  The hypothesis in `(HPK9co)` is exactly that `lambda` belongs to
the closure in Corollary 3K.  The final assertion follows from `(HPK9cn)`.
End proof.

There is an important limit to this reformulation.  The displayed power
form of the phase cocycle does not define a smaller class of circle
cocycles.

**Proposition (the `m`th-power primitive normal form is universal).**  Let
`m>=1`.  For every circle cocycle

`eta in Z^1(Q action X,T)`                            `(HPK9cp)`

there is a measurable circle-valued `1`-cochain `b` such that

`b^m=eta`, `delta b in C^2(Q action X,mu_m)`.         `(HPK9cq)`

**Proof.**  Choose a Borel section `r:T->T` of the power map
`z |-> z^m`, and put `b_q(x)=r(eta_q(x))`.  Then `b^m=eta`.  Since `eta` is
a cocycle,

`(delta b)^m=delta(b^m)=delta eta=1`,

so `delta b` is `mu_m`-valued.  End proof.

Thus a density theorem for cocycles merely described as `lambda=b^m` with
`mu_m`-valued curvature would be a density theorem for **all** circle
cocycles.  The phase construction does come with additional data: its
specific curvature is the evaluated extension cocycle and its primitive is
tied to the Haar character field.  Any improvement over Corollary 3L must
use that compatibility.  The power equation alone supplies no leverage.

The quotient `(HPK9cm)` vanishes in the hyperfinite case.  The density
theorem of Bezuglyi--Sanadhya says that, for a hyperfinite Borel action and
any locally compact second countable target, coboundaries are dense in all
cocycles (their Borel topology is at least as strong as the fixed-measure
topology used here).  Therefore

`R_Q hyperfinite  ==> closure(B^1)=Z^1`
`                    ==> H^1_cr=0`.                  `(HPK9cr)`

Together with Corollary 3L this gives another route through the amenable
quotient case.  Its role is calibration, not a new proof of the general
problem: arbitrary principal sofic relations need not be hyperfinite, and
no corresponding density theorem is known for them.

There is a canonical hyperfinite envelope of every circle skew product.  It
is useful both as a possible next target and as a warning about the direction
of the missing permanence statement.

**Proposition (vertical wreath envelope).**  Use the cocycle convention from
`(HPK9ci)`, so

`eta_(qr)(x)=eta_q(rx) eta_r(x)`.                     `(HPK9cs)`

On `Y=X times T`, put

`B_q(x,t)=(qx,t)`,
`V_(r,s)(x,t)=(x,eta_r(sx)t)`, `r,s in Q`.            `(HPK9ct)`

The relation `V_eta` generated by all `V_(r,s)` is hyperfinite.  The maps
`B_q` normalize it, and if `E_eta` is the relation generated by the `B_q`
and `V_(r,s)`, then

`R_Q(eta) < E_eta`.                                   `(HPK9cu)`

More precisely, `E_eta` is generated by an action of

`W=(directSum_(Q times Q) Z) semidirect Q`
`  ~= (directSum_Q Z) wr Q`.                          `(HPK9cv)`

Thus `W` is an abstractly sofic group whenever `Q` is sofic.

**Proof.**  The `V_(r,s)` are fiberwise circle translations and hence
commute.  They therefore define an action of the countable abelian group
`D=directSum_(Q times Q) Z`; its orbit relation `V_eta` is amenable and
therefore hyperfinite.  Direct calculation gives

`B_q V_(r,s) B_q^(-1)=V_(r,sq^(-1))`.                `(HPK9cw)`

Hence the `B_q` act on `D` by shifting the second coordinate and together
give the semidirect-product action `(HPK9cv)`.  Grouping the direct sum first
over the second coordinate identifies it with the displayed restricted
wreath product.  Restricted wreath products of sofic groups are sofic.

Finally the skew transformation in `(HPK9ci)` is

`alpha(q)=B_q V_(q,1)`.                               `(HPK9cx)`

Every generator of `R_Q(eta)` therefore belongs to `E_eta`, proving
`(HPK9cu)`.  End proof.

If `E_eta` were sofic, subgroupoid permanence would make `R_Q(eta)` sofic.
The proposition does **not** prove that premise.  Abstract soficity of `W`
does not imply soficity of this particular pmp action.  Equivalently, the
normal hyperfinite relation `V_eta` cannot simply be adjoined to the lifted
base relation using a known permanence theorem in this orientation.

The finite obstruction is visible inside the proof.  Coordinatewise
rounding of every scalar `eta_r(sx)` to a root of unity commutes with the
index shift `(HPK9cw)`.  But it need not preserve the multiplicative
relations among the vertical generators which act trivially at `x`; those
relations include the cocycle identity `(HPK9cs)`.  A nonzero rounded carry,
however small on the circle, moves the entire finite phase fiber.  Thus a
sofic model of `E_eta` still requires exactly the relation-preserving phase
completion isolated in `(HPK18)`.  The wreath envelope relocates the gate
to action soficity; it does not bypass it.

The same obstruction has a universal projective-shift form.  This removes
the arbitrary cocycle from the structure map and places all of the
difficulty in one compact-bundle lift.

**Proposition (universal projective-shift pullback).**  Let

`P_Q=T^Q/T_diag`,                                     `(HPK9cy)`

where the circle acts on `T^Q` by constant scalar multiplication, and let
`R_q f(s)=f(sq)` be the right shift.  For the cocycle `eta`, define

`f_x(s)=eta_s(x)`, `Phi_eta(x)=[f_x] in P_Q`.         `(HPK9cz)`

Then `Phi_eta` is `Q`-equivariant.  The formula

`c_q([f])=f(q)f(1)^(-1)`                              `(HPK9da)`

defines a universal circle cocycle on `P_Q`, and

`eta_q(x)=c_q(Phi_eta(x))`.                           `(HPK9db)`

Moreover the skew action `Q action X times T` is isomorphic to the pullback
of the shift action on `T^Q` through `Phi_eta`.  Explicitly, put

`Z_Phi={(x,f) in X times T^Q:[f]=Phi_eta(x)}`.        `(HPK9dc)`

Give each fiber its diagonal-circle Haar measure.  Then

`I:X times T -> Z_Phi`, `I(x,t)=(x,t f_x)`           `(HPK9dd)`

is a measure-space isomorphism and conjugates the skew action to

`q(x,f)=(qx,R_q f)`.                                 `(HPK9de)`

**Proof.**  Apply the cocycle identity `(HPK9cs)` with the pair `(s,q)`:

`f_(qx)(s)=eta_s(qx)=eta_(sq)(x)eta_q(x)^(-1)`
`          =f_x(sq)f_x(q)^(-1)`.                     `(HPK9df)`

The last scalar is independent of `s`, so `(HPK9df)` says exactly that
`Phi_eta(qx)=R_q Phi_eta(x)`.  Formula `(HPK9da)` is independent of the
representative `f`; and

`c_q(R_r[f])c_r([f])`
` =f(qr)f(r)^(-1) f(r)f(1)^(-1)=c_(qr)([f])`,

so it is a cocycle.  Since `f_x(1)=eta_1(x)=1`, `(HPK9db)` follows.

Every lift of `[f_x]` is uniquely `t f_x`, so `(HPK9dd)` is a fiberwise
Haar-preserving bijection.  Finally `(HPK9df)` gives

`eta_q(x)t f_(qx)=t R_q f_x`,                         `(HPK9dg)`

which is precisely the conjugacy `(HPK9de)`.  End proof.

Consequently, a finite model of `R_Q(eta)` is exactly a coherent lift of the
projective configuration factor `Phi_eta` through

`T^Q -> P_Q`.                                        `(HPK9dh)`

Soficity of the base relation lets one include every finite partition of
`P_Q` pulled back by `Phi_eta` as vertex colors.  What it does not provide is
a choice of representatives in `T^Q` whose right-shift overlaps agree away
from `o(1)` of the finite chart.  A Borel section of `(HPK9dh)` gives
representatives pointwise, but its shift defect is exactly the cocycle
`(HPK9da)`; coordinatewise torsion rounding reintroduces the carries from
`(HPK18)`.

This also explains why ordinary product permanence is insufficient.
`Z_Phi` carries the relatively Haar measure supported on the fiber product,
not the independent product of the two marginal actions.  The needed new
input is an **existential, relative, Hamming-exact finite-circle-bundle
selection** for the particular principal circle bundle `(HPK9dh)`.  Austin's
terminology `model-surjective` must not be used here: the quotient
`T^Q->P_Q` is exactly the Popa factor map, and it is not model-surjective for
some residually finite property-`(T)` groups and sofic approximations.  That
failure comes from good models in nonzero finite-graph cohomology sectors.
It does not obstruct `(HPK18)`: Austin's bad models are already exact circle
cocycles.  On every fixed finite chart the exact cocycles form a closed
subgroup of a finite torus, whose torsion points are dense, so any exact
sector can be approximated by finite-phase exact cocycles.  Our requirement
is instead to select one model sequence whose vanishing raw cocycle defect
forces vanishing distance to the exact cocycle locus, with equality away from
`o(1)` vertices after torsion approximation.  This is exactly the qualitative
cocycle-stability gate `(CS1)--(CS8)`, not a cohomology-sector restriction.
The full audit, stabilizer-character classification, and torsion-density
argument are in
`notes/POPA_FACTOR_MODEL_LIFTING.md`.  Such a selection would make the
skew relation sofic and close Theorem 3H.  Without it, the proposition is an
exact reformulation rather than a proof: every circle cocycle occurs by
`(HPK9cz)--(HPK9db)`.

This is genuinely stronger than Theorem 3A and Corollary 3I: the limiting
cocycle need not itself have a countable-range gauge.  It also identifies a
sharper obstruction.  A surviving bounded-exponent phase class must lie
outside the convergence-in-measure closure of all countable-reducible
circle cocycles, after every finite-index restriction.

Essential freeness in Theorem 3J is load-bearing.  Topological closeness of
circle rotations does not control fixed points: a nontrivial rotation fixes
nothing even when its angle tends to zero.  Here every nontrivial word moves
the base almost everywhere, so the problematic stabilizer statistic is
identically zero throughout the approximating sequence.  This is precisely
why `(HPK9ck)` suffices here but ordinary weak density of finite actions did
not suffice in the property-MD shortcut.

There is one immediate case where the condition is automatic.  If the phase
exact sequence `(CTM17)` itself splits and its kernel has exponent `m`, choose
the section to be a homomorphism.  Then `v=1`, `(HPK9c)` says that `b` is a
1-cocycle, and `(HPK9g)` holds with `r=b`.  Hence:

**Corollary (split bounded-exponent phase kernel).**  A regular-trace
common-Cartan model whose permutation-kernel exact sequence splits and whose
kernel has bounded exponent can exist only for a sofic group `Gamma`.

The common-Cartan hypothesis is essential here.  There are split
bounded-exponent-abelian-by-residually-finite nonsofic groups in
`(AB4)--(AB5)`; the corollary says precisely that their given abelian kernel
cannot occur as the full phase kernel of such a model.

## 3. The finite-window shadow

Choose diagonal representatives `a_(n,k):[d_n]->T` for the elements `(HPK3)`
and permutation representatives `sigma_(n,g)`.  The theorem has the following
entirely finitary shadow.  For every fixed `k,l in K` and `g in Gamma`,

`d_n^(-1) sum_j |a_(n,kl)(j)-a_(n,k)(j)a_(n,l)(j)|^2 ->0`, `(HPK10)`

`d_n^(-1) sum_j a_(n,k)(j) -> 1_(k=1)`,                `(HPK11)`

and, with the harmless inverse determined by the permutation convention,

`d_n^(-1) sum_j |a_(n,gkg^(-1))(j)`
`                 -a_(n,k)(sigma_(n,g)^(-1)j)|^2 ->0`. `(HPK12)`

Equations `(HPK10)--(HPK12)` say that the coordinates are asymptotic
character labels, Haar-generic on every finite Fourier window, and
asymptotically transported by the quotient chart.

The original monomial representatives also supply phase functions
`c_(n,g):[d_n]->T` for every `g in Gamma`.  With the convention used below,
their multiplication defects say

`d_n^(-1) sum_j |c_(n,h)(j)c_(n,g)(sigma_(n,h)j)`
`                    -c_(n,gh)(j)|^2 ->0`.             `(HPK12a)`

The restriction of this phase cocycle to the asymptotically trivial
permutation kernel is the character field `(HPK10)--(HPK12)`.  Thus the
finite completion problem concerns the whole cocycle `(HPK12a)`, with the
Haar kernel law retained.  Equivalently, after choosing a section, it asks
for a combinatorial finite-order version of the primitive `(HPK9b)--(HPK9d)`.

The word **asymptotic** is load-bearing.  The finite coordinate labels need
not themselves be characters, and `(HPK10)` is an `L^2` equality rather than
equality outside a small set.  Pointwise circle rounding does not change one
notion into the other; `notes/PHASES.md`, Sections 6a--6d, proves the precise
obstruction.  The cocycle-stability criterion `(CS1)--(CS8)` is one sufficient
way to cross this gap, not a consequence of `(HPK10)--(HPK12)`.

## 4. Exact finite-window Fourier-completion gate

Here is the exact output that would suffice.  It is useful because it
separates the missing rounding statement from the already solved Cartan and
trace estimates.

**Theorem 4 (finite phase completion implies soficity).**  Suppose that for
arbitrarily accurate finite windows there are finite sets `Y_n`, maps

`sigma_n:Gamma -> Sym(Y_n)`,
`z_(n,g):Y_n -> mu_(m_n)`                              `(HPK13)`

with possibly growing `m_n`, such that for every fixed `g,h`:

1. `sigma_(n,g)sigma_(n,h)=sigma_(n,gh)` off `o(|Y_n|)` points;
2. with the convention
   `M_(n,g)e_y=z_(n,g)(y)e_(sigma_(n,g)y)`,

   `z_(n,h)(y) z_(n,g)(sigma_(n,h)y)=z_(n,gh)(y)`      `(HPK14)`

   off `o(|Y_n|)` points; and
3. the monomial traces satisfy

   `|Y_n|^(-1) sum_(y in Fix(sigma_(n,g))) z_(n,g)(y)
      ->1_(g=1)`.                                     `(HPK15)`

Then `Gamma` is sofic.

**Proof.**  Let the monomial datum act on

`Omega_n=Y_n times mu_(m_n)`

by

`Pi_(n,g)(y,u)=(sigma_(n,g)y,z_(n,g)(y)u)`.            `(HPK16)`

The two failures in `(HPK13)--(HPK14)` are exactly the two ways in which
`Pi_(n,g)Pi_(n,h)` can differ from `Pi_(n,gh)`, so multiplication holds off
`o(|Omega_n|)` points.

Let `r_(n,g)` be the density of `y` for which `sigma_(n,g)y=y` and
`z_(n,g)(y)=1`.  These and only these base points give fixed points in every
fiber of `(HPK16)`.  If `t_(n,g)` denotes the trace in `(HPK15)`, then

`r_(n,g) <= |t_(n,g)|+(1-r_(n,g))`,

because all remaining diagonal summands have total absolute mass at most
`1-r_(n,g)`.  Hence

`r_(n,g) <= (1+|t_(n,g)|)/2`.                          `(HPK17)`

For `g!=1`, `(HPK15)` makes the right side tend to `1/2`.  Thus `(HPK16)`
moves at least `1/2-o(1)` of its points.  Taking a fixed diagonal product
power makes its fixed-point density at most `(1/2+o(1))^L`, while the
multiplication error grows by at most the factor `L`.  First choose `L` and
then a sufficiently accurate window.  This gives the standard asymptotically
free sofic approximations.  End proof.

Theorem 4 does not assume a uniform bound on `m_n`; exact equality off a
small set removes the shrinking root-spacing problem.  The unresolved step
is precisely

`L^2 phase cocycle with Haar kernel law (HPK10)--(HPK12a)`
`  ==> combinatorial finite-phase chart (HPK13)--(HPK15)`. `(HPK18)`

This is the phase-kernel form of the normal-IRS rounding problem.  Manzoor's
normal-Dirac formulation shows why an unconditional proof of `(HPK18)` would
settle hyperlinear versus sofic rather than follow from a generic IRS density
statement.

In section language, `(HPK18)` asks to replace the measurable primitive
`b_q` of `(HPK9c)` on each finite window by a finite-order primitive for which
the same equation is literally true away from a small exceptional set.  It
is not enough to approximate each `b_q` in chordal `L^2`: the spacing of the
finite phase group can shrink at the same rate, so metric closeness need not
imply equality in Hamming measure.

## 5. A positive split finite-rank case

There is one group-theoretic regime in which the phase kernel can already be
removed without `(HPK18)`.

**Theorem 5 (split finite-rank abelian kernel).**  If

`Gamma=K semidirect_alpha Q`,                         `(HPK19)`

where `K` is finitely generated abelian and `Q` is sofic, then `Gamma` is
sofic.

**Proof.**  Let `Hol(K)=K semidirect Aut(K)`.  The map

`(k,q) |-> ((k,alpha(q)),q)`
`Gamma -> Hol(K) times Q`                              `(HPK20)`

is an injective homomorphism.

The holomorph of a finitely generated abelian group is residually finite.
Indeed, writing `K=Z^r directSum T` with `T` finite, `Hol(K)` has a
finite-index subgroup isomorphic to a subgroup of the integral affine group
`Z^r semidirect GL_r(Z)`, which embeds in `GL_(r+1)(Z)`.  Integral linear
groups are residually finite directly: reduce modulo a prime which does not
divide a chosen nonzero entry of `A-1`.  Residual finiteness passes from a
finite-index subgroup to the whole group by taking the finite-index normal
core and intersecting the finitely many conjugates of a separating subgroup.
Thus `Hol(K)` is residually finite and hence sofic.  Products and subgroups of
sofic groups are sofic, so `(HPK20)` proves the claim.  End proof.

This theorem also applies whenever `Hol(K)` is known to be sofic, without a
finite-generation assumption.  It does not apply to a nonsplit extension:
the unrestricted wreath embedding needed for an arbitrary extension has the
same dangerous extension orientation.

## 6. Kun--Thom calibration

The split hypothesis alone is not enough.  The explicit quotient
`(AB1)--(AB3)` in `notes/NOTEPAD.md` is

`P=reduced Z[G/Gamma] semidirect G`,                  `(HPK21)`

where `G` is residually finite but `P` is nonsofic.  Its abelian kernel is
not finitely generated as an abelian group.  Strict compression forces
`G/Gamma` to be infinite: a proper inclusion between the conjugate
subgroups `t Gamma t^(-1)<Gamma` is impossible at finite index, since the
two conjugates have equal index in `G`.  Therefore the augmentation kernel
in `(HPK21)` has infinite rank, exactly outside Theorem 5.

Pontryagin duality identifies

`dual(reduced Z[G/Gamma])=T^(G/Gamma)/T`,              `(HPK22)`

with quotient Haar measure and the shifted `G`-action.  Thus Theorem 1
specializes to the same algebraic dual action already isolated after
`(AB1)--(AB3)`; it does not silently add a periodic model.  If `(HPK21)` had
regular-trace common-Cartan microstates, their finite shadows would satisfy
`(HPK10)--(HPK12)`, while its proved nonsoficity says that they could not be
upgraded to `(HPK13)--(HPK15)`.

This is the required stress test.  Any proof of `(HPK18)` must use a
hypothesis genuinely forced by **all** hyperlinear models, not finite rank,
splitness, residual finiteness of the quotient, or Haar genericity alone.

For the bounded-exponent quotient following `(AB3)`, the stress test is even
sharper.  It is a split extension by an infinite-dimensional
`Z/mZ`-module, yet it is nonsofic.  The split bounded-exponent corollary does
not contradict this: it proves that no regular common-Cartan embedding can
have that displayed module as its entire permutation kernel.  A hypothetical
common-Cartan hyperlinear embedding would have to produce a different
abelian kernel and a nondivisible Bockstein residue `(HPK9e)--(HPK9g)`.

## 7. Current boundary

The common-Cartan route now has four exact layers:

1. Birkhoff monomialization gives an abelian phase kernel over a sofic
   quotient (`CTM1--CTM19`);
2. the regular trace forces that kernel to appear as the Haar character
   field `(HPK4)--(HPK12)`;
3. for bounded-exponent kernels, the Bockstein residue
   `(HPK9e)--(HPK9g)` is the exact obstruction to fixed-alphabet completion;
4. for torsion kernels, torsion splitting `(HPK9ab)--(HPK9ah)`, or directly
   combinatorial
   finite-phase completion `(HPK13)--(HPK15)`, gives a sofic approximation.

There is also an unsplit endpoint: soficity of the torsion central groupoid
`Sigma_omega` implies soficity of `Gamma` through the full-bisection embedding
`(HPK9at)--(HPK9ay)`.  Universal permanence for this endpoint is not known
and would already settle the finite-central-kernel extension problem.  A
finite-index restriction on which the torsion class vanishes is enough by
Theorem 3C.

Theorem 3H gives a principal endpoint for bounded exponent, and Corollary 3I
settles that endpoint whenever the circle cocycle is cohomologous into any
countable subgroup of `T`: its skew product is a subgrouprelation of the
sofic product `R_Q times S_A`.  Consequently a remaining bounded-exponent
class must have genuinely uncountable scalar range in every gauge (and after
every finite-index restriction), in addition to being Mackey-full.

The statistical-closure theorem `(HPK9cg)--(HPK9ck)` sharpens this once more:
the class must remain outside the convergence-in-measure closure of all
countable-reducible cocycles.  Equivalently, it must define a nonzero class
in `(HPK9cm)` after every relevant finite-index restriction.  The universal
root calculation `(HPK9cp)--(HPK9cq)` corrects a tempting overstatement: a
density theorem based only on the form `lambda=b^m` would cover every circle
cocycle.  The next positive target must use the compatibility of the
particular primitive `b` and curvature `omega` with the phase extension, not
the power equation by itself.

Only the general implication from layer 2 to layer 4 is missing.  The
torsion-kernel criterion settles it when the residue in layer 3 is
torsion-split; allowing all roots of unity removes both explicit
minimal-alphabet counterexamples above.  Slow tensor amplification
`(HPK9q)--(HPK9u)` shows that the
residue may be assumed to live on a principal quotient relation and settles
the treeable case, but arbitrary principal sofic relations are not covered by
that vanishing argument.  The exact torsion-kernel obstruction is now
`(HPK9ah)`, not the larger minimal-alphabet Bockstein kernel.  The amenable case
is supplied by Burton--Chaudkhari--Juschenko--Muliarchyk, while the general
case cannot be obtained by averaging over a finite window without paying its
Følner boundary.  A successful general proof must exploit the normal `0/1`
law or the simultaneous prefix-path structure beyond the Haar Fourier
moments recorded here.

Primary source pins:

* Burton--Chaudkhari--Juschenko--Muliarchyk,
  *Hyperlinear approximations to amenable groups come from sofic
  approximations*, arXiv:2311.09202.
* Aareyan Manzoor, *There Is An Equivalence Relation Whose von Neumann
  Algebra Is Not Connes Embeddable*, arXiv:2502.06697v2.
* Sorin Popa, *Cocycle and Orbit Equivalence Superrigidity for Malleable
  Actions of w-Rigid Groups*, arXiv:math/0512646.
* Luiz Cordeiro, *An elementary approach to sofic equivalence relations*,
  arXiv:1608.05608, Theorem 3.4.
* Luiz Cordeiro, *An elementary approach to sofic groupoids*,
  arXiv:1708.08023; and *On sofic groupoids and their full groups*,
  C. R. Acad. Sci. Paris 356 (2018), Theorems 2.1, 2.4, and 2.5.
* Yoshikata Kida, *Splitting in orbit equivalence, treeable groups, and the
  Haagerup property*, arXiv:1403.0688, Corollary 2.8.
* Vadim Kaimanovich and Klaus Schmidt, *Ergodicity of cocycles. 1: General
  theory*, especially the compact skew-product/Mackey reduction in Section
  2, Propositions 2.5--2.7.
* Sergey Bezuglyi and Shrey Sanadhya, *Cohomology of hyperfinite Borel
  actions*, arXiv:2001.09205; Groups Geom. Dyn. 15 (2021), 1363--1398.
