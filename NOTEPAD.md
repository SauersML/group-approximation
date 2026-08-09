# NOTEPAD

Consolidated working notes. Formerly `BUILD_ITERATION_NOTES.md`,
`docs/HISTORY.md`, and `docs/REORGANIZATION.md`; merged 2026-08-06.
Each part is kept verbatim under its own banner.

---

# The square-root loss is optimal for representation-functor conversions (2026-08-08)

The exterior-amplification criterion below loses a factor `sqrt d`.  This is
not an artifact of the full exterior algebra.  Let

`Pi : U(d) -> U(D)`

be any continuous finite-dimensional unitary representation, and write

`ell_Pi(U)^2 = ||Pi(U)-1||_(2,D)^2
             = 2 - 2 Re(tr_D(Pi(U)))`.

Suppose the coordinate sign changes

`r_j = diag(1,...,1,-1,1,...,1)`

are all detected by `ell_Pi(r_j) >= a`.  (They are conjugate, so it is enough
to assume this for one `j`.)  If

`ell_Pi(exp(i t H)) <= L |t| ||H||_op + o(|t|)`

at the identity for every diagonal self-adjoint `H`, then

`L >= (a/2) sqrt d`.

Proof.  Restrict `Pi` to the diagonal torus and let `mu` be its normalized
weight distribution on `Z^d`.  Thus

`tr_D(Pi(diag(exp(i t_1),...,exp(i t_d))))
    = E_mu exp(i <m,t>)`.

For `r_j`,

`ell_Pi(r_j)^2 = 2(1-E_mu cos(pi m_j))
                = 4 P_mu(m_j is odd)`.

Hence `P_mu(m_j != 0) >= a^2/4` for every `j`, and therefore
`E_mu ||m||_2^2 >= d a^2/4`.  Averaging over sign vectors
`eps in {+1,-1}^d` gives

`E_eps E_mu <m,eps>^2 = E_mu ||m||_2^2`.

Choose one `eps` attaining at least this average and put
`H=diag(eps_1,...,eps_d)`, so `||H||_op=1`.  The second-order character
expansion gives

`ell_Pi(exp(i t H))^2
   = t^2 E_mu <m,eps>^2 + o(t^2)
   >= t^2 d a^2/4 + o(t^2)`.

Comparing first-order Lipschitz constants yields the claim.

Consequences.  Any universal, continuous representation-functor conversion
from operator-norm microstates to normalized-HS microstates which detects a
single bad eigendirection necessarily turns an operator defect `epsilon` into
an HS defect of order at least `epsilon sqrt d`.  The full exterior-algebra
construction has exactly this scale and is optimal up to constants.  Thus the
weak-MF free-lamp group cannot be made hyperlinear by a rate-free functor on
`U(d)` alone.  One must use group-specific structure: a trace-visible
Kazhdan/central corner, a quantitative MF profile with
`epsilon sqrt d -> 0`, or a different witness with a finite normal detector.

---

# Square-root MF profile implies hyperlinearity: exterior amplification (2026-08-08)

There is a dimension-sensitive route from operator-norm approximations to
normalized-HS approximations which is stronger than naive tensor
amplification.

Let `phi_n:G -> U(d_n)` be unital maps which are multiplicative on exhausting
windows with operator-norm error `epsilon_n`, and suppose every fixed
`g != 1` is eventually operator-norm separated from `1` by some `c_g>0`.  If

`epsilon_n * sqrt(d_n) -> 0`,

then `G` is hyperlinear.

For `U in U(d)`, let `Lambda(U)` be its action on the full exterior algebra
`Lambda^*(C^d)`, of dimension `2^d`, and let

`R_d(U) = Ad(Lambda(U))`

on the Hilbert--Schmidt space of endomorphisms of that exterior algebra.  This
is an exact homomorphism from `U(d)` to a unitary group.  The exterior character
identity gives

`tr_norm(R_d(U)) = | tr_norm(Lambda(U)) |^2
                  = | det((I+U)/2) |^2`.

If `W` is unitary and `||W-I||_op <= epsilon`, diagonalizing `W` gives

`|det((I+W)/2)|^2
   = product_j (1 - |lambda_j-1|^2/4)
   >= 1 - d*epsilon^2/4`.

Consequently

`||R_d(W)-I||_(2,norm)^2 <= d*epsilon^2/2`.

Thus the multiplicative defect of `R_d o phi_n` tends to zero under the stated
square-root profile.  Conversely, if `||U-I||_op >= c`, at least one eigenvalue
satisfies `|lambda_j-1|>=c`, and hence

`tr_norm(R_d(U)) <= 1-c^2/4`,
`||R_d(U)-I||_(2,norm)^2 >= c^2/2`.

This supplies dimension-free HS separation from operator-norm separation.
Finally take tensor powers `l_n -> infinity` sufficiently slowly that
`l_n*epsilon_n*sqrt(d_n) -> 0`.  The nontrivial normalized characters are
raised to the `l_n`-th power and therefore tend to zero, while multiplicative
defects still tend to zero.  These are hyperlinear microstates with the
canonical trace.

Application target: the explicit weak-MF nonsofic free-lamp group recorded
below becomes a hyperlinear nonsofic group as soon as Shulman's symmetric-double
approximations are shown to admit `epsilon_n sqrt(d_n) -> 0`.  Her qualitative
MF theorem does not state such a rate; extracting or disproving this profile is
now a concrete quantitative subproblem.  The condition is not cosmetic:
exterior amplification detects one bad eigenvalue with constant trace weight,
and the same character formula shows why a full-rank error costs the factor
`sqrt(d)`.

---

# The Hilbert-ultraproduct trap in defect-localized commutant pinning (2026-08-08)

There is a seductive but invalid proof that property `(T)` forces commutant
no-growth in every hyperlinear model.  Writing `U_n(g)` for a normalized-HS
model of a compressed pair `Gamma < G`, let `A_n` be the averaging operator of
the adjoint maps `Ad U_n(s)` on `L^2(M_{d_n})`, and let `V_n` be its low-spectral
subspace.  The corresponding low-spectral subspace for `t Gamma t^{-1}` can be
defined by conjugating `A_n` with `Ad U_n(t)`, so it has **exactly the same
finite dimension** as `V_n`.  Since `t Gamma t^{-1} <= Gamma`, it is tempting to
claim that `V_n` is almost contained in the conjugate space, apply
`exists_mem_close_of_almost_le`, and conclude equality of the two commutants in
the tracial ultraproduct.

The containment claim is false at exactly one interface.  A group-relation
defect `U_n(g)U_n(h)-U_n(gh)` that tends to zero in normalized HS norm acts
negligibly by left/right multiplication on uniformly operator-norm-bounded
vectors (in particular, on lamp unitaries).  It need not act negligibly on an
arbitrary normalized vector of `L^2(M_{d_n})`, whose operator norm can be of
order `sqrt(d_n)`.  The low-spectral spaces may contain such vectors.  They
define vectors in the Hilbert-space ultraproduct, but need not define
equiintegrable vectors in `L^2` of the **tracial** ultraproduct.  Property `(T)`
of the exact ultraproduct representation controls the latter and says nothing
about the former.  Thus an adversarial high-operator-norm subspace can carry the
finite-dimensional rank discrepancy while every bounded lamp still sees only
small relation defects.

This explains simultaneously why:

* the exact finite-dimensional commutant collapse is valid;
* the same rank argument in a hyperlinear model is not valid;
* an SOS/Kazhdan-Laplacian certificate alone does not repair it (its evaluated
  identity is only HS-close as a superoperator and can fail on the same
  non-equiintegrable directions);
* the existing pinning lemmas are correct but do not supply the missing
  localization theorem.

A valid completion of this lane must prove an additional **equiintegrable
spectral localization** statement: the portion of the low-spectrum needed for
the equal-rank comparison must admit uniformly bounded representatives, or the
non-equiintegrable portion must be shown incapable of carrying the rank balance.
Without such a statement, invoking equal dimensions is invalid.  The Bernoulli
shift inclusion `uNu* < N` in a `II_1` factor is the calibration showing that no
abstract trace/dimension replacement can provide it.

---

# Automorphic hyperlinear-action charts cannot bypass the Kun--Thom set-action obstruction (2026-08-08)

Let `X` be a `G`-set and let `Delta = directSum_X C_2`, with `G` acting by
permuting the lamp coordinates.  If the induced action
`G -> Aut(Delta)` is a sofic `C`-action in the sense of Alekseev--Bradford,
Definition 4.23, for **any** class of target groups `C`, then the original
set action `G curvearrowright X` is a sofic action.

For finite `F subset G` and `Z subset X`, put in the automorphic test set
`E subset Delta` the identity, the single lamps `delta_x` for `x in Z`, and
the products needed by the finite covariance window.  An automorphic chart
provides a finite permutation model `phi:G -> Sym(A)` and, on a large set of
`s in A`, injective partial homomorphisms `pi_s:E -> Lambda`.  Define

`iota_s(x) = pi_s(delta_x)`.

The union of these finitely many images is a finite set `B`.  Injectivity of
`pi_s` makes each `iota_s:Z -> B` injective, and exact local covariance gives

`iota_(phi(g)s)(x) = iota_s(g^{-1}x)`

whenever both sides occur in the window.  These are exactly the orbit charts
of Alekseev--Bradford Definition 4.16.  Thus the set action is sofic.

For the Kun--Thom coset action `G curvearrowright G/Gamma`, this rules out the
apparently broader Alekseev--Bradford hyperlinear-action route.  If the set
action were sofic, their Corollary 5.5 applied to a finite lamp would make the
corresponding wreath product sofic, contradicting the Kun--Thom centralizer
theorem.  Consequently neither ordinary sofic orbit charts nor sofic
hyperlinear automorphic charts can produce the desired hyperlinear model.
Any successful construction must act directly at the tracial-microstate level
and cannot factor through those partial-homomorphism charts.

# The stable Steinberg-cover route for the binary Leavitt witness is trivial (2026-08-08)

For the binary Leavitt algebra `L = L_2(F_2)`, the graph-algebra K-theory exact
sequence has structure map `1-2 = -1` on every algebraic K-group of `F_2`.
It is therefore an isomorphism, and the stable algebraic K-groups of `L`
vanish, in particular `K_2(L)=0`.  Hence the stable Steinberg central extension
does not provide a nontrivial hyperlinear cover whose central quotient could
be `EL(L)`.  This closes the tempting route "make the Steinberg cover
hyperlinear, then invoke central-quotient closure."  The statement follows
from the long exact sequence for Leavitt path algebras in
Ara--Brustenga--Cortinas, arXiv:0903.0056 (and later general formulations such
as Gabe--Ruiz--Tomforde--Whalen, arXiv:1407.5094).  An unstable-rank kernel
would require a separate computation, but it cannot be justified by stable
`K_2` and is incompatible with using the stable Steinberg extension as the
proposed cover.

---

# The full-web Kazhdan obstruction to the one-unitary ansatz (2026-08-08)

The exact `tau`-fixed stratum observed in the Heisenberg surrogate does not
extend to the true Kun--Thom substitution web.  More strongly, its approximate
version is quantitatively sterile.

Let `S` be a Kazhdan set for `SL_d(Z)`, with constant `kappa > 0`, and let
`theta_s = Ad(pi(s))` be any finite-dimensional tracial unitary action.  If a
unitary `Z` satisfies

`max_{s in S} ||theta_s(Z) - Z||_2 <= epsilon`,

then the Kazhdan inequality for the conjugation representation gives

`dist_2(Z, Fix(theta)) <= epsilon / kappa`.

For the true Laurent substitution web, every element of `Fix(theta)` lying in
the common-web commutant commutes with all the conjugates
`A EL_r(F_q[x_1,...,x_d]) A^{-1}`.  Those conjugates generate
`EL_r(F_q[x_1^{+-1},...,x_d^{+-1}])`: each Laurent root
`e_ij(c x^v)` is a substitution conjugate of a positive-monomial root.  Hence
the fixed algebra commutes with every invisible Laurent letter `lambda(g)`.
If `Y` is the fixed-point projection of `Z`, then

`||[Z, lambda(g)]||_2 <= 2 ||Z-Y||_2 <= 2 epsilon / kappa`.

Consequently

`||Z lambda(g) Z* - lambda(g)||_2 <= 2 epsilon / kappa`,

so conditional expectation onto the Laurent/positive model algebra has norm
at least `1 - 2 epsilon/kappa`.  In particular, any asymptotically exact
one-unitary coboundary construction has absorption tending to `1`, never the
order-one escape required by the hyperlinear counterexample route.

The estimate gives a sharp stopping rule for the proposed constrained
optimization.  If

`a_g(Z) = ||E_W(Z lambda(g) Z*)||_2`

and `delta(Z)=max_(s in S)||theta_s(Z)-Z||_2`, then

`a_g(Z) >= 1 - 2 delta(Z)/kappa`.

Hence `a_g(Z) <= 1/2` forces `delta(Z) >= kappa/4`.  No penalty-constrained
search inside the global-coboundary family can simultaneously drive
coherence to zero and retain even fifty-percent mixing on the true web.  The
observed surrogate trajectory (coherence decreasing while absorption rises
toward one) is the predicted behavior, not merely an optimizer preference.
Surrogates lacking the full Kazhdan substitution web cannot test this
inequality.

Scope: this kills the global coboundary/joint-fixed ansatz only.  It does not
kill genuinely non-coboundary, window-dependent approximate 1-cocycles
`D_A` whose defect tends to zero without admitting a common transfer unitary
`Z`.  That non-coboundary sector is the actual remaining gauge problem.

# A monolithic finite-simple-lamp reduction (2026-08-08)

For a finite nonabelian simple group `K`, put

`B = directSum_(G/Gamma) K`,  `W = B semidirect G`.

If the coset action is faithful and transitive, then `B` is a minimal nonzero
normal subgroup of `W` and `C_W(B)=1`.  Indeed, a nonzero normal subgroup of
`B` contains one simple coordinate, and transitivity supplies every
coordinate.  An element centralizing `B` has trivial permutation part by
faithfulness and trivial base part because `Z(K)=1`.

It follows that every nontrivial normal subgroup of `W` meets `B`: if
`N cap B = 1`, then `[N,B] <= N cap B`, so `N <= C_W(B)=1`.  Therefore any
homomorphism from `W` to a tracial ultraproduct which is nontrivial on one
lamp is automatically faithful.  The Kun--Thom centralizer argument proving
nonsoficity works verbatim for every nontrivial lamp group, not only `Z/2`.
Thus a negative solution can equivalently be obtained by constructing just
one trace-visible lamp in this finite-simple-lamp generalized wreath product;
canonical-trace control on every group word is unnecessary.  What remains is
still substantive: no current operator-norm or Hilbert--Schmidt construction
is known to force that one lamp to occupy positive normalized rank.

---

# Kazhdan-corner extraction for simple groups (2026-08-08)

**Theorem.** Let `J` be a nontrivial simple group with Kazhdan property
`(T)`. If `J` is weak-MF in the operator-norm sense, then `J` is
hyperlinear.

**Proof.** Weak-MF gives an injective homomorphism

`rho:J -> U(B)`,  `B=(product_n M_(d_n))/(directSum_n M_(d_n))`,

where the ideal is the operator-norm null ideal. By the universal property,
`rho` extends to a unital star-homomorphism
`Phi:C*_max(J)->B`. Let `p` be the central Kazhdan projection and put
`q=1-p`. Since `u_g p=p` for every `g`, `Phi(q)` cannot vanish: otherwise
all `rho(g)` would equal one, contradicting injectivity. Put `z=Phi(q)` and
work in the nonzero unital corner `zBz`. The elements

`psi(g)=z rho(g)`

form a representation of `J` in `U(zBz)`. It is nontrivial; if every
`psi(g)=z`, then again `rho(g)=Phi(p)+z=1` for every `g`.

Lift `z` to projections `z_n` of ranks `r_n>0` and lift the `psi(g)` to
unitaries in `z_n M_(d_n) z_n = M_(r_n)` (polar correction changes the
lifts by operator-norm null sequences). Multiplicative defects tend to zero
in operator norm and hence in normalized Hilbert--Schmidt norm on the
`r_n`-corners.

For a finite Kazhdan set `S`, the positive Kazhdan Laplacian

`Delta=sum_(s in S) (u_s-1)*(u_s-1)`

satisfies `q Delta q >= kappa q` in `C*_max(J)` for some `kappa>0`.
Applying `Phi`, lifting, and taking the normalized corner traces gives

`liminf sum_(s in S) ||psi_n(s)-1||_(2,r_n)^2 >= kappa`.

Thus the resulting homomorphism from `J` into the tracial ultraproduct of the
`M_(r_n)` is nontrivial. Its kernel is a proper normal subgroup of the
simple group `J`, hence trivial. This is a hyperlinear embedding. End proof.

This theorem defeats rank blindness by changing the normalization to the
Kazhdan corner and then using the spectral-gap inequality to force positive
trace mass there. It does **not** apply to the weak-MF Kun--Thom free-lamp
group below: that amalgam is neither simple nor Kazhdan. It does apply to the
simple Kazhdan Leavitt witness `EL_4(L_(F_2)(1,2))` conditional on the single
presently open certificate that this group is weak-MF. No 2026 permanence
theorem found in the audit supplies that certificate; Shulman's symmetric
double theorem supplies weak-MF for the free-lamp amalgam, not for the
Leavitt elementary group.

### The leaf-truncation weak-MF ansatz has a uniform norm floor

Let `H_N` be the span of binary words of lengths at most `N`, and compress the
standard Leavitt/Fock creation and deletion operators to `H_N`.  Write the
compressions as `S_i,T_i`.  On every word of length `N`, `S_i` vanishes, so

`||(T_i S_i)-I||_op=1`.

On the vacuum vector both deletion operators vanish, so also

`||S_0 T_0+S_1 T_1-I||_op=1`.

The bad spaces have small relative rank, but operator norm sees them with
full strength.  Direct sums, amplification, and moving the boundary to a
deeper leaf preserve this norm-one defect.

There is a representation-independent bounded version.  Suppose
`S_0,S_1,T_0,T_1` are square matrices of norm at most `M>=1` and

`||T_0 S_0-I|| <= eps`, `||T_1 S_1-I|| <= eps`,
`||T_0 S_1|| <= eps`.

If `eps<1`, the first relation makes `S_0` invertible and gives

`||T_0 y|| >= ((1-eps)/M)||y||`

for every `y`: write `y=S_0x`, use
`||T_0S_0x|| >= (1-eps)||x||`, and
`||y||<=M||x||`.  The second relation similarly gives
`||S_1v|| >= ((1-eps)/M)||v||`.  Hence for a unit vector `v`,

`eps >= ||T_0S_1v|| >= (1-eps)^2/M^2`.

Equivalently

`eps >= ((M^2+2)-sqrt((M^2+2)^2-4))/2`.

For contractions this is `(3-sqrt(5))/2`.  Thus no uniformly bounded
approximate representation of the Leavitt generators can have vanishing
operator-norm defect, even before the completeness relation is imposed.

This closes the proposed Fock/leaf finite-section construction of weak-MF for
`EL_4(L_(F_2)(1,2))`.  It does not yet prove that the *group* is not weak-MF:
an arbitrary unitary microstate of the elementary group assigns unitaries to
root elements, not bounded operators `S_i,T_i`.  To promote the norm floor to
a group obstruction one would need a uniformly bounded interpretation of the
Leavitt generators inside a fixed finite portion of the maximal group
C-star-algebra, compatible with the Steinberg commutator multiplication.
No such interpretation is presently established, and the existence of
exotic group microstates remains exactly the weak-MF certificate.

---

# An explicit weak-MF nonsofic group (2026-08-08)

Let `Γ < G` be any of the residually finite Kazhdan infranormal pairs in
Kun--Thom, arXiv:2608.06222, Theorem E, and put

`H := G *_Γ (Γ × ℤ)`.

Then `H` is nonsofic by the kernel-checked free-lamp reduction together with
Kun--Thom Theorem 4.1.  It is also weak-MF in Shulman's operator-norm-injective
sense.  (This is weaker than Schafhauser's trace-MF terminology, which includes
approximation of the canonical regular trace and therefore implies
hyperlinearity.)  Indeed, the
factor maps

`G → G × ℤ`, `g ↦ (g,0)`, and `Γ × ℤ → G × ℤ`

into the first and second factors of

`D := (G × ℤ) *_Γ (G × ℤ)`

agree on `Γ`; the normal-form theorem for amalgams makes the induced map
`H → D` injective.  The group `G × ℤ` is weak-MF because `G` is residually finite.
Shulman, arXiv:2603.13564v2, Theorem 10 and its group corollary, proves that a
double `A *_C A` of an arbitrary weak-MF group `A` over an arbitrary subgroup
`C` is weak-MF.  Hence `D`, and therefore its subgroup `H`, is weak-MF.

This separates weak-MF from sofic.  It does **not** separate Schafhauser-MF or
hyperlinear from sofic: operator-norm separation can be supported on a subspace of vanishing
normalized rank (`Sofic/NormTraceGap`).  Shulman's construction supplies no
control of the canonical group trace.  Property-(T) corner extraction cannot
be recovered merely by passing to a property-(T) subgroup: every property-(T)
subgroup of the amalgam fixes a vertex of its Bass--Serre tree and is conjugate
into a factor.  Thus the remaining problem for this witness is exactly a
trace-visible version of Shulman's commutant-unitary lift, equivalently
Connes-embeddability of

`L(G) *_{L(Γ)} (L(Γ) ̅⊗ L(ℤ))`.

The same theorem does not automatically settle the Dogon--Vigdorovich
finite-central-extension candidate.  The decomposition of
`SL₂(ℤ[1/p])` uses the two Iwahori embeddings related by a commensuration that
does not extend to an automorphism of `SL₂(ℤ)`; it is a twisted amalgam, not
the identical symmetric double in Shulman's automatic theorem.  Shulman's
general compatibility criterion sends the problem back to the Iwahori
compatibility question rather than removing it.

## Quantitative audit of Shulman's double (2026-08-08)

This section is deliberately confined to the Kun--Thom free lamp

`H = G *_Γ (Γ × ℤ)`

and does not concern Thom's central free lamp.  It records what Shulman's
proof does and does not provide toward the proposed square-root MF profile.

### The exact rate demanded by Lemma 9

In Shulman's notation, write `X_tilde` for the cut-down lift and put, on the
finite set being amalgamated,

`a = max_i max(||[X_tilde,A_i]||, ||[X_tilde*,A_i]||)`,

`b = max_i max(||[X_tilde X_tilde*,A_i]||,
               ||[X_tilde* X_tilde,A_i]||)`.

For the Halmos unitary

`V = [[X_tilde, sqrt(1-X_tilde X_tilde*)],
      [sqrt(1-X_tilde* X_tilde), -X_tilde*]]`,

Pedersen's inequality gives the explicit estimate

`||[diag(A_i,A_i),V]|| <= a + (5/4) sqrt(b)`.

Consequently, at a selected matrix coordinate of dimension `d`, this step
has the square-root profile only if

`sqrt(d) a -> 0` and `d b -> 0`.

The published proof supplies only qualitative convergence of `a` and `b`.
The quasicentral approximate-unit choice in Lemma 9 gives no coordinate or
rank modulus, the continuous section in Lemma 7 gives no Lipschitz modulus,
and Theorem 4 selects a finite coordinate from strong convergence with no
bound on that coordinate.  In the paper's outer parameter `k`, the displayed
amalgamation error is `1/k`; after choosing an inner coordinate `n_k`, the
desired estimate would require `n_k = o(k^2)` (as well as the analogous
bounds for the other asymptotic-homomorphism defects).  No such estimate is
present in the proof.

This non-extraction is formal, not merely an absence of bookkeeping.  At
the group-C*-algebra level every algebra in this application has the trivial
character.  For each outer index `k`, replace the first `R_k` matrix
coordinates of the lifted maps by the corresponding exact trivial
representation, leaving the tail unchanged.  A finite-prefix change does
not alter the strong limit under `q`; the new prefix has zero multiplicative
and amalgamation defect, so none of the norm estimates worsens; but no
operator-norm separating coordinate can occur before `R_k`.  Since `R_k`
is arbitrary (take, for example, `R_k = k^4`), the proof's stated data are
compatible with arbitrarily bad values of `sqrt(n_k)/k`.  Thus an
`n_k = o(k^2)` conclusion requires genuinely new quantitative structure,
not a different diagonal reading of the published proof.

There is also a harmless constant slip in the displayed proof of Lemma 9:
from `b <= epsilon^2/4`, Pedersen gives `(5/4)sqrt(b) <= 5 epsilon/8`, not
`< epsilon/2` as printed.  Replacing that target by
`b < 4 epsilon^2/25` (or shrinking all preliminary targets once more) repairs
the qualitative theorem.  It does not supply a dimension modulus.

### Finite-quotient profile obstruction

The missing modulus cannot be obtained from the natural residual-finite
specialization of the construction.

**Lemma (Kazhdan square-root barrier for an exact ambient sector).**  Let
`S` be a Kazhdan generating set for `Γ`, with Kazhdan constant `kappa`, and
assume the compressor/infranormal hypotheses under which the already-proved
finite-dimensional `commutant_no_growth` theorem holds.  Let
`π : G -> U(d)` be a genuine representation and `V in U(d)`.  Put

`epsilon = max_{s in S} ||[V,π(s)]||_op`.

For the free-lamp witness

`W = [π(t) V π(t)^*, π(gamma)]_grp`,

one has

`||W-1||_(2,normalized) <= 2 epsilon / kappa`.

Consequently, if `||W-1||_op >= alpha`, then

`epsilon sqrt(d) >= alpha kappa / 2`.

**Proof.**  Apply property (T) to the genuine adjoint representation of
`Γ` on `M_d` with its normalized Hilbert--Schmidt inner product.  Since
operator norm dominates normalized Hilbert--Schmidt norm, there is
`X in π(Γ)'` with `||V-X||_2 <= epsilon/kappa`.  The
finite-dimensional commutant-no-growth theorem says that this commutant is
`π(G)`-invariant.  Hence `π(t)Xπ(t)^*` still commutes with
`π(gamma)`, and

`||W-1||_2
 = ||[π(t)Vπ(t)^*,π(gamma)]||_2
 <= 2 ||V-X||_2
 <= 2 epsilon/kappa`.

On the other hand, for a `d`-dimensional matrix,
`||Y||_2 >= ||Y||_op/sqrt(d)`.  Apply this to `Y=W-1`.  ∎

Thus **no Shulman specialization in which the `G`-sector is represented
exactly** can satisfy `epsilon sqrt(d) -> 0` while keeping the witness
operator-norm visible.  This covers all literal finite-quotient models and
shows that a favorable profile, if it exists, must spend defect inside the
ambient `G`-sector itself; merely adding Shulman's almost-central unitary to
exact residual-finite models cannot work.

There is a quantitative version that identifies exactly how exotic that
ambient defect must be.

**Theorem (square-root profile forces ambient Frobenius instability).**
Let `rho_n` be operator-norm microstates of the Kun--Thom free lamp, of
dimensions `d_n`, with multiplicative defect `eta_n`, and assume the fixed
free-lamp witness has operator-norm separation at least `alpha > 0`.  If

`eta_n sqrt(d_n) -> 0`,

then the restrictions `rho_n|_G`, viewed in the *unnormalized* Frobenius
metric, stay a fixed positive distance from every genuine `d_n`-dimensional
representation of `G` on a fixed finite window.  More precisely, for a
window containing a Kazhdan set of `Γ` and the witness letters, there is
`C = C(kappa,window)` such that for every genuine representation `pi_n`,

`alpha <= C (sqrt(d_n) eta_n
             + max_{g in window} ||rho_n(g)-pi_n(g)||_F)`.

In particular, a square-root-profile realization proves that this explicit
residually finite Kazhdan ambient group `G` is not Frobenius stable.

**Proof.**  Write `V_n` for the lamp.  The relators `[V_n,rho_n(s)] = 1`
for a Kazhdan set `s in S_Γ` hold in unnormalized Frobenius norm up to
`O(sqrt(d_n) eta_n)`.  If `rho_n|_G` is `theta_n`-close in Frobenius norm to
a genuine `pi_n`, then

`max_s ||[V_n,pi_n(s)]||_F
  <= O(sqrt(d_n) eta_n + theta_n)`.

Property (T), applied to the genuine adjoint representation of `pi_n(Γ)`
on the Frobenius Hilbert space `M_{d_n}`, puts `V_n` within
`O((sqrt(d_n) eta_n+theta_n)/kappa)` of `pi_n(Γ)'`.  Exact
finite-dimensional commutant-no-growth makes that commutant invariant under
`pi_n(G)`, so the witness formed with `pi_n` is Frobenius-close to the
identity by the same bound.  Replacing its finitely many `pi_n` letters by
the `rho_n` letters and comparing with `rho_n` of the witness costs only
`O(sqrt(d_n) eta_n+theta_n)`.  Finally, operator norm is bounded by
unnormalized Frobenius norm, so witness separation gives the displayed lower
bound.  ∎

**Conditional corollary.**  If this particular ambient `G` is Frobenius
stable (even only locally on the fixed window above), then Shulman's
symmetric-double approximations cannot have the square-root MF profile.
Conversely, producing the desired profile necessarily produces a concrete
Frobenius-instability sequence for `G`.  Existing Frobenius-stability
theorems for higher-rank semisimple lattices and for 2-Kazhdan groups do not
currently apply to

`EL_r(F_q[x_1^{+-1},...,x_d^{+-1}]) semidirect SL_d(Z)`.

Thus the surviving model-production problem is no longer merely "choose the
Shulman diagonal faster": it is to construct an operator-norm asymptotic
representation of this `G` whose unnormalized-Frobenius defect tends to zero
but which remains Frobenius-far from every genuine representation, while
simultaneously carrying the separating lamp.

The regular finite-quotient subclass satisfies a still stronger logarithmic
barrier:

**Lemma (regular finite-quotient obstruction).**  Let `S` be a fixed finite
symmetric generating set of the Kazhdan group `Γ`.  Suppose `t` compresses
`Γ`, so `t Γ t^-1 <= Γ`, and choose `gamma in Γ` with
`t^-1 gamma t` outside `Γ`.  There is a constant `C_Γ` such that the
following holds.  Let `q : G -> Q` be any finite quotient, let `U` be the
left-regular representation of `Q` (or any multiple of it) on dimension
`d`, and let `V` be a unitary.  Put

`delta = max_{s in S} ||[V,U(q(s))]||`.

If the free-lamp witness remains operator-norm visible,

`||[U(q(t)) V U(q(t))^-1, U(q(gamma))]_grp - 1|| >= alpha`,

then

`delta >= alpha / (C_Γ (1 + log d))`.

In particular, for fixed `alpha > 0`,

`delta sqrt(d) -> infinity`.

**Proof.**  Finiteness upgrades the compressed inclusion to equality:

`q(t) q(Γ) q(t)^-1 = q(Γ)`.

Thus `h = q(t)^-1 q(gamma) q(t)` belongs to `q(Γ)`.  Write `h` as an
`S`-word of length `L`.  Telescoping commutators gives

`||[V,U(h)]|| <= L delta`.

Conjugating the displayed witness by `U(q(t))` shows that its distance from
one is exactly `||[V,U(h)]||`.  Property (T) makes all finite Cayley graphs
`Cay(q(Γ),q(S))` a uniform expander family; the elementary ball-growth
bound for an expander gives

`L <= diam Cay(q(Γ),q(S)) <= C_Γ (1 + log |q(Γ)|)`.

For the regular representation (and its multiples), `|q(Γ)| <= d`.
Combining the inequalities proves the claim.  (If the image of `Γ` is
bounded, the same argument gives a fixed positive lower bound instead.)

For a standard local almost-homomorphism whose pairwise multiplicativity
error is `epsilon`, the relations `zs=sz` give
`||[V,U(q(s))]|| <= 2 epsilon`; evaluating the fixed eight-letter witness
adds only a fixed multiple of `epsilon`.  Hence the same conclusion holds,
up to an inessential constant, with `epsilon` in place of `delta`.

**Consequence.**  Shulman's theorem remains a valid qualitative weak-MF
certificate, but its obvious RF/regular implementation provably has the
wrong quantitative profile: its error is at best logarithmic in dimension,
not `o(d^-1/2)`.  Any square-root-profile realization extracted from
Shulman's abstract proof would therefore have to use genuinely non-liftable
inner coordinates and a new quantitative modulus for both the
quasicentral-unit step and the strong-limit coordinate selection.  Those
data are not consequences of the published construction.

### Final answer for the assigned Shulman-profile audit

There are three logically different conclusions, and they should not be
blurred together.

1. **The primary proof has no extractable dimension/error rate.**  Its two
   continuous-section uses, its quasicentral approximate-unit choice, and
   the final strong-limit coordinate choice are qualitative.  The arbitrary
   finite-prefix delay above proves that no rate can be inferred from those
   data, even after repairing the harmless `5/8` constant slip.
2. **The natural exact-factor realization has the wrong rate.**  Whenever
   the copy of the Kun--Thom ambient group `G` is represented genuinely (in
   particular, by finite quotients), property `(T)` plus finite-dimensional
   commutant no-growth gives `epsilon * sqrt(d) >= c`; for regular quotient
   models the stronger estimate `epsilon >= c/(1+log d)` holds.
3. **An exotic realization is not ruled out, but it would be new
   mathematics not supplied by Shulman.**  The displayed Frobenius
   inequality shows that such a realization must keep the `G`-restriction a
   fixed unnormalized-Frobenius distance from every genuine representation.
   Thus the requested profile is at least as hard as producing an explicit
   Frobenius-instability sequence for
   `EL_r(F_q[x_1^{+-1},...,x_d^{+-1}]) semidirect SL_d(Z)`, coupled to the
   lamp.  No cited stability or instability theorem currently decides this
   group.

This is a negative determination of the *published construction as a source
of the square-root profile*, not a proof that no square-root-profile models
of the free-lamp group exist.

### Frobenius-stability status of the Kun--Thom ambient group (2026-08-08)

Fix

`R = F_q[x_1^{+-1},...,x_d^{+-1}]`,
`N = EL_r(R)`, `Q = SL_d(Z)`, and `G = N semidirect Q`,

with `d >= 4` and `r >= d+3`.  The Laurent ring is noetherian of Krull
dimension `d`.  Weibel, *The K-book*, III.5.5, records that `St_r(R)` is the
universal central extension of `EL_r(R)` for `r>=5` and that
`K_2(r,R)=K_2(R)` for `r>=d+3`; hence
`H_2(EL_r(R),Z)=K_2(R)` in the stated range.  Kun--Thom Theorem E allows
arbitrary `r >= 3`, so choosing this stable-range instance loses nothing for
the existence problem.

**Normalization.**  Here Frobenius norm means the *unnormalized* norm

`||A||_F = Tr(A^* A)^(1/2) = sqrt(matrix_dimension) ||A||_2`.

A finitely generated group `L` is Frobenius stable if every sequence of maps
`phi_n : L -> U(k_n)` satisfying

`||phi_n(x) phi_n(y) - phi_n(xy)||_F -> 0`

for every fixed `x,y` is pointwise Frobenius-close to genuine
homomorphisms `pi_n : L -> U(k_n)`.  This is the normalization in
Bader--Lubotzky--Sauer--Weinberger.  Their cited cohomological criterion is
one-way: `[T_2]`, i.e. `H^1(L,V)=H^2(L,V)=0` for every unitary coefficient
module `V`, implies Frobenius stability.  The disappearance of a scalar
class by itself does not imply stability.

**Theorem (exact LHS reduction).**  For the stable-range Kun--Thom ambient
group above:

1. `H^2(G,C)=0` for trivial complex coefficients.
2. For every unitary `G`-module `V`, put `U=V^N` and
   `W=U^perp`.  Then `H^2(G,U)=0`, and the Lyndon--Hochschild--Serre
   spectral sequence gives a natural isomorphism

   `H^2(G,W) = H^2(N,W)^Q`.

   Consequently

   `H^2(G,V) = H^2(N,(V^N)^perp)^Q`.

3. Since `G` is Kazhdan, it follows that `G` has `[T_2]` exactly when

   `H^2(N,W)^Q = 0`

   for every unitary `G`-module `W` with `W^N=0`.  In particular, property
   `(T_2)` for `N` is a sufficient (strictly stronger) missing theorem.

**Proof.**  The elementary group `N` is perfect.  In the stable range its
Schur multiplier is `K_2(R)`.  Iterating the fundamental theorem for the
regular Laurent ring gives

`K_2(R) = K_2(F_q) + K_1(F_q)^d + K_0(F_q)^(choose(d,2))
         = (F_q^x)^d + Z^(choose(d,2))`.

After tensoring with `C`, the free summand is naturally
`exterior^2 C^d`, generated by the Steinberg symbols `{x_i,x_j}`; monomial
substitution by `Q` is the exterior-square standard action.  Therefore

`H^2(N,C)^Q = Hom_Q(exterior^2 C^d,C) = 0`.

Also `Q=SL_d(Z)` has `[T_2]` for `d>=4`: it is the non-Hermitian real
higher-rank lattice case of Bader--Sauer as used by
Bader--Lubotzky--Sauer--Weinberger.  In the LHS spectral sequence for
`1 -> N -> G -> Q -> 1`, perfectness gives `H^1(N,C)=0`; the only three
total-degree-two terms are consequently zero, proving (1).

For a general unitary `V`, normality of `N` makes `V^N` and its orthogonal
complement `G`-invariant.  On `U=V^N`, the universal-coefficient theorem
and perfectness give

`H^2(N,U) = Hom(K_2(R),U)`.

The torsion summand has no homomorphism to the additive Hilbert space.  A
`Q`-fixed homomorphism on the free summand would give a `Q`-equivariant
linear map `exterior^2 C^d -> U`.  If nonzero, irreducibility and Zariski
density make it injective, and pulling back the Hilbert norm would
unitarize the exterior-square standard representation.  This is impossible:
a nontrivial elementary unipotent has unbounded powers, whereas a unitary
operator does not.  Hence `H^2(N,U)^Q=0`; together with `[T_2]` for `Q`
and `H^1(N,U)=0`, the LHS total-degree-two terms vanish and
`H^2(G,U)=0`.

On `W`, one has `H^0(N,W)=0`.  Property `(T)` of `N` gives
`H^1(N,W)=0`.  Thus the only surviving total-degree-two LHS term is
`E_2^(0,2)=H^2(N,W)^Q`; it has neither a nonzero incoming nor outgoing
differential, proving (2).  Property `(T)` of `G` already supplies degree
one vanishing, giving (3).  ∎

**Exact status and consequence for Shulman's profile.**  The calculation
unconditionally kills the scalar `K_2` obstruction; it does **not** prove
Frobenius stability.  Existing higher-Kazhdan theorems for semisimple
lattices genuinely give `[T_2]` for `Q`, but do not give the required
coefficient-wise invariant vanishing for the universal Laurent elementary
kernel `N`.  The explicit open subproblem left by current theory is:

`For every unitary G-module W with W^N=0, is H^2(N,W)^Q zero?`

An affirmative answer makes `G` Frobenius stable by the cited criterion and,
by the square-root-profile obstruction above, rules out the desired
Shulman profile.  A negative answer only supplies a cohomology class; since
the stability criterion is not an equivalence, it does not by itself
construct Frobenius instability or the free-lamp profile.  Thus current
theory decides neither stability nor instability of this `G`, and this lane
ends at the displayed coefficient-wise problem.

### Why the 2026 strong-MF amalgam theorem does not bypass the obstruction

Gao--Kunnawalkam Elayavalli--Manzoor--Patchell, arXiv:2603.24502, prove that

`G *_H (H x L)`

inherits their strong reduced-norm `MF/PMF/PFF` properties when `H` is
separable in `G` (an intersection of finite-index subgroups), under their
other exactness and residual-finiteness assumptions.  This theorem has
exactly the free-lamp shape, but its separability hypothesis fails for the
Kun--Thom pair for a structural reason.  Infranormality implies that the
image of `Gamma` is normal in every finite quotient of `G`; hence the
relative profinite closure of `Gamma` contains its normal closure.  Since
`Gamma` is not normal, that closure is strictly larger than `Gamma`, so
`Gamma` is not separable in `G`.

The proof of arXiv:2603.24502 makes the failure transparent: it approximates
using finite-index subgroups whose intersection is the amalgam.  For the
Kun--Thom pair their intersection can only reach the larger profinite
closure, so the limit identifies the invisible cosets and kills the
free-lamp commutator witness.  Thus this newer strong-convergence theorem
confirms, rather than removes, the same profinite-absorption obstruction.

### Thom's central quotient is a separate route

For clarity, the preceding conclusions concern only the Kun--Thom free lamp

`G *_Gamma (Gamma x Z)`.

Thom's banked-hyperlinear group is instead de Cornulier's

`K = K_0(Z[1/p]) / Z`,

where `K_0` is the four-block unipotent-by-`SL_3 x SL_3` matrix group and
`Z` is the integral subgroup of its additive centre.  The non-Hopfian map is
induced by the *outer* `GL_1`-scaling of the top-right block, not by an
internal compressor in `K`.  The most obvious Kazhdan subgroup
`K_0(Z)/Z` has algebraic centralizer equal to the surviving central group
`Z[1/p]/Z`, which is normal.  Hence Kun--Thom centralizer normality gives no
contradiction for this subgroup.  Natural Levi subgroups have larger
centralizers, but their compression semigroups do not generate the
unipotent radical.  No direct nonsoficity proof of `K` follows from that
criterion.

There is a general algebraic reason for this failure, with an essential
component-group qualification.  Let an ambient
finitely generated group be Zariski dense in a finite-dimensional algebraic
group `A`, and let `H` be a subgroup.  If `g H g^-1 <= H`, then

`g Zcl(H) g^-1 <= Zcl(H)`.

Dimension alone would not imply equality for disconnected algebraic
groups.  Here conjugacy gives both equal dimension and isomorphic component
groups.  Under the inclusion, the identity components have equal dimension,
so connectedness forces them to agree; the induced injection of the two
finite component groups has equal cardinality and is therefore onto.  The
inclusion is consequently equality.  Thus the compression semigroup of `H` lies in the
normalizer of `Zcl(H)`.  If it generates the ambient group, Zariski density
forces `Zcl(H)` to be normal in `A`.  Consequently its algebraic centralizer
is normal, and

`C_G(H) = G intersection C_A(Zcl(H))`

is normal in `G`.  Hence Kun--Thom centralizer normality is automatically
satisfied for every infranormal subgroup whose behavior is detected by a
finite-dimensional algebraic envelope.  The explicit Kun--Thom Laurent
semidirect products evade this observation because the substitution action
does not admit such a fixed finite-dimensional algebraic envelope.  A
centralizer attack on Thom's `K` would likewise need a genuinely
non-algebraic subgroup; the obvious arithmetic and Levi candidates cannot
work.

---

<!-- ======== formerly BUILD_ITERATION_NOTES.md ======== -->

# Profinite closure LANDED (2026-08-08, final)

`Sofic/ProfiniteClosure` green (3851 jobs, audit 0): `profiniteClosure`,
`normalClosure_le_profiniteClosure` (blindness ⟹ Γ* ⊇ ⟨⟨Γ⟩⟩ under
compressor generation — N18's group half as a theorem), and
`not_mem_profiniteClosure_of_kills` (one finite quotient killing Γ but not
t certifies t ∉ Γ*).  This decides the audited dispute: for KT Theorem-E
pairs the SL_d(ℤ/N)-quotients kill Γ and keep compressors alive, so
compressors ∉ Γ* — the "t ∈ Γ*" step of the external Theorem B is REFUTED
(as the FALSE-side counter-audit claimed and my flag anticipated);
Γ* is confined to the Laurent factor.  Pin note: normalizer at this pin
takes a Set (`Subgroup.normalizer (S : Set G)`, `mem_set_normalizer_iff`).

---

# Free-lamp rigidity LANDED (2026-08-08, latest)

`Sofic/FreeLampRigidity` green (3850 jobs, audit exit 0): N20 kernel-checked
— for infranormal pairs (compressor set S generating G), EVERY
finite-dimensional representation of FreeLamp G Γ K over ANY field by ANY
invertibles kills `lampWitness` (`freeLampRep_kills_witness`), hence H_K has
no faithful f.d. representation (`freeLampRep_not_injective`, not MAP).
Mechanism: `commutantStabilizer` subgroup + `commutant_no_growth` (the
existing co-Hopfian rigidity) + generation.  Gotchas: `set`-vars are OPAQUE
fvars (not let-bindings) — simp only [hρ, hx, MonoidHom.comp_apply] before
any defeq matching; universe: FreeLamp needs G : Type 0; `e⁻¹ = e.symm` in
the automorphism group via `eq_inv_of_mul_eq_one_left` +
`LinearEquiv.mul_eq_trans` + `self_trans_symm`.  Adjudication note: Theorem
B's "t ∈ Γ*" parenthetical is an UNVERIFIED pin (finite-quotient
normalization does not imply t ∈ Γ*); flag before grading B/amalgamated-Popa
[proved].  Preusser 1912.11386 verified from abstract (sandwich over
exchange rings n ≥ 3).

---

# Free-lamp reduction LANDED (2026-08-08, latest)

`Sofic/FreeLampReduction` green (full build 3849 jobs, audit 10030 decls,
rem:freelamp in manuscript).  Formalized: `FreeLamp G Γ K` :=
`PushoutI (lampMap)` over Bool (factors `G`, `↥Γ × K`; base `↥Γ` via
subtype/inl); `inLamp_commute_inAmbient` (base-crossing through
`of_apply_eq_base`); `lampWitness_ne_one` — the four-letter reduced word
`[(1,k), s, (1,k⁻¹), s⁻¹]` through `Reduced.eq_empty_of_mem_range`, needing
only `s = t⁻¹γt ∉ Γ` and `k ≠ 1`; `SoficApproximation.toUniversal` +
`IsMetricallyFaithful` (KT's sofic-representation normalization; survives
null perturbation and restriction; forces injectivity);
`CentralizerNormalization G Γ` = NAMED transcription of KT 2608.06222v1
Thm 4.1 (verified verbatim from source), positive control at Γ = ⊤;
endpoint `freeLamp_not_isSofic`.  So H_K nonsoficity is now a
machine-checked reduction to exactly one cited theorem.

Lean gotchas (new, all instance-transparency): NEVER add a bespoke
`instance : Group (DefWrapper)` over a Mathlib type — make the wrapper an
`abbrev` or every `map_mul`-generated `*` differs from the statement's `*`
by instance constants and `simp only [mul_assoc]` leaves `X = X` open.
Pattern-match instances over `bif`-indexed factor families make
`rw [Prod.inv_mk]`/`map_inv` fail in application position: cross with
`exact`/`congrArg` + `show`-reascription to the Prod-typed statement, never
`rw`.  `decide` rejects goals with free variables (chain conditions on
words: use `.cons_cons (by simp) …`).  `List.IsChain` ctor is `cons_cons`.
Word-letter elaboration (`⟨false, (1,k)⟩`) is expected-type-driven and
consistent across `have`s stated the same way — state letter equations
verbatim and they rw cleanly.

Next candidates: (i) instantiate `CentralizerNormalization` consequences
further (e.g. formalize the H_K ≅ (*_{G/Γ}K) ⋊ G normal form, or the
non-MAP dimension-rigidity argument for H_K — the repo's ExactCompression
co-Hopfian mechanism does the (T)-free part); (ii) EL₄(L) simplicity now
has a verified citation path: Preusser arXiv:1912.11386 (sandwich over
exchange rings, n ≥ 3 — verified from abstract 2026-08-08) + purely
infinite simple ⟹ exchange (Ara–Goodearl–Pardo) + kernel-checked GL₄ = E₄;
formalizing the sandwich over exchange rings is a real but bounded project.

---

# Q3.4 norm–trace session (2026-08-08, later)

LANDED at 068e27e: `Sofic/NormTraceGap` (green, audited, rem:normtrace in
the manuscript).  Domination hsDistSq ≤ ‖·‖_op² via a three-lemma
Euclidean toolkit (only place `EuclideanSpace` appears); `NormModel`
(op-norm unitary models, δ separation / ε multiplicativity) with positive
control `isNormApproximable_of_finite` (regular representation, exact,
entry-separated); bridge `NormModel.toHyperlinearModel` (trace clause =
the entire active hypothesis); corner padding `padMatrix` with
`l2_opNorm_cornerPad` (‖fromBlocks C 0 0 0‖ = ‖C‖, both directions
through `l2_opNorm_le_of_sum_normSq`) and `NormModel.exists_hs_collapse`
(norm data intact, all HS distances < η — weak-MF is trace-blind);
`norm_normTrace_sub_one_le` (vanishing-density diagonal deviation ⟹
trace → 1); `phase_deviation_no_amplification` (i·1: invertible
deviation, |tr| = 1 at every tensor power — deviation RANK is the wrong
amplification invariant; the right one is 1 − |tr|, distance to scalars).
Lean gotchas hit: `Pi.single j (1:ℂ) k` under a FiniteModel carrier
needs the ascription `(Pi.single j (1:ℂ) : Y → ℂ) k`; `positivity`
cannot see `Complex.normSq` (use `Complex.normSq_nonneg` sums) ;
namespace is `Unitary.star_mem`; `pow_le_pow_left₀`; never `rw` a
`set`-abbreviation into Matrix-application position (instances
transparency) — state the entry equation directly and rw the
`permMatrixC_entry Y …` instance into it.

ADJUDICATION (verified from source, arXiv:2608.06222v1 fetched
2026-08-08): Kun–Thom Theorem 4.1 reads "Γ infranormal ≤ G, both Γ and G
Kazhdan; σ : G → S_U ANY sofic representation ⟹ C_{S_U}(σ(Γ)) is
normalized by σ(G)."  It quantifies over all sofic representations of G.
Consequently the free-lamp argument — H_K := G *_Γ (Γ×K) sofic ⟹
restrict ρ to G, ρ(k) centralizes σ(Γ), normalization puts ρ(tkt⁻¹) in
the centralizer, so ρ kills λ := [tkt⁻¹, γ] ≠ 1 (Bass–Serre) — is SOUND
at paper level; the "H_K is not Kazhdan so KT doesn't apply" objection is
wrong (the theorem is applied to G, not H_K).  So modulo KT 4.1 + amalgam
normal form, H_free = F_{G/Γ} ⋊ G is a nonsofic group whose
hyperlinearity ⟺ Connes-embeddability of L(G) *_{L(Γ)} (L(Γ) ⊗̄ L(ℤ)) —
the sharpest known negative-resolution target for Q3.4.

NEXT FORMALIZATION TARGET (feasible now): Mathlib `PushoutI` has
normal-form machinery for amalgamated products.  Formalize (a) the
free-lamp normal form H_K ≅ (*_{G/Γ}K) ⋊ G, or at least λ ≠ 1; (b) the
conditional reduction "KT-4.1-shaped hypothesis (as a named Prop on the
repo's UniversalSofic ultraproduct) ⟹ ¬IsSofic H_K" — all other
ingredients (SoficUltraproduct, exists_soficEmbedding) are already green.
That would be doctrine-compliant (named-hypothesis style, cf.
StuckReduction) and would machine-check the reduction of the new family
to one cited theorem.  NOT to attempt: the Kazhdan-corner theorem
(needs C*_max + Kazhdan projections; its metric hinge is now formalized,
the scaffolding is not), and simplicity of EL₄(L) (sandwich-theorem
scope over general rings unverified; major separate project).

---

# Cluster build iteration — exact pending fixes (2026-08-05)

CURRENT STATE (2026-08-05, later session): **the build is fully green.**
3710/3710 targets, no errors and no warnings under
`-DwarningAsError=true`, and `lake build Audit` is green too.  The
per-module sections below are kept as a record of how each failure was
diagnosed; they are history, not a TODO list.  Two notes for next time:

* Lake is now 5.0.0 and has **no `-j`/`--jobs` flag** — cap the build
  with `taskset -c 0-31 lake build` instead.
* `lake` is not on the default remote PATH; prefix remote commands with
  `export PATH=$HOME/.elan/bin:$PATH`.

## What MSI Agate can and cannot do (measured 2026-08-05)

Agate is RHEL 8.10, kernel `4.18.0-553`, **glibc 2.28**.  Consequences, all
verified rather than guessed:

* **No Lean executable can be built there.**  The toolchain's bundled `clang`
  needs `GLIBC_2.29` and dies with a version error, so any `lake build` that
  reaches a `:c.o` target fails.  Library builds are unaffected because they
  stop at oleans -- which is why the corpus has always built fine and why
  `lean4export` cannot be built there at all.  Anything needing a Lean binary
  has to run on GHA (Ubuntu) or inside a container.
* **No Landlock** (needs kernel >= 5.13), so `landrun` -- and therefore
  `leanprover/comparator`'s sandbox -- cannot run on Agate.  `systemctl --user`
  also has no bus on the compute nodes.
* **Cargo builds need `RUSTFLAGS=` cleared.**  The login profile injects
  `-llapack -lopenblas`, which leaks into *build-script* linking; every crate
  with a build script fails with `unable to find library -lopenblas` before
  any real code compiles.

## Do not try to walk proof terms from a downstream script

In Lean 4.32 an importing module cannot see the proof bodies of imported
theorems: `ConstantInfo.value?` is `none` for them, in the elaboration
environment *and* in `env.setExporting false |>.checked.get`.  Axiom data is
precomputed per-module by `exportedAxiomsExt` when the olean is written, and
`Lean.collectAxioms` reads that table rather than re-walking bodies -- see the
comment in `Lean/Util/CollectAxioms.lean`, "axiom collection never crosses
module boundaries".  So a `lake env lean` script that traverses `value?` is
silently walking *types only* and will report a closure far smaller than the
truth.  Re-checking actual proof terms requires a tool that reads the oleans
directly: `leanchecker` (already in CI) or `lean4export`.

State: MSI auth works (breaker off; pushes via one-off credential helper
pinned to SauersML: `git -c credential.helper= -c credential.helper='!f() {
echo "username=SauersML"; echo "password=$(gh auth token -u SauersML)"; }; f'
push origin main`). Build loop: put changed files with `msi put f
/projects/standard/PROJECT_ACCOUNT/nonsofic_existence/f`, then `lake build`
remotely. 3685/3689 targets green; four modules remain, errors fully
diagnosed from full bodies (task byuok6c6f):

## AlmostMinimalDisplacement
- :32 `Finset.le_sup' _ hg` can't infer f (displacement is semireducible).
  Fix: `by unfold displacement; exact Finset.le_sup' (fun g ↦ ‖ρ g ξ - ξ‖) hg`.
- :74 pin's `add_le_add_right h a : a + b ≤ a + c` (left-add!). Replace with
  `add_le_add (norm_le_displacement ρ Q hQ η hg) le_rfl`.

## HilbertCircumcenter
- :33 `hR ht : t ∈ closedBall x R` vs `dist x t ≤ R`: use
  `Metric.mem_closedBall'.mp (hR ht)`.
- :57 same add_le_add_left convention issue: use
  `add_le_add le_rfl (dist_le_coveringRadius hbdd y hs)`.
- :208 stuck `IsOrderedRing ?m` metavar near `div_le_one (by positivity)`
  in hm2/hn2 region (~line 205-212): add type ascriptions to the casts
  (read the lines first).
- :321 hinv forward branch beta mismatch persists even with `by exact`:
  replace with `refine ⟨g * h, ?_⟩; show φ (g * h) x₀ = φ g (φ h x₀);
  exact (hmul g h x₀).symm`.

## DiagonalClassGroup
- :82/:86: fin_cases mangles Fin literals + decide-proofs (type-incorrect
  under instances transparency). RESTRUCTURE diagUnit_conj_mem's `mem` case:
  prove a single general lemma instead of two special ones:
  `diagUnit_conj_elementaryUnit (u) (i j hij a) : diagUnit u *
   elementaryUnit i j hij a * (diagUnit u)⁻¹ = elementaryUnit i j hij
   (![(u:R),1] i * a * ![((u⁻¹:Rˣ):R),1] j)` proved at val level via
  `!![(u:R),0;0,1] = Matrix.diagonal ![(u:R),1]` (ext, fin_cases, simp) and
  `Matrix.diagonal_mul_single` / `Matrix.single_mul_diagonal`
  (names to verify), D(1+S)D' = DD' + DSD' with DD' = 1.
  Then mem-case: `obtain ⟨i,j,hij,a,rfl⟩ := hz; rw [diagUnit_conj_elementaryUnit];
  exact elementaryUnit_mem _ _ _ _` — no fin_cases at all.
- :121 `No goals`: in stableUnits_normal the `congr 1; exact map_inv ...`
  inside the show-block over-splits. Replace whole rewrite with:
  `have h := map_mul/map_mul/map_inv chain on diagUnitHom` then rw.
- :171 diagPair_mul entries need `simp [Units.val_mul]` (goal
  `↑u * ↑u' = ↑(diagPair (u*u') _) 0 0`).
- Downstream :213/:228/:235/:244/:281/:283/:285 errors were cascades/stale;
  re-check after above.

## UltralimitGeometry
- :422/:430 whnf timeout in bddAbove_orbit_seqNorm even at 1e6 heartbeats:
  whnf unfolds stdPart's `OrderRingHom.comp Classical.ofNonempty` dite.
  Fix: `attribute [irreducible] seqNorm seqNormSq` placed after
  seqNormSq_parallelogram (before Center section), keeping earlier
  unfold-based proofs working (they precede the attribute). If that breaks
  earlier proofs' rw [seqNorm]-style steps, scope it: set it just before
  the Center section. :434 kernel unknown-constant is cascade.

## ShalomFinitePresentation / others
- Not yet re-built after toGroup.of/lift_apply_of fixes; expect new errors
  after deps compile. GaussianPositiveDefinite: header now
  `open scoped Matrix InnerProductSpace Nat` (⟪⟫_ℝ is in InnerProductSpace
  scope, NOT RealInnerProductSpace).

## Rose-K₁ breakthrough (record!)
Unstable descent is now elementary: diag(u,1…1) ∈ E_{2^m}(L) ⟹ via
elementaryBlockGroup_map + prefix-code self-similarity, diag(κ_w(u),1) ∈
E₂(L), and κ_w(u) ≡ u mod H (proved) ⟹ u ∈ H. So H = ker(Lˣ → K₁(L)) and
ScalarReduction ⟸ STABLE K₁(L₂) = 0 (ABC09 at n=1 only). Candidate routes:
BHS-style splitting for the corner-skew Laurent presentation; or graded
triangulation induction on normal-form support through GE₂ over blocks.
Draft the unstable-descent theorem next (all ingredients proved).

## Teammate (tex-align-sweep)
Line-by-line on UltralimitGeometry still queued. All static sweeps clean.

## Rose-K₁ formalization roadmap (from ABC09 full text, user-supplied)
NOT eliminated: the paper's mathematical content. Eliminated: the need for
its full machinery (spectra, homotopy fibrations, Waldhausen NK-vanishing
in all degrees). With the proved unstable descent (H = ker K₁), the target
is STABLE K₁(L₂) = 0 over a field k, degree-1 only. Concrete plan mirroring
ABC09 §4 specialized to the 2-rose (no sinks, no sources, e₀ = 1):
1. L = L₀[t₊,t₋,φ] (corner-skew Laurent; their eq. (skewle), cites
   [skew, Lemma 2.4]); t₊ = a chosen s-generator, φ(x) = t₊ x t₋.
   L₀ = ⋃_n L_{0,n}, L_{0,n} = span{s_α t_β : |α|=|β|=n} ≅ M_{2^n}(k) —
   ultramatricial; repo's leftCombCode/prefix machinery covers this.
2. Twisted Bass–Heller–Swan at K₁ ONLY via Higman-style linearization for
   corner-skew Laurent rings (concrete matrix moves; Yao's proof low-degree
   part). Gives: units of L modulo E generated by units of L₀ modulo the
   relation u ~ φ(u) (plus NK₁-terms).
3. K₁ of ultramatricial-over-field: GL_N(M_{2^n}k) = GL_N·E with
   determinant; K₁(L₀) = colim kˣ — elementary over a field.
4. coker(1−φ) on kˣ = the proved c ≡ c² mechanism (n−1 = 1).
5. NK₁-vanishing for the specific von Neumann regular L₀ (low-degree only —
   NOT Waldhausen's general theorem). Research exact elementary proof.
Their explicit Δ_n/Ω_n transition matrices (proof of thm:skewle) are the
concrete forms to formalize for step 3-4.

## Rose-K₁ status (2026-08-05, after degree-zero milestone)
DONE and green (modules StableUnitsGenerators, FamilyDiagonalClass,
FieldMatrixReduction, LeavittDegreeZero):
- pairKappaUnit: corner insertion along ANY pair t*s = 1, with the
  GL₂-intertwiner coset identity (generalizes word-kappa).
- mem_stableUnits_of_val_unipotent: units 1 + a·b with b·a = 0 are in H.
- centralClassGroup A ≤ Aˣ: units = central·H; ScalarReduction A ⟺ all
  units in it (scalarReduction_of_forall_mem_centralClassGroup).
- CompleteMatrixFamily transvection pullback → H; diagonal-with-central-
  entries pullback → centralClassGroup (Finset-induction corner-sum
  factorization Π κᵢ(dᵢ)).
- unitsEquiv_field_matrix_mem_centralClassGroup: any unit identified by a
  family with a matrix over a FIELD (Mathlib Matrix.Pivot transvection
  decomposition) lies in centralClassGroup.
- fullBinaryCode n (all 2ⁿ words, complete) + entry scalar extraction:
  any unit with value in span{s_α t_β : |α|=|β|=n} is in centralClassGroup
  (mem_centralClassGroup_of_val_mem_levelSpan). With the proved central
  collapse c̄ = c̄² ⇒ c̄ = 1̄, degree-zero units are IN H.

REMAINING (the one frontier): Laurent width-reduction — arbitrary unit of
L₂ ≡ degree-zero unit modulo E-moves. Sharpened plan:
- Grading facts (all trivial identities): t₀^d s₀^d = 1; L_d = L₀·s₀^d for
  d ≥ 0, L_{−d} = t₀^d·L₀; normal form u = Σ_{e>0} t₀^e A_{−e} + A₀ +
  Σ_{d>0} A_d s₀^d, A_i ∈ L₀-span.
- Padding: span{balanced ≤ n} = span{balanced = n} via 1 = Σ_c s_c t_c
  (needed to feed mem_centralClassGroup_of_val_mem_levelSpan).
- Width reduction: E-move [[1,v],[0,1]]·diag(u,1)·[[1,0],[w,1]] =
  [[u+vw, v],[w,1]] with v := −A_N s₀^{N−1}, w := s₀ kills the top
  s₀-degree (and dually t₀ side); iterate at growing matrix size
  (Higman linearization) until all entries degree-zero; then
  fromMatrix(V) is degree-zero (s_γ(balanced)t_δ) → in H; descend via
  the (to-be-generalized to 2^m) mem_stableUnits_of_diagUnit_mem.
- KEY structural fact (why no ℤ-winding survives): L₂ has NO units of
  nonzero pure degree — rank obstruction in L₀ = ⋃ M_{2^m}(k)
  (a·p₀·b = 1 impossible: rank ≤ 2^{m−1}); ker(1−φ₀ on K₀) = 0 in ABC09
  terms. λ(u) = Σ s_b u t_b ≡ u² mod H for EVERY unit (fromMatrix of
  diag(u,u) = κ₀(u)κ₁(u)) — the c ↦ c² mechanism at unit level.

## Laurent endgame analysis (2026-08-05, second session)
Groundwork now green (FamilyDescent, LeavittGradingSpans):
- mem_stableUnits_of_cornerDiag_mem: descent at EVERY matrix size (the
  2^m generalization item is DONE — elementary group pulls back to H
  through any family; single-slot diagonal pulls back to pairKappa).
- levelMonomials_eq (length form), span_levelMonomials_mono (padding),
  monomial_factor_s0/t0 (positive monomial = balanced′·s₀; negative =
  t₀·balanced′), exists_corner_move (the Φ-move: for all v w,
  ∃ unit ≡ u mod H with value s₀(u+vw)t₀ + s₀vt₁ + s₁wt₀ + s₁t₁).
THE WALL, precisely: Φ-move with vw := −(positive part) kills positive
degrees of u but reinjects ONE positive-degree entry (v or w carries
it). This is the K₀-patching obstruction of classical BHS. Two
candidate elementary resolutions, in preference order:
1. Bass XII §7 semisimple-style ending using von Neumann REGULARITY of
   the balanced subalgebra: pseudo-inverses exist concretely — for
   balanced x at depth n, x = Θ(scalar matrix C) and C⁺ from Mathlib
   Pivot decomposition C = E₁DE₂, C⁺ := E₂⁻¹D⁺E₁⁻¹ (D diagonal, D⁺
   entrywise). Use idempotent pivots eB = top coefficient support to
   split the linear matrix and cancel the reinjected entry against the
   t-side. Needs on-paper derivation of the exact induction BEFORE
   coding; do width-1 case by hand first: u = t₀p + a + bs₀ unit.
2. If (1) stalls: no-pure-degree-unit rank argument is formalizable
   NOW: map balanced elements to scalar matrices (entry extraction),
   use Mathlib Matrix.rank + rank_mul_le; p₀^{(d)} has scalar matrix =
   0/1 diagonal of rank 2^{m−d} < 2^m = rank 1. Gives ker-part; the
   coker-part needs the coordinate-free lattice argument (heavier).
Audit note: audit re-run after the six new modules — GREEN, 6680
declarations, closure exactly [propext, Classical.choice, Quot.sound],
ASSUMPTION_INSTANCE still exactly 26.

## Laurent endgame ARCHITECTURE (width-1 hand-derivation, do in order)
Step A (Bass/vN-regular reduction — the remaining hard induction):
  every unit ≡ mod H to (balanced unit)·(code-permutation unit).
  Mechanism found: in the 2×2 picture [[a, −b],[σ, 1]] (reached by the
  proved Φ-composite from u = a + bσ), pivot on the invertible corner
  b̃ : fL₀ ≅ eL₀ of b (e := bb⁺, f := b⁺b, pseudo-inverse b⁺ from the
  Pivot decomposition at the FIXED matrix level M_{2^n}(k) of the
  original representation — all operations stay at level n, and
  rank(f) ≥ 1 strictly decreases per round, so ≤ 2^n pivots terminate.
  The exact op-sequence still needs a symbol-level paper derivation
  (watch: clearing ops reinject σ·(...)·b̃⁻¹ terms — verify the final
  matrix is triangular with UNIT diagonal before coding).
Step B (done): balanced units ∈ H (degree-zero theorem + central
  collapse).
Step C (new discovery — code-permutation units ∈ H, elementary):
  - Equal-length leaf transpositions T(w,w') = s_w t_{w'} + s_{w'} t_w
    + (1 − p_w − p_{w'}) are BALANCED → ∈ H by Step B directly.
  - Unequal-length transpositions: conjugate by a code-unit g with
    |g·w| = |g·w'| (prefix-replacement makes lengths equal); the
    conjugation identity g·T(w,w')·g⁻¹ = T(gw, gw') is a word
    computation; then T(w,w') ∈ H by NORMALITY of stableUnits — no
    abelianness needed.
  - General code-permutation unit = product of transpositions: Higman
    generation for Thompson's V — finite tree combinatorics; OR avoid
    it by making Step A's endpoint transposition-factored directly.
Alternative fallback for C if V-generation is painful: every
code-permutation unit U = U_{C'→leftComb} · U_{leftComb→C}⁻¹; reduce to
V_C := Σ s_{c_i} t_{ℓ_i} vs leftComb by induction on leaf-splitting.

## Step A DERIVATION RESULTS (third session — the state of the math)
1. WIDTH ≥ 2 IS ALREADY REDUCIBLE with the proved exists_corner_move:
   u with degrees in [−M, N], N ≥ 2: factor positive part = b·σ
   (monomial_factor_s0, b degrees [0, N−1]), apply the move with
   (v, w) := (−b, σ): result degrees max(N−1, 1) on top, negatives not
   grown. Mirror: (v, w) := (τ, −c) with negative part = τ·c kills
   bottom to max(−(M−1), −1), top unchanged. So mod H every unit
   reaches degrees ⊆ [−1, 1] — NO new math, just the induction to
   formalize (measure: max monomial |α|−|β| spread of a REPRESENTATION;
   representation-directed, no canonical components needed).
2. THE RESIDUAL CLASS: one more move funnels [−1,1] units to
   R := {units with value c + s₁s₀t₀, c balanced} (fixed universal
   tail β := s₁s₀t₀; note 1 + β ∈ H already: unipotent with A := s₁,
   B := s₀t₀, BA = 0). Remaining gap = R ⊆ H·(balanced units).
3. GRADED INDEPENDENCE IS FORMALIZABLE: weight the existing
   streamFamily (UniversalLeavittOver) over K := RatFunc k with
   s_i ↦ X·prefixOperator, t_i ↦ X⁻¹·deleteOperator (relations still
   hold); a finite sum Σ x_d of pure-degree elements maps to
   Σ X^d·ρ₀(x_d) with ρ₀ the unweighted action, so vanishing forces
   ρ₀(x_d) = 0 by X-transcendence, and ρ₀ is INJECTIVE because L₂ is
   simple (kernel is an ideal; 1 acts as identity ≠ 0 — simplicity is
   already proved: exists_mul_mul_eq_one). Gives canonical degree
   components, componentwise unit equations.
4. R-ENDGAME plan: for u = c + β ∈ R with inverse y = Σ y_d
   (canonical components by 3): top-degree cascade βy_{d*} = 0 forces
   support conditions (βx = 0 ⟹ t₀x = 0 and p₀x = 0 ⟹ x = p₁x);
   combine the cascade with the fixed-level M_{2^m}(k) rank argument
   (scalar-entry extraction + Matrix.rank + rank_mul_le) to force
   y = y₀ + y₋₁-shape and then solve. This replaces K₀-patching by a
   finite matrix-rank computation. Derive fully on paper next turn
   BEFORE coding; then formalize 1 → 3 → 4 in that order.

STATUS UPDATE (fourth session): item 1 IS FORMALIZED AND GREEN —
LeavittWindowReduction (degreeMonomials windows, exists_decomp_top/bot,
wrap_mem_span, corner_terms_mem_span, exists_top_cut/bot_cut,
exists_window_reduction) + BinaryLeavittWindow
(exists_narrow_representative: every unit of L_k(1,2) ≡ mod H to a
[−1,1]-window unit). Audit green at 6731 decls, ratchet still 26.
GRADED INDEPENDENCE (item 3) refined plan for FINITE fields (𝔽₂!):
scaled stream representations ρ_c (s_i ↦ c•P_i, t_i ↦ c⁻¹•D_i) over
K := RatFunc k give ρ_c(x_d) = c^d • ρ_1(x_d) on pure degree d; the
∀c-relation Σ c^d v_d = 0 over the INFINITE field K forces v_d = 0
(coordinate functional via Basis.extend + Polynomial.funext /
eq_zero_of_infinite_isRoot on Kˣ); ρ_1 over L_K faithful by simplicity
(kernel ideal + 1 ↦ id ≠ 0); base change β : L_k → L_K (lift of
family K along Algebra k L_K := RingHom.toAlgebra of composed
algebraMaps) is injective by simplicity of L_k, and maps degree-d
spans to degree-d spans — transports independence back to any k.
Then item 4 (residual class R = {c + s₁s₀t₀}) via componentwise unit
equations.

STATUS (fifth session): GREEN — VandermondeExtraction
(eq_zero_of_forall_units_zpow_smul; pin quirks: Module.Basis namespace
needs `open Module`; linearIndepOn_singleton_iff takes explicit R;
deprecations eval_finsetSum/finsetSum_coeff/Infinite.sdiff; rw of
b i₀ = v d₀ under dependent i₀-type needs congrArg-not-rw) and
GradedIndependence (graded_independence over [Infinite K]; supply
K,V explicitly to the extraction lemma).
REMAINING, in order:
(b) base change: letI : Algebra k (BinaryLeavittAlgebra (RatFunc k))
  := RingHom.toAlgebra ((algebraMap _ _).comp (algebraMap k _));
  β := lift (family (RatFunc k)); β on wordS/wordT by lift_generator
  induction; β injective by exists_mul_mul_eq_one k + Nontrivial;
  β maps degree-d spans into degree-d spans (span_induction; k-smul
  becomes algebraMap k K •[K]); Infinite (RatFunc k) via X-powers or
  Polynomial infinite + IsFractionRing injectivity. Conclusion:
  graded_independence for EVERY field.
(c) residual endgame for u = c + β₀ (β₀ := s₁s₀t₀, c balanced):
  canonical components now available — write u⁻¹'s components, cascade
  from top degree, fixed-level rank argument. Derive on paper first.

## Iteration log (continued)
- GREEN as of this round: DiagonalClassGroup, LeavittDiagonalClass,
  AlmostMinimalDisplacement, UltralimitGeometry, HilbertCircumcenter,
  GaussianPositiveDefinite.
- Root causes found this round (reusable): pin swaps add_le_add_left/right
  argument-side (use add_le_add h le_rfl / le_rfl h); Bracket instance for
  group commutators is SCOPED (open scoped commutatorElement); open scoped
  Nat imports the totient notation clobbering identifier phi; simp needs
  structure-def names (diagUnit, diagPair) to unfold vals; rw with same-term
  pattern consumes all occurrences (drop duplicates); section variables not
  in the STATEMENT are invisible in proofs (include L in); include-in must
  precede docstrings; single_apply_of_row_ne/col_ne have explicit index/value
  args; attribute [irreducible] seqNorm seqNormSq fixed the whnf blowup.
- Still to verify: DelormeFixedPoint, ShalomFinitePresentation, KazhdanCover,
  GLIsElementary, BinaryLeavittDiagonal, DiagonalDescent (first builds).

## Residual-class derivation state (sixth session, in progress)
For u = c + β (β := s₁s₀t₀, c balanced), y := u⁻¹ with canonical
components y_d (graded_independence_all now green):
- β² = 0 (t₀s₁ = 0 inside).
- Component equations: c·y_e + β·y_{e−1} = [e=0] and
  y_e·c + y_{e−1}·β = [e=0].
- Top degree N ≥ 1 (toward contradiction/reduction): β·y_N = 0 and
  y_N·β = 0; β·x = 0 ⟹ t₀x = 0 ∧ p₀x = 0 ∧ x = p₁x (extract via
  t₀t₁·β = t₀); annihilation chain β·y_{e−1} = −c·y_e for 1 ≤ e ≤ N.
- Factorizations: y_e = B_e·s_{0^e} with B_e := y_e·t_{0^e} satisfying
  B_e = B_e·p_{0^e} (right-supported); y_N·s₁·p₀ = 0.
- Next: push the chain into the fixed-level M_{2^m}(k) picture (all
  B_e, c at common depth m) and run the rank bound: B_N = p₁B_N p_{0^N}
  gives rank ≤ 2^{m−N}; combine the uy = 1 degree-0 equation
  c·y₀ + β·y₋₁ = 1 with the chain to force N ≤ 0 dually M ≤ ... then
  the [0,0]-case is a balanced unit (done). Alternative if rank path
  stalls: multiply chain by t₁-extractions to convert into explicit
  matrix equations over k.

## Residual endgame derivation, session 7 — MAJOR simplifications
- The residual tail IS a corner isometry: β = s₁s₀t₀ = s₁·p₀ (since
  s₀t₀ = p₀). So R-units are u = c + s₁p₀, c balanced.
- FREE MOVE FAMILIES (all in H by mem_stableUnits_of_val_unipotent):
  1 + s₁Xt₀ for ALL X (A := s₁X, B := t₀, BA = t₀s₁X = 0); dually
  1 + s₀Xt₁ for all X. Useful products against u:
  (1 + s₁Xt₀)·u = u + s₁·X·(t₀c)   [t₀β = 0]
  u·(1 + s₁Yt₀) = u + (cs₁)·Y·t₀   [p₀s₁ = 0]
  (1 + s₀Xt₁)·u = u + s₀X(t₁c) + s₀X·p₀  [t₁β = p₀]
- KILL CRITERion: u + s₁X t₀c balanced ⟺ X·(t₀c) + s₀t₀ ∈ L₋₁;
  u + cs₁Yt₀ balanced ⟺ (cs₁)·Y + s₁s₀ ∈ L₊₁.
- UNIT RELATIONS (y := u⁻¹, y₀ its balanced component — canonical by
  graded_independence_all): t₀·u = t₀c gives (t₀c)(ys₀) = 1, and the
  degree-0 component gives (t₀c)·z = 1 with z = Zs₀ PURE degree +1,
  hence (p₀c)(Zp₀) = p₀ with Zp₀ BALANCED.  Dually y·u = 1 right-mult
  s₁ gives y(cs₁) = s₁, degree-split y₀(cs₁) = s₁, hence
  p₁(y₀c)p₁ = p₁ with everything balanced.
- So in M_{2^m}(k): (p₀c)·(Zp₀) = p₀ (p₀-corner of c right-invertible
  in the corner) and (p₁y₀)·(cp₁) = p₁ (cp₁ full column rank).
- REMAINING CHIRALITY GAP: the left-move needs X(t₀c) ≈ −s₀t₀ (a
  LEFT-division by t₀c) but unit-ness gives its RIGHT inverse; the
  right-move needs (cs₁)Y ≈ −s₁s₀ (RIGHT division) but we have the
  LEFT inverse.  Next ideas: (i) use BOTH relations simultaneously —
  p₀-corner right-invertible + p₁-column-full may force c's rank
  structure to make one division solvable over M_{2^m}(k) via
  rank(p₀c) = 2^{m−1} ⟹ rowspace(p₀c) is a complement question;
  (ii) exploit that solvability is only needed MOD degree slack;
  (iii) symmetrize with the mirror residual (t-side tail) using the
  swap; (iv) failing exact kill, split c by vN-regular idempotents of
  p₀c and reduce the failure rank inductively (rank strictly drops,
  fixed level m, ≤ 2^m steps).

## Residual endgame, session 8 — unimodular matrix picture (KEY)
For u = c + s₁p₀ (c balanced), U := toMatrix(u) at depth 1 is
  U = [[a, b], [d + s₀, e]],  a := t₀cs₀, b := t₀cs₁, d := t₁cs₀,
  e := t₁cs₁ — ALL BALANCED, single tail entry s₀ at (2,1).
- (R1) ⟹ the ROW (a,b) is right-unimodular OVER THE BALANCED
  SUBALGEBRA: a·z₀ + b·z₁ = 1, z_j := t_jZs₀ balanced.
- (R2) ⟹ the COLUMN (b,e) is left-unimodular balanced:
  w₀·b + w₁·e = 1, w_j := t₁y₀s_j balanced.
- STABLE RANK 1 for L₀ = ⋃M_{2^m}(k) (formalizable, elementary):
  A·Z₀ + B·Z₁ = 1 in M_N(k) ⟹ ∃ T, A + BT invertible.  Proof: pick
  complement K' of ker A, complement W of im A; dim ker A = dim W
  (rank-nullity); im A + im B = k^N ⟹ basis w_i of W with
  w_i ≡ B u_i mod im A; T := (ker A ∋ e_i ↦ u_i, 0 on K');
  A + BT injective ⟹ invertible.  Inverse at the SAME level ⟹
  balanced.  Mathlib: finrank_range_add_finrank_ker,
  Submodule.exists_isCompl.
- PIVOT: col-op c₁ += c₂·t makes â := a + bt balanced-invertible;
  clearing row/col (free E-moves) gives [u] = [ê],
  ê = (e − d̂â⁻¹b) − s₀·(â⁻¹b) = ẽ − s₀g, ẽ,g BALANCED.
  Dually pivot on e via (R2) gives â' = b̃ + h·s₀ shape.
- For ê = ẽ − s₀g: t₁ê = t₁ẽ (t₁s₀ = 0) ⟹ (t₁ẽ)(ê⁻¹s₁) = 1 right-
  invertible; e := ê⁻¹s₁t₁ẽ = ê⁻¹p₁ê (p₁s₀ = 0!) idempotent conjugate
  to p₁; kill-move solvability for the tail ⟺ g·e = g.  Free move
  X := g·(ê⁻¹s₁) adds s₀·g·e EXACTLY, leaving tail −s₀·g(1−e) — but
  e is NOT balanced, so the balanced-shape bookkeeping breaks; the
  swap-conjugate converts s₀g-tails to s₁g'-tails (general residual
  shape u = c + s₁g).
- CHIRALITY WARNING (recurring): unit relations give RIGHT inverses
  where the kill-moves need LEFT division and vice versa.  The sr1
  pivot is the tool that BREAKS the symmetry: it converts
  unimodularity (which we do get from unit-ness) into an honest
  invertible balanced entry.  Next session: iterate the sr1-pivot on
  the [0,1]-shape ê = ẽ − s₀g itself: its depth-1 matrix has row
  (t₀ẽs₀ − gs₀?, ...) — NO: first swap-normalize to s₁-tail
  c' + s₁g', then matrixify: entries t_i(s₁g')s_j = δ_{i1}g's_j not
  balanced unless g' = p₀-shaped.  ALTERNATIVE next attack: use BOTH
  unimodularities at once — 2×2 over balanced with ONE non-balanced
  entry and both a-row and e-column completable: after making â
  invertible AND ê'-column invertible simultaneously (two independent
  sr1 choices), the Whitehead-style factorization of U may land in
  E₂(balanced)·diag(balanced-unit, unit-with-tail-in-p₀-corner) where
  the tail sits INSIDE a corner killed by rank descent at fixed level.

## Session 9: sr1 GREEN + new kappa move families
- StableRankOne.lean GREEN: exists_isUnit_add_comp_of_sup_range
  (End version; injectivity via projections only — no quotients) and
  exists_isUnit_add_mul_of_unimodular (Matrix version via
  Matrix.toLinAlgEquiv'; note: module ToLin, NOT ToLinAlgEquiv, at
  this pin; Submodule.projectionOnto takes p q EXPLICIT before h,
  apply-lemmas take them implicit).
- NEXT BRICK (mechanical, fully specified): transport sr1 to the
  balanced span: Θ := (family).prefixRingEquiv-fromMatrix ∘
  (algebraMap k A).mapMatrix : Matrix ι ι k →+* A is INJECTIVE
  (algebraMap injective entrywise + fromMatrix iso) with range =
  balanced span at depth n (monomials = images of single matrices;
  Θ C ∈ span since scalar•monomial ∈ span).  Transport unimodular
  rows a·z₀ + b·z₁ = 1 to matrices, apply sr1, pull back T and the
  INVERSE (same level ⟹ balanced): yields â := a + b·t balanced
  invertible WITH balanced inverse.
- NEW MOVE FAMILIES (session-9 discovery): for ANY z ∈ L,
  (s₀ + s₁z, t₀) is an isometry pair (t₀s₁ = 0!), giving
  [w] = [κ₀(w) + s₁·z·(w−1)·t₀] for every unit w and every z.
  Dually (s₀, t₀ + z·t₁) gives [w] = [κ₀(w) + s₀·(w−1)·z·t₁].
  These generalize pairKappaUnit beyond word pairs and give
  z-parameterized freedom to reshape residual tails — combine with
  the sr1 pivot loop: after pivot [u] = [ẽ − s₀g] (t₁ẽ right-
  invertible), try the dual pair with z chosen from ê⁻¹-data to
  cancel the reinjected tail.  Watch: κ₀ deepens tails (s₀s₁p₀t₀);
  apply the z-pairs BEFORE funneling, at the [−1,1] stage.

## Session 10: the obstruction is level-invariant — pivot must close it
For general residual u' = c' + s₁g (tail s₁g, g balanced): the kill
succeeds iff rowsp_m(g) ⊆ R := rowsp_m(p₀c') (kill-move changes g by
A·(p₀c'), arbitrary A).  The relation (p₀c')(Z'p₀) = p₀ holds for ALL
residual representatives (t₀ kills any s₁-tail), so rank(p₀c') is
always full (2^{m−1}).  KEY NEGATIVE FINDING: every level-m move is
δ-invariant, where δ := dim((rowsp g + R)/R):
- left family (1+s₁Xt₀): g += A(p₀c') — adds R-rows, δ fixed;
- right family (1+s₁Yt₀): (c', g) ↦ (c'(1+V), g(1+V)) simultaneous
  right-mult by unipotent V = p₁Vp₀-corner — δ fixed;
- block-diagonal balanced units: rowsp-preserving on both — δ fixed.
Hence the closing argument MUST use the depth-changing moves (the
toMatrix 2×2 sr1-pivot), which relate level-m data to level-(m+1)
data.  Plan: track (g, p₀c') through one full pivot+funnel cycle and
exhibit the self-similar rank relation that forces δ = 0 after
enough iterations (the ker(1−φ₀) = 0 mechanism: φ halves ranks, so
an invariant obstruction of positive rank contradicts stability).
z-κ families (session 9) may implement the tracking cleanly.

## Session 10b: the flip loop (derivation nearly complete)
GREEN this session: BalancedStableRank.lean (balancedEmbed n :
M_{2^n}(k) →+* A injective with range = balanced span;
exists_balanced_sr1_pivot: balanced unimodular pair ⟹ balanced t with
a + b·t a unit with balanced inverse).
DERIVATION (general residual u = c + s₀h₀ + s₁h₁, all balanced):
1. Depth-1 matrix: U = C̃ + H·S, C̃ := (t_i c s_j) balanced 2×2,
   H := (h₀,h₁)ᵀ balanced column, S := [s₀,s₁] co-isometry row
   (S·(t₀,t₁)ᵀ = 1, (t₀,t₁)ᵀ·S = I₂).
2. UNIT RELATIONS, degree-0 component of U·toMatrix(y) = I₂ gives
   C̃·V₀ + H·[q₀,q₁] = I₂ with V₀ := (t_i y₀ s_j), q_j := y₋₁·s_j all
   BALANCED — a 2×2 balanced right-unimodularity of (C̃ | H).
3. RECTANGULAR sr1 (generalize exists_isUnit_add_comp_of_sup_range to
   g : V' →ₗ V arbitrary source — same proof) ⟹ ∃ balanced row T
   (1×2): Û := C̃ + H·T invertible with balanced inverse.
4. U = Û + H(S − T) ⟹ [u] = [1 + H·S'] with S' := (S−T)·Û⁻¹ (row).
5. WHITEHEAD FLIP [1 + XY] = [1 + YX] (X := H 2×1, Y := S' 1×2;
   formalizable: diag(1+XY,1) ~E diag(1,1+YX) via 4 explicit
   elementary matrices; the four E-factors have arbitrary-entry
   blocks, all free).  Result: [u] = [σ], σ := 1 + S'·H ∈ Lˣ —
   an ELEMENT again, with σ = (balanced) + S·(Û⁻¹H), i.e. residual
   shape with new tail column H' := Û⁻¹·H.
6. LOOP: u ↦ σ maps tail-data H ↦ Û⁻¹H (balanced-invertible times H)
   plus re-extraction.  This move is NOT level-m-invariant (it uses
   depth) — the δ-invariance obstruction of session 10 does not
   apply.  REMAINING: find the terminating measure for the loop
   (candidates: the balanced ideal generated by entries of H against
   the corner filtration; or show one flip with OPTIMAL T from the
   sr1-freedom already lands h' with rowsp(h') ⊆ rowsp(p₀c')-solvable;
   or two flips compose to a level-m-solvable kill).
FORMALIZATION order once termination nailed: rectangular sr1 →
2×2-unimodularity extraction (needs component-calculus for toMatrix
of products — straightforward with graded independence) → Whitehead
flip → the loop.

## Session 11: element-level identification + level bookkeeping
- The "2×2 balanced unimodularity" IS the degree-0 component of
  u·y = 1 directly: for u = c + h (h := degree-1 part, h = s₀h₀+s₁h₁):
  c·y₀ + h·y₋₁ = 1, with h·y₋₁ balanced.  No matrix detour needed for
  the STATEMENT; the matrix picture is needed to APPLY sr1 (the
  pivot-parameter t ranges over window[−1,−1], and {h·t} corresponds
  to the rectangular block family B·T via the block dictionary:
  t_i(h·t)s_j = h_i·(t·s_j), t ↔ (ts₀, ts₁) bijective).
- RECTANGULAR sr1 (g : W →ₗ V arbitrary fin-dim source) — same proof
  as exists_isUnit_add_comp_of_sup_range verbatim; gives the ELEMENT
  pivot: ∃ t ∈ window[−1,−1]-span, û := c + h·t unit with balanced
  inverse [via block dictionary + level-m matrices].
- FLIP STEP: u = û + h(1−t): [u] = [1 + û⁻¹h(1−t)] = (flip, GREEN) =
  [1 + (1−t)û⁻¹h] = [c' + h'] with c' := 1 − tû⁻¹h balanced and
  h' := û⁻¹h — one full round, all pieces formalizable NOW.
- LEVEL BOOKKEEPING (important correction): the round maps the level
  pair (level c, level H) as (m, low-canonical) → then the C̃-level
  drops by one per round but the H-level FOLLOWS one behind and the
  pair PLATEAUS around (m−2, m−1).  The naive level-induction does
  NOT terminate by itself.
- BASE-CASE INSIGHT (works, formalizable): scalar-coefficient
  residuals γ + λ₀s₀ + λ₁s₁ (γ, λᵢ ∈ k, some λᵢ ≠ 0) are NEVER units:
  the stream representation image γ + Σλᵢ·prefixOperator is not
  surjective (the recursion f(w) = γ⁻¹(g(w) − λ_{w₀}f(tail w)) cannot
  terminate on constant streams; concrete non-preimage witness
  exists).  So IF the loop reaches scalar level, tails must vanish
  and u ≡ central ∈ H.
- REMAINING GAP (the one unknown): the plateau — show the loop
  composed with level-m moves strictly reduces a finite measure at
  the plateau level (candidates: rank of the kill-obstruction of H
  against rowsp(p₀c'); the affine self-map H ↦ Û(H)⁻¹H analyzed as
  the ABC09 transition action, ker(1−φ₀) = 0 realized as eventual
  solvability).  Alternatively strengthen the non-unit argument:
  characterize which (c, h) at the plateau admit units and show the
  kill is always solvable there.

## Session 12: corner-support discovery (sharpest lead for the finish)
Run one flip-round on the CANONICAL residual u = c + s₁p₀ with pivot
û := c + s₁p₀t.  Then the new balanced part is c' = 1 − w·p₀ with
w := tû⁻¹s₁p₀ (RIGHT-SUPPORTED: w = wp₀), and consequently:
- p₀c' = p₀(1−w)p₀ is CORNER-SUPPORTED (p₀c'p₁ = 0 since wp₀p₁ = 0);
- if the corner element p₀ − p₀wp₀ is invertible INSIDE the corner
  p₀Mp₀, then rowsp(p₀c') = rowsp(p₀) — the FULL half-coordinate
  row space;
- the new tails h'ᵢ = tᵢ(û⁻¹s₁p₀) are right-supported on p₀, and
  x = x·p₀ ⟹ rowsp(x) ⊆ rowsp(p₀).  KILL-CONDITION SATISFIED
  rowsp(tail) ⊆ rowsp(p₀c') whenever the corner-invertibility holds!
So the endgame reduces to TWO finite sub-steps at the plateau level:
(a) handle the h₀'-component (either choose t with t₀û⁻¹s₁ = 0 to
    make h₀' = 0, or solve the augmented system A·[p₀c' | s₀h₀'] =
    [−h₁' | 0] — the junk-vanishing condition As₀h₀' = 0 is finitely
    many balanced equations);
(b) show t can be chosen with BOTH û invertible AND p₀ − p₀wp₀
    corner-invertible (another sr1-flavored freedom argument: the
    corner condition is again a unimodularity statement in the corner
    algebra ≅ level-(m−1); candidate: derive corner-unimodularity of
    p₀(1−w)p₀ from û-invertibility + the p₀-corner of û⁻¹-relations).
If (a)+(b) close, the FULL CHAIN is: width-reduction (green) →
funnel to canonical (green machinery) → one flip-round (flip green,
element-pivot needs the block dictionary) → kill (green move
families) → balanced → H (green).  ScalarReduction follows; B4, B5,
B6 and Theorem C assemble; the manuscript is complete.

## Session 13: normal-form loop in closed form + the flag condition
GREEN: ResidualNormalForm.lean (exists_prefix_kill: z free mod L·t₀;
exists_corner_transport: [1+s₁βt₁] = [1+β] with corner inverse
t₁u⁻¹s₁, x = 1 − βx two-sided trick).
DERIVATION HARVEST:
- Normal form: every residual class = [1 + s₁z], z ∈ window[−1,0].
- THE LOOP in closed form: z ↦ û_L⁻¹(1−t_L)z₀ (left-sr1 pivot û_L,
  balanced part transforms z₀ ↦ û_L⁻¹z₀).  All level-preserving moves
  leave rank(z₀·p₁ mod L₀p₀) invariant — the kill succeeds iff
  z₀p₁ ≡ 0 mod the free ideal, i.e. iff p₀û_L⁻¹p₁ = 0 for the
  canonical-converted form.
- BLOCK-FLAG ANALYSIS: p₀M⁻¹p₁ = 0 ⟺ M(p₁V) = p₁V ⟺ colsp(cp₁) =
  p₁-coordinate half (M := û_L has Mp₁ = cp₁).  (R2) gives cp₁ full
  column rank; block-diagonal balanced conjugation can rotate
  colsp(cp₁) onto p₁V iff colsp(cp₁) ∩ p₀V = 0 ⟺ corner block
  c₁₁ = p₁cp₁ injective.  So the remaining question is now:
  (*) can the pre-moves always achieve c₁₁ invertible (or dually
  colsp(cp₁) transverse to p₀V)?  Candidates: sr1 inside the corner
  (c₁₁ + correction·(stuff) invertible via corner-unimodularity from
  (R2): p₁y₀·cp₁ = p₁ IS corner-left-unimodularity of (c₀₁-stack) —
  transversality via one more sr1-pivot with the s₁p₀-tail as the
  perturbation: u ↦ u(1 + s₁Y t₀)-moves change cp₁?? (they change
  c-columns only in p₀?): check which moves move colsp(cp₁).
- Non-units found: 1 + s₀ (stream surjectivity), 1 + s₁s₀t₁ (flip to
  1 + s₀).  Unit-ness genuinely constrains z₀.

## Session 14: THE ENDGAME MATHEMATICS IS COMPLETE (verify then batch-write)
For canonical residual u = c + s₁w (c, w balanced, p := p₀):
KILL-SEQUENCE (all moves already-green families; four steps):
0. NORMALIZE (right-mult by balanced unit h): make p·c·p' = 0 with
   p-corner pcp invertible.  Possible since rank(pc) = half (R1);
   column-reduce: ∃h invertible: (pc)h = [block | 0]  [F3-lemma].
   After this: kill-condition ⟺ w·p' = 0; kill-ideal = {X : X = Xp}
   (the move w += A(pc) reaches ALL of Mp since pcp invertible).
1. ROW-MIX (left-mult by block-diagonal balanced unit g = g₀⊕g₁,
   preserves pcp' = 0): tail w ↦ g₁'w.  Choose g₁' invertible so the
   p-rows of the new ω := wp' span rowsp(ω) — always possible since
   rank(ω) ≤ #columns(ω) = half ≤ #p-rows  [F1-lemma].
   Result: rowsp(p'ω) ⊆ rowsp(pω), i.e. ∃N: p'ω = −N(pω)  [F2-lemma:
   solvability of N·M = B from row-space containment].
2. SET wp (free via kill-moves): pwp := 0, p'wp := N from step 1.
3. TWIST (right-mult by the free unipotent 1 + s₀Yt₁ realizing
   V' := −pω, a p-row/p'-col corner): (c, w) ↦ (c(1+V'), w + V').
   The kill equation w_new = A·(p c_new) with c_new = c(1+V') splits
   into: p-cols: Ap := wp (free ✓); p'-cols: ω + V' = (wp)·V' —
   p-rows: (1 − pwp)V' = −pω: holds by V' := −pω, pwp = 0 ✓;
   p'-rows: p'ω = (p'wp)(−pω) = −N(pω)·(−1)-sign-check: holds by
   step 1-2 choice of N ✓.
4. KILL: A(p c_new) = −w_new solvable ⟹ tail dead ⟹ u ≡ balanced
   ⟹ ∈ H (balanced units green).  ScalarReduction FOLLOWS.
SUPPORT LEMMAS TO FORMALIZE (all finite linear algebra over k):
F1: ∀ω (n×half): ∃G invertible: bottom-rows(Gω) ∈ rowspan(top-rows).
F2: rowsp(B) ⊆ rowsp(M) → ∃N: N·M = B (Basis.constr lift, transpose).
F3: rank(M) = #rows → ∃H invertible: M·H = [M' | 0], M' invertible
    (column reduction).
MOVE-LEMMAS (element-level val-computations, all in green families):
- right-mult h: (c, w) ↦ (ch, wh); left block-diag g: (gc, g₁'w) with
  g₁' := t₁gs₁; kill-family: w += A(pc) via (1 + s₁(As₀)t₀);
  V'-twist via (1 + s₀Yt₁) with s₀Yt₁-image = V' = pV'p':
  (c, w) ↦ (c + cV', w + V').  [each: verify val-identity + junk-free]
ENTRY: width-reduction (green) → [−1,1] → funnel (exists_corner_move
with (v,w) = (−b, s₀)) → canonical c + s₁p₀.  EXIT: balanced → H.
SIGN/BLOCK details need re-verification during formalization — the
derivation was single-pass; treat each block identity as to-check.
Then: ScalarReduction (BinaryLeavittAlgebra k) unconditional →
upgrade BinaryLeavittDiagonal (drop hscalar) → B4/B5/B6 → final
manuscript assembly.  BATCH-WRITE ALL OF THIS NEXT (user directive:
write fully, then debug).

## Session 15 (continuous run): corrected moves + the DEEP kill module
- CORRECTION: right-mult by 1 + s₀Yt₁ acts as (c,w) ↦ (c(1+V), w(1+V))
  — session-14's kill-sequence step 3 was invalid.  Move algebra:
  (ch, wh) / (gc, g₁w) / (c, w + A·p₀c).  ResidualMoves.lean WRITTEN
  (blockDiagUnit, blockDiagUnit_mul_residual, kill_move_residual,
  kill_mover_mem) — not yet compiled (continuous-run mode).
- z₋ = 0 CLASSIFICATION: 1 + s₁z₀ (z₀ balanced) is a unit ⟺ s₁z₀ is
  nilpotent (geometric series is forced finite; negative components
  of the inverse vanish by downward recursion).
- COUNTEREXAMPLE to depth-1 kill-sufficiency: u = 1 + s₁s₀₀t₁₁ is a
  unit ((s₁s₀₀t₁₁)² = 0 via t₁₁s₁ = t₁, t₁s₀ = 0) with z₀ = s₀₀t₁₁,
  z₀p₁ = z₀ ≠ 0.  It IS trivially in H (unipotent a := s₁s₀₀,
  b := t₁₁, ba = 0).  Hence δ := rank(z₀p₁) is NOT class-invariant:
  the moves enumerated so far miss the DEEP families.
- THE DEEP KILL MODULE: movers 1 + s_{1α'}·X·t_{0β''} (incomparable,
  |α'| = |β''| for balance) change the tail by s_{α'}·A·(t_{0β''}c)
  with NO junk (t_{0β''}s₁ = 0).  K_c := span of all such changes ⊇
  old kill-ideal (α' = β'' = ∅ gives A·p₀c).  For c = 1 the module
  contains all s_{α'}At_{β''}-balanced elements — kills the
  counterexample (X := 1, α' = 00, β'' = 11).  CONJECTURE (final
  form): u = c + s₁w unit ⟹ w ∈ K_c.  Deep-matrix heuristic:
  K_c-membership ⟺ rowsp_deep(w) ⊆ rowsp of the deep matrices of
  t₀c; (t₀c)(ys₀) = 1 gives t₀c full row rank at EVERY depth.
  Remaining: prove the conjecture (candidates: induction on depth of
  w's representation using the full-row-rank at matching depth;
  or the z₋ = 0-classification generalized: reduce to nilpotent case
  by the loop, then nilpotent tails are killable via their explicit
  finite inverse).  NOTE the nilpotent-route: if z₋ = 0 then
  u = 1 + s₁z₀ with s₁z₀ nilpotent — u·(1 − s₁z₀ + (s₁z₀)² − …) = 1
  — and each partial product mover 1 + (finite sum) may itself be an
  H-member via iterated unipotent/flip decompositions of nilpotents:
  CHECK: is every unit of the form 1 + n (n nilpotent, n ∈ s₁·L₀!)
  in H?  1 + n with n^D = 0: 1 + n = Π-telescoping?  For n = s₁z₀:
  [1 + s₁z₀] = flip = [1 + z₀s₁] with (z₀s₁) nilpotent balanced-shifted
  … z₀s₁ pure degree +1 nilpotent ⟹ 1 + z₀s₁: window [0,1] with
  NILPOTENT tail: try induction on nilpotency degree D via the flip:
  each flip conjugates/shortens?  (s₁z₀)² = 0-case: 1 + s₁z₀ IS
  unipotent-lemma-able?? a := s₁z₀, b := 1: ba ≠ 0.  a := s₁, b := z₀:
  ba = z₀s₁ ≠ 0 but NILPOTENT — generalize mem_stableUnits_of_val_
  unipotent from ba = 0 to ba NILPOTENT: diag(1+ab, 1) vs 1+ba:
  Whitehead flip gives [1+ab] = [1+ba]; induct on nilpotency index:
  [1 + ba] with (ba)^{D−1}... (ab)^k-relations: THE FLIP REDUCES
  NILPOTENCY INDEX?? (1+ab)(1+ba): if (ab)² = 0 then 1+ab = unit and
  [1+ab] = [1+ba] with (ba)³ = b(ab)²a·… = 0-index-shifts by one!
  (ba)^{k+1} = b(ab)^k a: (ab)^D = 0 ⟹ (ba)^{D+1} = 0 — WRONG
  DIRECTION (index grows).  Decompose instead: 1 + n, n^D = 0:
  n = n', use 1 + n = (1 + n·e₁)(1 + n·e₂)···-idempotent-splittings?
  OVER A FIELD: nilpotent balanced-level N: 1 + N = product of
  ELEMENTARY transvections in M_{2^m}(k)!!  — 1 + N is UNIPOTENT
  matrix ⟹ ∈ E_{2^m}(k) ⟹ its image is in H by the
  field-matrix-reduction (unitsEquiv_field_matrix... centralClass)!!
  But s₁z₀ is NOT balanced (degree 1) ✗.  HOWEVER: 1 + s₁z₀ with
  (s₁z₀)^D = 0: pure-degree-1 nilpotent: at depth-D-matrix picture
  toMatrix_D(1 + s₁z₀) = I + (strictly-lower-triangular-by-degree
  block structure)?? — degree-+1 elements SHIFT the grading-blocks:
  the depth-j matrix of a degree-1 element has a SHIFT-structure ⟹
  1 + (degree-1-nilpotent) is I + (block-shift-nilpotent-matrix) ⟹
  UNIPOTENT MATRIX over the deep level ⟹ product of elementary
  transvections OVER THE BALANCED-DEEP-RING (not field — entries are
  L-elements... at depth D the entries of s₁z₀'s matrix: t_γ(s₁z₀)s_δ
  — NOT scalar).  Hmm.  Simplest honest: prove
  mem_stableUnits_of_val_unipotent' for n with n² = 0 directly:
  1 + n, n² = 0: diag(1+n, 1): [[1,n],[0,1]]·[[1,0],[?,1]]-…:
  1 + n = (1+n)·1: E₂-identity: [[1+n, 0],[0, (1+n)⁻¹-wait use
  diagPair_inv_self + flip with x := n, y := 1?? flip x=n,y=1:
  [1+n·1] = [1+1·n] trivial.  x := 1+?, …  DIRECT: n² = 0:
  1 + n unit with inverse 1 − n: is diag(1+n,1) ∈ E₂?
  [[1,n],[0,1]]·[[1,0],[-n?,1]]… compute [[1,n],[0,1]][[1,0],[y,1]]
  = [[1+ny, n],[y,1]]: want [[1+n,0],[0,1]]: ny = n: y := 1?? then
  [[1+n, n],[1, 1]]-no.  Known fact: 1+n (n²=0) IS a product of two
  of OUR unipotents?  n = n·1: n² = 0 ⟹ 1+n = (1 + a b) with
  a := n, b := 1 − n/2?? char-2-issues.  In fact for n² = 0:
  1 + n = (1 + n)·— just use the FLIP-form: n = s₁z₀ = a·b with
  a := s₁, b := z₀: [1 + s₁z₀] = [1 + z₀s₁] (flip ✓ green!) and
  z₀s₁: DEGREE +1 with (z₀s₁)² = z₀(s₁z₀)s₁: (s₁z₀)² = 0 ⟹
  (z₀s₁)³ = z₀(s₁z₀)²s₁ = 0: index ≤ 3… circles.  NEXT SESSION:
  settle "1 + nilpotent-in-tail ∈ H" cleanly, then reduce general
  residuals to the nilpotent case via the z₋-elimination (the
  y-negative-component recursion suggests: LOOP kills z₋?).

## Session 15b (continuous run): square-zero tails DIE + written modules
NEW MATH (verified on paper twice):
- z₋ = 0 classification: 1 + s₁z₀ (z₀ balanced) unit ⟺ s₁z₀ nilpotent.
- SQUARE-ZERO KILL: (s₁z)² = 0, z balanced ⟹ 1 + s₁z ∈ H via
  pseudo-inverse: a := s₁z, b := ξz (zξz = z): ab = s₁z, ba = ξ(zs₁z)
  = 0 since zs₁z = 0 by s₁-left-cancellation.  Uses vN-regularity of
  balanced elements (matrix generalized inverse via Pivot
  diagonalization: C = PDQ, C⁺ = Q⁻¹D⁺P⁻¹).
- z₋-elimination observation: in the loop, if 1 + z₋s₁ is invertible
  take t := 0: z ↦ (1+z₋s₁)⁻¹z₀ is PURE balanced-part — z₋ gone.
WRITTEN THIS RUN (uncompiled): ResidualMoves.lean,
ResidualReduction.lean (NarrowReduction hypothesis + full chain to
ScalarReduction/B4/GL₂/GL₄), BalancedRegularity.lean
(exists_pseudoInverse_matrix [name-risk: Matrix.Pivot or
TransvectionStruct namespace for prod_mul_reverse_inv_prod],
exists_balanced_pseudoInverse, square_zero_tail_mem_stableUnits).
REMAINING MATH for NarrowReduction: (i) general nilpotency index D
(flag/filtration splitting compatible with the ψ(e) := t₁es₁ twist,
or dyadic induction — index-2 case DONE); (ii) z₋-elimination in the
non-invertible case (sr1-t reinjects −û⁻¹tz₀; check whether the
REACHED form after one loop always has invertible 1 + z₋'s₁ — the
new z₋' = −û⁻¹tz₀ with t from sr1: is 1 − û⁻¹tz₀s₁ unit?
û = 1 + z₋s₁ + tz₀s₁ ⟹ û − tz₀s₁ = 1 + z₋s₁: 1 − û⁻¹tz₀s₁ =
û⁻¹(û − tz₀s₁) = û⁻¹(1 + z₋s₁) — PRODUCT OF INVERTIBLE-IFF:
1 − z₋'s₁-NEW-c₂' = û⁻¹(1 + z₋s₁)?!?! CHECK THIS: c₂' := 1 + z^new₋s₁
= 1 − û⁻¹tz₀s₁ = û⁻¹(û − tz₀s₁) = û⁻¹(1 + z₋s₁): INVERTIBLE ⟺
1 + z₋s₁ invertible.  So: if 1 + z₋s₁ invertible: eliminate now;
else c₂' is NON-invertible again — the invertibility of 1 + z₋s₁ is
loop-INVARIANT?!  New attack for (ii): 1 + z₋s₁ non-invertible:
z₋s₁ balanced: use IT as data — u = 1 + s₁z: FLIP: [1+s₁z] =
[1+zs₁] = [(1 + z₋s₁) + z₀s₁] — the balanced part of the flipped
form IS 1 + z₋s₁: run sr1 on the OTHER side/dual pivot, or note
(1+zs₁)-unit with balanced-part-singular still fine — kill z₀s₁-part
against it...  CONTINUE HERE NEXT MATH TURN.

## Session 15c: the γ-invariant — NarrowReduction reduces to TWO lemmas
Define γ(1 + s₁z) := 1 + z₋s₁ (balanced).  Facts derived:
- γ is MULTIPLICATIVE on [−1,0]-form products:
  γ((1+s₁a)(1+s₁b)) = γ(a-form)·γ(b-form)  [only (−1,−1) hits deg −1].
- γ is INVARIANT under both free families (t₀s₁ = 0 protects it) and
  transforms by left-mult under the loop (c₂' = û⁻¹(1 + z₋s₁)) and by
  conjugation under block-diagonal moves — its (non)invertibility is
  an invariant of all known moves.
- If γ invertible: flip + absorb: [1+s₁z] = [1+zs₁] = [γ]·[1+γ⁻¹z₀s₁]
  = [1 + s₁γ⁻¹-moved z₀-pure form] ⟹ z₋ = 0 case ⟹ tail NILPOTENT
  (classification) ⟹ kill by (i).
NARROWREDUCTION ⟸ (G) + (i):
(G): u = 1 + s₁z unit ⟹ γ = 1 + z₋s₁ invertible in the balanced
  algebra.  [Test-verified on κ₁-images (⟺ unit-condition), free
  movers (γ = 1), products (multiplicativity).  Attack: the
  (XX_d)-system (1+s₁z₋)y_d = [d=0] − s₁z₀y_{d−1} plus py_d-facts
  downward induction; or stream-representation invertibility
  restricted to a γ-detecting subspace.]
(i): 1 + s₁z₀ with (s₁z₀)^D = 0 ⟹ ∈ H.  Index 2 PROVED
  (square_zero_tail_mem_stableUnits, written).  General D: filtration
  splitting compatible with ψ(e) = t₁es₁, or dyadic induction via
  [1+n]² = [1+n²]-char-2-plus-odd-part, or flag idempotents from
  vN-regularity of the P_k := (z₀s₁)^k z₀ kernel chain.
Also: entry into 1+s₁z-form from the [−1,1]-window: [window-unit] =
[c + s₁w-funnel-output] — then LEFT-round (sr1-pivot) gives the
1 + s₁z-form; both formalizable with existing machinery (sr1 needs
the element-level block dictionary — the remaining nontrivial
formalization plumbing).

## Session 15d: exact p-split; (i) reduced to p'-supported tails
- EXACT IDENTITY: (1 + s₁z₀p₀)(1 + s₁z₀p₁) = 1 + s₁z₀ (cross term has
  p₀s₁ = 0).  First factor has square-zero tail ((s₁z₀p₀)² = 0 same
  way) ⟹ in H by square_zero_tail_mem_stableUnits.  So
  [1 + s₁z₀] = [1 + s₁(z₀p₁)] ALWAYS — tails reduce to p₁-supported.
- p₁-supported tail: s₁(z₀s₁t₁)·— κ₁-sandwich: 1 + s₁(z₀s₁)t₁ =
  κ₁(1 + z₀s₁) ⟹ corner transport (green) gives [1+s₁z₀] = [1+z₀s₁]
  — an independent derivation of the flip for these shapes, with all
  factors explicit.
- Twisted-product criterion: n = s₁z₀ nilpotent of index D ⟺
  Q_{D−1} := z₀·φ(z₀)·…·φ^{D−1}(z₀) = 0 where φ(x) := s₁xt₁
  (multiplicative!).  Flag-splitting attempts (support idempotents
  σ_k): D = 2, 3 terminate; D ≥ 4 the junk factors block clean
  telescoping — needs the fixed-point support construction or another
  route.  Deep-matrix triangularity fails (degree persists).
- STATE: (i) index-2 proved; index-general open but tails now
  p₁-supported WLOG (formalizable now); (G) open with the
  (XX_d)-system attack.  These two remain the entire mathematical gap
  for NarrowReduction ⟹ ScalarReduction ⟹ manuscript completion.

## Session 16: (i') reformulation, vacuous-split traps, W-induction base
- (i) ⟺ (i'): units 1 + ζ with ζ pure degree +1; unit-ness FORCES ζ
  nilpotent automatically (downward recursion kills negative inverse
  components, x_d = (−ζ)^d, finiteness ⟹ nilpotency).  So (i') is:
  1 + ζ, ζ ∈ L₁ nilpotent ⟹ ∈ H.
- σ-form criterion: ζ = Bσ, ζ^D = R_{D−1}σ^D with
  R_j := B·φ₀(B)···φ₀^j(B), φ₀(x) := s₀xt₀; nilpotency ⟺
  R_{D−1}·p_{0^D} = 0 (NOT R = 0 — σ not right-injective).
- VACUOUS-SPLIT TRAPS (documented so they're not retried): for
  Bσ-forms, right-support splits of B are vacuous (pσ = σ, p'σ = 0);
  for Cs₁-forms, left-p-splits vacuous (p's₁ = s₁, ps₁ = 0);
  left-support splits vacuous by definition of support.  The ONE real
  split is the proved s₁z-form/right-support: [1+s₁z] = [1+s₁zp₁].
- Width-of-inverse induction: base W = 0 works (y balanced-valued
  unit ⟹ y ∈ centralClass green ⟹ [u] = [y]⁻¹ trivial).  But width
  is invariant under balanced multipliers and degree-(±1) H-movers
  miss the top component — the step needs the same missing mechanism.
- char-2 shortcut evaluated and rejected: (1+n)² = 1+n² gives only
  2-torsion, not triviality.
NEXT: (G) via the (XX_d) system remains the most structured target;
for (i') the twisted-flag fixed-point construction (session 15d) with
the ψ-compatible idempotents is the open front.  Also consider:
represent 1 + ζ at depth D (index): entries of toMatrix_D(ζ) vanish
except γ-starting-1-blocks with SHORTER words — check whether ζ^D = 0
forces a STRICT block-triangular structure at depth D against the
cylinder flag {p_{1^k0...}} — the cylinder flag is the natural
φ-compatible flag and may make every nilpotent tail literally
strictly triangular w.r.t. a balanced idempotent chain, giving the
telescoping product decomposition into square-zero pieces with the
ordered cross-conditions holding by flag-position.

## Session 17: TailSupportReduction written + (G)-unimodularity extracted
WRITTEN (uncompiled): TailSupportReduction.lean — mul_p0_mem_span /
mul_p1_mem_span (right multiplication by corner projections selects
monomials by first t-letter, staying in the balanced span at depth
n+1), and exists_tail_support_reduction: the exact p-split
[1 + s₁z] = [1 + s₁(z·p₁)] with the explicit square-zero left mover
1 − s₁(zp₀) ∈ H.
(G)-DERIVATION ADVANCE (from the (V_d) bottom cascade of the flipped
form v = γ + z₀s₁, x := v⁻¹):
- L_{−M} elements expand as Σ (x s_w) t_w with BALANCED coefficients;
  {t_w}-independence (right-multiply by s_w) extracts balanced
  equations from every graded component.
- The degree-0 equation yields the UNIMODULARITY
  γ·x₀ + (z₀p₁)·Y = 1 with Y := s₁(x₋₁s₀)t₀ + s₁(x₋₁s₁)t₁ balanced
  (every p₁-row-supported balanced Y arises as s₁(t₁Y s₀)t₀ +
  s₁(t₁Y s₁)t₁).
- Rectangular sr1 (green) ⟹ ∃T balanced: û := γ + (z₀p₁)T invertible
  with balanced inverse.
- Pivot + flip: [v] = [1 + s₁·z^new] with
  z^new = (1 − t₁T)û⁻¹z₀:  z^new₀ = û⁻¹z₀,  z^new₋ = −t₁Tû⁻¹z₀,
  and the balanced part of the new flipped form is
  c = 1 − p₁Tû⁻¹z₀, giving p·c = p EXACTLY (kill-ideal = Mp).
- γ^new = 1 − t₁Tû⁻¹z₀s₁; invertibility of γ^new ⟺ invertibility of
  1 − p₁Tû⁻¹z₀ = c (ab/ba flip).  So the loop's γ-question becomes
  the invertibility of the new balanced part c — one more application
  of the SAME extraction to the new form may close (G) by a
  finite-descent (each round the balanced part is 1 − p₁(...) with
  p-corner IDENTITY — its singularity lives in the p₁-corner only;
  the p₁-corner of c is 1 − (p₁Tû⁻¹z₀)-corner: iterate the corner:
  candidate终 termination: the corner perturbations are compressions
  by t₁·(...)·s₁ which STRICTLY deepen the cylinder support —
  after finitely many rounds the perturbation's corner support
  exhausts and c becomes unipotent-plus-identity ⟹ invertible).
NEXT: nail the corner-depth termination for (G); then (i') general
index remains (p₁-supported reduction now WRITTEN).

## Session 18: LEMMA (i') PROVED — nilpotent tails die, all indices
THEOREM: z balanced, n := s₁z, n^D = 0 ⟹ 1 + s₁z ∈ H.
PROOF (induction on D; base D ≤ 2 = square_zero_tail_mem_stableUnits,
written):
Let D ≥ 3, r := (zs₁)^{D−2}z (pure degree D−2; nonzero else lower
index).  Facts: r·s₁·z = (zs₁)^{D−1}z = 0 (from n^D = 0 by
s₁-cancellation).
1. PSEUDO-INVERSE OF PURE-DEGREE ELEMENTS: r = R·σ_d with d := D−2,
   σ_d := wordS(0^d), R := r·τ_d balanced, R = R·p_{0^d}
   automatically.  Take Ξ balanced with RΞR = R (balanced regularity,
   written) and η := τ_d·Ξ.  Then rηr = R(σ_dτ_d)ΞRσ_d = RΞRσ_d = r.
2. e := η·r = τ_d(ΞR)σ_d: idempotent (e² = η(rηr) = ηr), BALANCED
   (τ_d·(balanced)·σ_d sandwich — needs the span-closure lemma
   t-word·span·s-word ⊆ span, same pattern as mul_p0_mem_span), and
   r·e = r.
3. KEY VANISHING: z·e·s₁·z = zη(r·s₁·z) = 0.
4. THE MOVE: mover m := 1 − s₁(ze): (s₁ze)² = s₁·(zes₁z)·e = 0,
   ze balanced ⟹ m ∈ H by square_zero_tail_mem_stableUnits.
   Product: m·(1 + s₁z) = 1 + s₁(z − ze − zes₁z) = 1 + s₁·z(1−e).
5. INDEX DROP: z' := z(1−e): expand (z's₁)^{D−2}z' over choices
   {zs₁, −zes₁} and final {z, −ze}: any term with e in a NON-final
   position contains zes₁·z = 0; the two survivors are
   (zs₁)^{D−2}z = r and −(zs₁)^{D−2}ze = −re = −r: they CANCEL.
   Hence (z's₁)^{D−2}z' = 0: index of s₁z' ≤ D−1.  Induction. ∎
LEAN PLAN (module NilpotentTailKill.lean):
- span-closure: mul by t-words on left / s-words on right of the
  balanced span (τ_d X σ_d sandwich) — generalize mul_p0_mem_span to
  arbitrary single letters, then induct over words;
- pure-degree right-mult: r·τ_d ∈ balanced span for r in
  window[d,d]-span (same machinery);
- the theorem by strong induction on D with the five steps above;
  the expansion step 5 needs a finite product-expansion lemma — do it
  by direct induction on D−2 with the two-term recursion
  (z's₁)^k z' = (zs₁)^k z(1−e) for all k ≤ D−2, proved by:
  (z's₁)((zs₁)^k z(1−e)) = (zs₁)^{k+1}z(1−e) − zes₁(zs₁)^k z(1−e);
  and zes₁(zs₁)^k z = zes₁z(...) = 0 for k ≥ 0 — WAIT check:
  zes₁·(zs₁)^k·z: starts zes₁z when k = 0 ✓ = 0; for k ≥ 1:
  zes₁·zs₁(...) = (zes₁z)s₁(...) = 0 ✓ ALWAYS.  So the recursion is
  CLEAN: (z's₁)^k z' = (zs₁)^k z (1−e) by induction on k — no
  binomial expansion needed!  Then k := D−2 gives r(1−e) = 0.
REMAINING for NarrowReduction: only the z₋-elimination/(G) — with
(i') done, NarrowReduction ⟸ (G) alone.

## Session 19: (G) dichotomy + worked instance; Fitting framework
- DICHOTOMY (proved): for u = 1 + s₁z, γ' := 1 + s₁z₋ (BALANCED —
  note s₁z₋ is degree 0!): γ' invertible ⟺ u⁻¹ has no negative
  graded components.  (⟸: bottom equation (1+s₁z₋)y_{−M} = 0 with
  y_{−M} = Σ C_w t_w, t_w-independence gives balanced kernel
  elements; ⟹: same equation kills y_{−M}.)  Note γ' vs γ = 1+z₋s₁:
  flip-equivalent invertibility.
- WORKED INSTANCE of (G): z₋ := −t₁ (γ' = p₀, maximally singular):
  u = p₀ + s₁z₀ is NEVER a unit: uy = 1 forces s₁z₀y = p₁ hence
  z₀y = t₁ hence y = z₀⁻¹t₁ (z₀ must be balanced-invertible), and the
  p₀-component equation forces p₀z₀⁻¹t₁ = p₀ — degree −1 = degree 0,
  contradiction by graded independence.
- GENERAL (G) FRAMEWORK: Fitting decomposition of the BALANCED
  element γ' at its level: π' := projector onto the generalized
  kernel (γ'π' =: N nilpotent, commutes with π'; γ'(1−π') corner-
  invertible).  The π'-corner unit equation reads (N + M)y = π' with
  M := π's₁z₀ pure degree +1; graded components give
  N·y_d + M·y_{d−1} = [d=0]π'; applying N^{K−1} isolates
  N^{K−1}My₋₁ = N^{K−1} ≠ 0, and coefficient extraction (x = Σ(xs_j)t_j
  valid for ALL x) turns this into balanced equations.  The worked
  instance is the K = 1 case where the (1−π')-side forces the graded
  contradiction.  CONJECTURED PROOF SHAPE: induction on K, pushing
  the contradiction of the K = 1 case through the nilpotent cascade.

## Session 20: second (G) instance + staircase formulation + chain plan
- Second non-unit verified: u = (1 − p₁₁) + s₁₁t₁ (γ' = 1 − p₁₁
  singular): the downward cascade forces t₁y₋₁ = t₁₁ and then
  γ'y₋₁ acquires an s₁t₁₁-component outside Im(s₁₁t₁·) = s₁₁·L,
  unsolvable by monomial prefix independence.  Pattern matches the
  p₀-instance: singular γ' + unit-ness ⟹ cascade escapes the image.
- (G) staircase formulation: u unit ⟺ 1 ∈ image of the staircase
  operator (y₀,…,y_{−M}) ↦ γ'y₀ + s₁z₀y₋₁ subject to
  γ'y_d + s₁z₀y_{d−1} = 0; (G) ⟺ solvability forces γ' invertible.
  Fitting corner analysis (K=1): all corner equations are consistent
  (tautological) — the contradiction must use monomial/prefix
  independence ACROSS levels as in both instances.  Note π = p₁π
  (kernels live under p₁ since p₀γ' = p₀), and the collapse
  Z·s₁ = W₁ with πs₁W₁ = πs₁, πs₁W₀ = πs₀.
- γ-ELIMINATION CHAIN (writable now, given γ-invertibility):
  γ = 1 + z₋s₁ invertible ⟹ γ⁻¹ balanced (γx = 1 ⟹ γx₀ = 1 at the
  balanced component ⟹ matrix-invertible in the subalgebra) ⟹
  [1+s₁z] = flip = [γ(1 + γ⁻¹z₀s₁)] = [1 + γ⁻¹z₀s₁] = flip =
  [1 + s₁(γ⁻¹-moved z₀)] pure z₋ = 0 ⟹ nilpotent automatic ⟹
  NilpotentTailKill.  Writing this as GammaReduction.lean with
  γ-invertibility as the explicit hypothesis.

## Session 21: (G) system fully catalogued; GammaReduction.lean written
WRITTEN: GammaReduction.lean (complete, hypotheses explicit).
(G) DERIVATION STATE — the master catalogue:
- MASTER FORM: u = p₀ + s₁·h with h := t₁ + z ∈ window[−1,0];
  h·(ys₁) = 1 (h right-invertible ALWAYS); (ys₁)h = 1 − yp₀ with
  f := yp₀ idempotent ≠ 0, p₀fp₀ = p₀, hf = 0.
- Λ-IDENTITY: s₁·Λ(x) = γ'x − p₀x where Λ(x) := (t₁ + z₋)x = h₋x.
- THE (S)-SYSTEM (t₁-extraction of positive equations):
  z₀y_d = −Λ(y_{d+1}) for 0 ≤ d ≤ N (y_{N+1} = 0).
- THE (C)-SYSTEM (negative side, coefficients C^{(j)}_w = y_{−j}s_w):
  γ'C^{(M)}_w = 0 at the bottom; z₀C^{(j+1)}_{wi} = −Λ(C^{(j)}_w)s_i;
  z₀C^{(1)}_i = [i=1] − Λ(y₀)s_i.
- ker γ' = {q : p₀q = 0, h₋q = 0}; kernels live under p₁; the flip
  kernel: left-kernel rows q' satisfy q's₁(1 + z₋s₁) = 0.
- INSTANCE VERIFICATIONS through (S): instance 1 (Λ = 0): z₀
  invertible forced, positive side forces z₀y₀ = 0 ⟹ y₀ = 0 ⟹
  contradicts p₀y₀ = p₀.  Instance 2: (S)-top forces y_N = 0 (N ≥ 1),
  then y₀ = p₀, then (XX₀) demands s₁₁t₁y₋₁ = p₁ — impossible by
  prefix independence (p₁₁ ≠ p₁).
- TAUTOLOGY TRAPS documented: p₀s₁ = 0 absorbs every naive q'-pairing;
  the corner equations are self-consistent — the contradiction is
  GLOBAL, coupling the finite (S)+(C) system with p₀y₀ = p₀.
- NEXT ATTACK: dimension/rank count over k of the finite staircase
  system: the unknowns (y_d components at bounded window/level) vs
  the equations; γ'-singularity creates a strict solvability defect
  that p₀y₀ = p₀ cannot meet — formalize the count on the finite-
  dimensional filtration pieces (all data at a common level m and
  bounded degree window; the staircase matrix is block-bidiagonal
  with γ' on the diagonal and s₁z₀ off-diagonal; det-style argument:
  the system forces 1 ∈ Im(bidiagonal operator) whose cokernel
  contains the γ'-cokernel at the 0-block — CHECK: is the d=0 block
  row exactly γ'y₀ + s₁z₀y₋₁ = 1 with coker(γ') obstructing modulo
  the s₁z₀-column? The instances say the s₁z₀-column cannot cover the
  γ'-cokernel because its image is s₁-prefixed while the cokernel
  needs p₀-content: p₀·(s₁z₀X) = 0 but p₀·1 = p₀ ≠ 0 — wait:
  p₀γ'y₀ = p₀y₀ = p₀ ✓ consistent... the p₀-row of the d=0 equation
  is auto-satisfied; the obstruction sits in the p₁-row where
  γ'|p₁-part = p₁ + s₁z₋ acts — TRY: q'-left-kernel pairing against
  the d = 0 equation DIRECTLY: q'γ' = 0 ⟹ q' = q's₁z₀y₋₁ (derived);
  iterate this DOWN the C-system: q' = q's₁z₀C-terms and
  z₀C^{(j)} = −Λ(C^{(j-1)})s-recursion pushes q' into
  q'·s₁·(z₀-Λ-chains) of length M+1 ending at γ'C^{(M)} = 0-kernel
  coefficients... then the chain terminates with q'·(...)·0 = q' ⟹
  q' = 0 IF each step is genuinely composable — CHECK THIS NEXT:
  q' = q's₁z₀y₋₁ = q's₁z₀(C_0t_0 + C_1t_1), substitute
  z₀C_i-hmm z₀C_i appears LEFT-multiplied inside; the recursion gives
  z₀C^{(1)}_i in terms of Λ(y₀) NOT of deeper C's — the descent
  direction is (G_{w,i}): z₀C^{(j+1)} = −Λ(C^{(j)})s_i: so
  q' = q's₁·z₀·y₋₁ needs z₀y₋₁ = z₀(C_0t_0+C_1t_1): z₀C_i-BUT the
  system gives z₀C^{(1)}_i directly = [i=1] − Λ(y₀)s_i!!! SUBSTITUTE:
  q' = q's₁([1-slot term] + corrections): q' = q's₁(z₀C_0t_0 + z₀C_1t_1)
  = q's₁(−Λ(y₀)s_0·t_0 + (1 − Λ(y₀)s_1)t_1)
  = q's₁t_1 + q's₁Λ(y₀)(−s_0t_0 − s_1t_1)
  = q'p₁ − q's₁Λ(y₀)  [since s_0t_0+s_1t_1 = 1]
  AND s₁Λ(y₀) = γ'y₀ − p₀y₀ = γ'y₀ − p₀ (Λ-identity + P!):
  q's₁Λ(y₀) = q'γ'y₀ − q'p₀ = 0 − q'p₀:
  ⟹ q' = q'p₁ + q'p₀ = q' — TAUTOLOGY AGAIN (p₀+p₁ = 1).  ALL linear
  pairings are consistent; the contradiction MUST be nonlinear
  (rank/dimension count) or use the mirror system (yu = 1) jointly.

## Session 22: (G) rank-count exhausted consistent; γ' IS MOVABLE
- M = 1 nonlinear relations derived: pairing the two inverse systems
  gives y_{−M}·s₁z₀·y_{d−1} = [d=0]·y_{−M}; for M = 1 this yields
  BALANCED idempotents P := s₁z₀y₋₁ (= p₁P, rank δ) and
  E := C₁z₀ with C₁z₀C_j = C_j, colsp(C₁) = ker γ' exactly,
  rank(C₁) = δ = corank(γ'), 1 − P ∈ γ'·Mat with colsp(1−P) =
  colsp(γ') exactly.  EVERY rank/subspace constraint checks out
  consistently, including the level-(m+1) scaling (rank P = 2δ_m from
  both computations).  The abstract matrix model of the system admits
  no contradiction — the instances' contradictions used the LEVEL
  EMBEDDING structure (s₁Xt_j corner copies), not the level-m algebra.
- VERDICT: (G) via rank counting at a fixed level is DEAD; (G) itself
  is possibly false as stated, and definitely not needed:
- KEY DISCOVERY: the p-split mover 1 − s₁(z·p₀) is in H for ARBITRARY
  z ∈ window[−1,0] (mem_stableUnits_of_val_unipotent with
  a := −s₁zs₀, b := t₀, ba = 0 — NO balancedness needed).  Hence
  [1 + s₁z] = [1 + s₁(z·p₁)] for mixed z, and more generally for all
  0-rooted cylinder projections V = p_{0w'} (t_{0w'}s₁ = 0):
  [1 + s₁z] = [1 + s₁·z(1 − p_{0w'})].  These moves CHANGE
  z₋ ↦ z₋·p₁ etc. — γ' is NOT invariant under them (session 15c's
  invariance was only for the other families).
- NEW ROUTE to NarrowReduction WITHOUT (G): use the mixed p-splits +
  corner transports + flips to normalize z₋'s column support, aiming
  to make 1 + s₁z₋ invertible (or z₋ = 0) reachable.  Note
  z ↦ zp₁ = zs₁t₁ then corner transport 1 + s₁(zs₁)t₁ = κ₁(1 + zs₁)
  gives [1+s₁z] = [1 + zs₁] for MIXED z — the flip — and zs₁ has
  components (zs₁)₋ = z₋s₁... iterate: the composite z ↦ t₁-shifted
  data: TRACK what happens to the negative part under
  z ↦ (the normal form of 1 + zs₁): worth computing whether the
  γ'-obstruction provably shrinks (column-depth of z₋'s 1-rooted
  content) per cycle.  ALSO available now: mixed-z tail support
  reduction means the ENTIRE session-13 loop machinery applies to
  mixed z with more freedom than previously exploited.

## Session 23: dynamics computed; the invariant sharpened to 1 + ẑ
- CORRECTION to session 22: the A-moves change γ' as an ELEMENT but
  not its invertibility class: (z₋(1−p_{0w}))s₁ = z₋s₁ always
  (t_{0w}s₁ = 0), and both old and new γ' are invertible iff
  1 + ẑ is, ẑ := z₋s₁ BALANCED.  So the true obstruction datum is
  the invertibility of 1 + ẑ — invariant under A-moves, prefix
  kills, and the flip (γ ↔ γ' are flip partners of it).
- THE FLIP EATS THE WINDOW: [1 + s₁z] = [1 + zs₁] with
  zs₁ = ẑ + z₀s₁ ∈ [0,1] — no negative part.  If 1 + ẑ invertible:
  factor and flip back ⟹ pure tail ⟹ NilpotentTailKill ⟹ DONE
  (this is GammaReduction, already written).
- CHIRALITY THEOREM (negative): [0,1]-forms with s₁-SUFFIX tails have
  NO mirror p-split (s·t words never vanish; only t·s do) — all
  annihilation-based movers live on the 1 + s₁(·) side.  Return to
  normal form hence requires the sr1-pivot loop.
- TWISTED ACTION found: right-mult by balanced h on v = c + z₀s₁ acts
  as (c, z₀) ↦ (ch', z₀φ₁(h)) via s₁h = φ₁(h)s₁, φ₁(h) := s₁ht₁ —
  wait: v·h = (1+ẑ)h + z₀φ₁(h)s₁ — the pair transforms with the
  CORNER TWIST φ₁ on the tail.  Left-mult: (gc, gz₀).  The
  (g,h)-orbit of (c, z₀) with the φ₁-twist is the corner-skew
  structure at the unit level; φ₁(h) is never invertible (image in
  p₁ corner) — the twist COMPRESSES the tail's right support.
- REMAINING QUESTION (sharpest yet): unit 1 + s₁z with 1 + z₋s₁
  singular: exhibit a move sequence reaching either invertible
  1 + ẑ' or H directly.  Available: M = 1 nonlinear idempotent data
  (P = s₁z₀y₋₁, E = C₁z₀, colsp(C₁) = ker γ', exact rank equalities),
  the twisted (g,h)-action, sr1-pivot loop, deep A-moves.  IDEA for
  next session: use the twisted action with h := suitable balanced
  unit to compress z₀'s right support INTO the corner where the
  M=1-idempotent data lives, making the balanced part invertible on
  the complement — i.e. exploit that φ₁(h)-compression can REMOVE
  exactly the tail content that couples to ker(1+ẑ), decoupling the
  singular part which then must vanish by the unit equations (the
  pure-singular case 1 + s₁z₋ + [tail coupling only to the regular
  part] should force the M=1 system into the instance-1 pattern
  where positive-side equations kill y₀'s p₀-part).

## Session 24: MAJOR — (G) reduced to one finite-dim case; three new theorems
REFORMULATION (P): u = 1+s₁z flips to v = γ + z₀s₁ ∈ window [0,1]
with BALANCED PART γ.  So (G) ⟺ (P): every [0,1]-window unit
w = c + ζ (c balanced, ζ ∈ L₁) has c invertible.  If (P): w = c(1+c⁻¹ζ),
pure positive tail, nilpotent automatically (below), done — NO
dynamics needed, GammaReduction's hypotheses all discharge.

NEW THEOREM 1 (no homogeneous units): L(1,2) has no units of pure
degree d ≠ 0.  Proof: pad w to level matrices: W is 2^p×2^q with
p−q = d ≠ 0; WX = I_{2^p}, XW = I_{2^q} impossible by rank.  Also the
ONE-SIDED version for d ≥ 1: a degree-(+1) element with a RIGHT
inverse of degree −1 is impossible (tall matrix ΞΡ = I_{2D}, rank ≤ D).

NEW THEOREM 2 (automatic nilpotency): unit 1 + ζ, ζ pure positive
degree ⟹ ζ nilpotent.  Proof: inverse x = Σx_d; degree recursion
x_d = δ_{d0} − ζx_{d−1} from the bottom: negative components vanish
(x_m = 0 for m < 0 directly!), x_0 = 1, x_d = (−ζ)^d, finite support
⟹ ζ^{M+1} = 0.  [Formalize via graded decomposition extraction.]

NEW THEOREM 3 (γ upgrade): 1+ẑ (ẑ balanced level q) invertible in L
⟺ invertible in B_q ≅ M_{2^q}(k) (singular matrix ⟹ zero divisor);
inverse automatically balanced.  So GammaReduction's hginv is free.

CORNER NORMAL FORM: mod H (balanced pivot units), any [0,1]-unit
becomes w = e + ζ, e = diagonal cylinder idempotent, f := 1−e.
FULL cross-corner unipotent toolkit: 1 + eηf, 1 + fηe ∈ H for ANY η
(a := eη, b := f, ba = 0 — mem_stableUnits_of_val_unipotent!).

CASE ANALYSIS on x := w⁻¹'s lowest degree m (c singular ⟺ m < 0):
- degree-0 f-compressions (hold for ALL m): (fx₋₁)(ζf) = f and
  (fζ)(x₋₁f) = f.  So ζf INJECTIVE (left-invertible), fζ surjective.
- m = −1: x₋₁ = fx₋₁f (from ex_m = 0 = x_me) ⟹ ξ := fζf is
  INVERTIBLE in corner fLf ≅ (amplified) L, homogeneous degree 1
  ⟹ contradiction by Theorem 1.  **m = −1 IMPOSSIBLE.**
- rank bound (all m): ζ_{fe}(ex₋₁f) + ξ(fx₋₁f) = f = I_{2D} at level:
  rank ≤ E + D ⟹ **E ≥ D: singular balanced part has rank ≥ 1/2.**
- equality E = D: forces Ξ full column rank (injective); but for
  m ≤ −2: x_m = fx_mf ≠ 0 with ξx_m = 0 ⟹ x_m = 0 contra.
  **E = D IMPOSSIBLE for m ≤ −2.**
- REMAINING: m ≤ −2, E > D strictly.  Chain equations: fζx_d = 0 and
  x_dζf = 0 for m ≤ d ≤ −2; im(ζf) ⊆ ker X_d; x_d = β_dx₀ − β_{d+1}x₋₁
  (β_d := x_de) for d ≤ −2, β_m·(from x_me = 0)... plus twisted trace.

MODULAR TRACE: normalized trace τ on L₀ (level-invariant); for
y ∈ L_d, z ∈ L_{−d}: 2^d·τ(yz) = τ(zy) (rectangular trace identity).
Gives τ(ex₀e) = 1 (all char, incl. char 2 — state multiplied form).
No positivity over 𝔽₂ (the MAIN case is 𝔽₂!) so trace alone can't
finish; it's one more constraint on the remaining case.

NEXT: (a) attack m ≤ −2, E > D by the β-recursion + padding rigidity
(the M=1 hand-case died by ⊗I₂-parallelism — generalize); AND
(b) actively search for a counterexample unit (rank e = 3·2^{q}/4,
m = −2 ansatz).  Even if (P) fails, mod-H moves + corner toolkit give
the fallback.  Meanwhile: Theorems 1–3 + corner form are formalizable
NOW and are needed regardless.

## Session 24b: the peeling isomorphism; K₀ is no obstruction; plan
MONOMIAL FACTS (recorded to avoid rederiving): S(a)T(b) nilpotent ⟺
a,b prefix-incomparable (else powers persist: S(a)T(b)² = S(a)T(db)
etc.).  t_is_j = δ_ij means NO t-before-s monomials exist; conjugation
experiments (1+ν)(1+σ)(1−ν) with ν = S(1)T(00), σ = S(00)T(1) give
window [−1,1] with negative part νσν-type surviving — no easy
[0,1]-singular unit from small conjugates (νσ = S(1)T(1), σν =
S(00)T(00), νσν = ν).

PEELING THEOREM (new, verified by direct ring computation): let
w = e + ζ be a unit ([0,1]-window normal form), x := w⁻¹, B := ζf =
wf, b := x₋₁ (so bB = f from the graded equation x₋₁ζf = f, and
x_dζf = 0 ∀d ≠ −1 — refined graded identities, both sides).  Set
P := B·b = ζf·x₋₁: then
  • P is a BALANCED idempotent (deg +1 · deg −1), P·B = B, (1−P)B = 0;
  • τ(P) = τ(f)/2 (modular trace);
  • Φ := (1−P)we : eL → (1−P)L is a RIGHT-MODULE ISOMORPHISM:
    injective: Φy = 0 ⟹ wy = P wy = B(bwy) ⟹ y = (xB)(bwy) = f(bwy)
    and y = ey ⟹ y = 0, using xB = Σx_dζf = f;
    surjective: Φ(ex v) = (1−P)v since (1−P)B = 0.
  ⟹ [e] = [1−P] in V(L).  BUT V(L(1,2))\{0} is the trivial monoid
  (all nonzero f.g. projectives ≅), so NO K₀ obstruction — as
  expected, the content is K₁-level.  Peeling gives a NEW [0,1]-unit
  u'' := (1−P)we + ψ (ψ ∈ PL₁f an explicit cylinder-matching
  partial isometry, degree +1 forced by trace scaling), but defect
  bookkeeping rank((1−P)e) is not guaranteed to improve without
  aligning P with e — open.
DECISION FOR NEXT TURN: settle (P) for m ≤ −2 COMPUTATIONALLY first:
implement exact L_𝔽₂(1,2) arithmetic (dict on word-pairs, prefix
collapse), then for structured/random ζ with e = 1−p₁₁ (E=3, D=1,
q=2) solve the LINEAR system wx = xw = 1 over 𝔽₂ with bounded
monomial support (|a|,|b| ≤ 5, ~4k unknowns, bitset Gaussian
elimination).  A solution = genuine counterexample certificate (then:
moves route with corner toolkit + peeling).  No solutions across the
sweep = strong signal (P) is true ⟹ hunt the proof via peeling
alignment / β-recursion + ⊗I₂ rigidity.

## Session 25: (P) PROVED — the corner-factorization rank argument
**THEOREM (P).**  L_k(1,2) has no unit of the form w = e + ζ with e a
balanced idempotent ≠ 1 and ζ pure degree +1.  Consequently every
[0,1]-window unit has invertible balanced part (rank normal form
C = g·E·h over the balanced matrix algebra reduces c to an idempotent
e mod balanced units, which preserves unit-ness and degree windows).

PROOF.  Let f := 1−e ≠ 0, x := w⁻¹ = Σ_{d=m}^{M} x_d graded.
(1) Graded equations: (A_d) ex_d + ζx_{d−1} = δ_{d0},
    (B_d) x_de + x_{d−1}ζ = δ_{d0}.
(2) Right-multiply (B) by f (ef = 0):  x_dζf = δ_{d,−1}f  ∀d.
    Left-multiply (A) by f:            fζx_d = δ_{d,−1}f  ∀d.  (R2)
(3) Downward expansion from (A) for d ≤ −1 (x_{m−1} = 0):
    x_d = Σ_{j=0}^{d−m} (−ζ)^j (f x_{d−j}).
(4) Substitute (3) into (R2) at d = −1 and right-multiply by f.
    With Y_c := f x_c f ∈ fL_cf and G_j := (−1)^j fζ^{j+1}f ∈ fL_{j+1}f:
        Σ_{j=0}^{−1−m} G_j · Y_{−1−j} = f.        (★)
    (If x has NO negative components the LHS is empty: f = 0, i.e.
    e = 1 — that is the invertible case.  So assume m ≤ −1.)
(5) RANK CONTRADICTION.  Fix level ℓ ≥ (max depth) + |m| + 1 and
    represent corner elements as rectangular matrices between the
    f-supported level spaces (dim D_ℓ = |f|·2^{ℓ−q}, D_{ℓ+c} = 2^c·D_ℓ),
    multiplicatively (prefix collapse = matrix product; f ↦ I_{D_ℓ}).
    Each term G_j·Y_{−1−j} factors V^{(ℓ)} → V^{(ℓ−1−j)} → V^{(ℓ)},
    so rank ≤ D_{ℓ−1−j}.  Hence
      D_ℓ = rank I ≤ Σ_{j=0}^{J} D_ℓ·2^{−1−j} = D_ℓ(1 − 2^{−(J+1)}) < D_ℓ.
    Contradiction.  ∎
Subsumes both the old m = −1 case and the E-vs-D dichotomy — no case
split at all.  Sanity: e = 1 gives D_ℓ = 0 (no contradiction) ✓; the
𝔽₂-computational search (running) expects ZERO hits ✓ to confirm.

CONSEQUENCE CHAIN (all side conditions of GammaReduction discharge):
[0,1]-unit w ⟹ c invertible ⟹ w = c·(1 + η), η := c⁻¹ζ ∈ L₁;
1+η unit ⟹ η nilpotent (Theorem 2, session 24); κ₁-transport
[1+η] = [1 + s₁(ηt₁)] with ηt₁ BALANCED and (s₁ηt₁)^D = s₁η^Dt₁ = 0
⟹ NilpotentTailKill ⟹ **every [0,1]-window unit ∈ H·(scalars)…**
actually ∈ H directly (c balanced-valued unit ∈ H).  Mirror statement
for [−1,0]-window units via the s↔t anti-automorphism (or rerun the
argument on xw-side).

## Session 25b: tree-rebalancers are in H — width-3 obstruction dissolves
- Test element ρ := S(0)T(00) + S(11)T(01) + S(10)T(1): verified
  ρρ' = ρ'ρ = 1 with ρ' the mirror — a genuine width-[−1,1] unit
  (Higman–Thompson/code-change element).  Its balanced part CAN be
  singular for width-3 units (explicit conjugate example, level 2,
  rank 1 of 4) — so (P) does NOT extend to width 3, LDU fails
  (explicit obstruction computed), and pivots are needed.
- **Incomparable unipotents:** for ANY prefix-incomparable words a,b:
  1 + λS(a)T(b) ∈ H via mem_stableUnits_of_val_unipotent with
  α := λS(a), β := T(b), βα = λT(b)S(a) = 0.  ALL degrees at once!
- **Mixed swaps:** σ̃_{ab} := 1 − p_a − p_b + S(a)T(b) − S(b)T(a) =
  (1+e_{ab})(1−e_{ba})(1+e_{ab}) ∈ H (SL₂ swap identity), and the
  sign-fix d := 1 − 2p_b is balanced-valued ∈ H, so the honest swap
  σ_{ab} = 1 − p_a − p_b + S(a)T(b) + S(b)T(a) ∈ H — for any
  incomparable pair a,b, ANY relative depths.
- Higman–Thompson V is generated by such incomparable transpositions
  (comparable moves route through an auxiliary disjoint cylinder,
  3-cycle of swaps) ⟹ ALL code-change units ρ ∈ H.
- REMAINING (the last mathematical gap, now very narrow): width-3 →
  width-2 mod H: show every [−1,1]-window unit reduces, using swaps +
  incomparable unipotents + balanced pivots (Bruhat/LPU over the
  cylinder groupoid), to a [0,1]- or [−1,0]-window unit; then (P)
  chain finishes NarrowReduction, hence ScalarReduction, B4, Theorem C.

## Session 25c: (P) computationally CONFIRMED over F2
Exact L_F2(1,2) arithmetic (scratchpad leavitt_search.py): monomial
prefix-collapse product, stream-module equation generation, linear
solve for bounded-support inverse, EXACT algebra verification of any
solution.  Selftests: relations, t_is_j, known unit/non-unit ✓.
RESULT: e = 1−p₁₁ (singular, rank 3/4): exhaustive over all 1023
nonzero degree-1 perturbations on the 10 shallow monomials (|b|≤1),
plus 100 random deeper samples (|b|≤2, up to 6 terms): ZERO units.
Control with e = 1 and nilpotent tail: unit correctly found.
Matches THEOREM (P) exactly.  The mathematics is settled; remaining
math gap is ONLY width-3 → width-2 (session 25b plan).

## Session 25d: Lean writing begun; exact roadmap for the (P)-chain
WRITTEN (uncompiled, registered in aggregator):
- IncomparableUnipotents.lean: incomparable_unipotent_mem_stableUnits
  (any unit valued 1 + s_a·y·t_b, a,b incomparable, ∈ H);
  incomparableUnit (explicit unit, inverse 1 − s_a y t_b);
  signedSwap := product of three incomparable unipotents ∈ H;
  signedSwap_val = 1 − p_a − p_b + s_at_b − s_bt_a (X/Y collapse
  lemmas hXX hXY hYX hXYX then calc + noncomm_ring).
- ShapeCalculus.lean: shapeMonomials p q; ShapeRep p q M x
  (x = ΣΣ M γ δ • s_γt_δ, index types Fin p → Fin 2);
  shapeRep_mem_span; exists_shapeRep (span_induction; Matrix.single —
  check pin API: `Matrix.single` vs `Matrix.stdBasisMatrix`!);
  shapeRep_entry (t_γ·x·s_δ = algebraMap (M γ δ), via
  prefixCode_orthogonal (fullBinaryCode _)); shapeRep_unique (needs
  hinj : Injective (algebraMap k A)); shapeRep_one (via
  fullBinaryCode_complete; unfolds IsComplete/fullBinaryCode — check
  those defs' exact shapes); shapeRep_mul (quadruple sum collapse);
  span_shapeMonomials_le_succ (trailing-cylinder split; ofFn/snoc
  juggling `List.ofFn_succ'`, `Fin.snoc` — COMPILE-RISK, may need
  hand lemma).

REMAINING LEAN MODULES for the (P)-chain (in dependency order), all
mathematics settled in sessions 24–25:
1. GradedComponents.lean:
   a. exhaustion: ∀ x : A(=BinaryLeavitt k) ∃ lo hi, x ∈ span
      (degreeMonomials lo hi).  Route: RingQuot.mkAlgHom_surjective +
      FreeAlgebra induction; generators s0,s1,t0,t1 ∈ window [−1,1];
      products via window_mul_mem_span; sums via span-window-union
      (monotone: span_degreeMonomials_mono).
   b. component decomposition: x ∈ span(window lo hi) → ∃ y_d ∈
      span(deg d d), x = Σ_{d=lo}^{hi} y_d (span_induction).
   c. uniqueness of components (graded_independence_all) + extraction
      lemma: two window elements equal ⟹ components equal.
2. PureTailNilpotency.lean (THEOREM 2): u unit, ↑u = 1 + η,
   η ∈ span(deg 1 1) ⟹ ∃ D, η^D = 0.  Decompose u⁻¹ by (1);
   componentwise equations of u⁻¹·(1+η) = 1 and (1+η)u⁻¹ = 1;
   downward induction kills negative components (x_m = 0 for m < 0
   directly from x_m + ηx_{m−1} = 0 chain bottom-up: at the LOWEST m:
   x_m = 0 if m<0 — careful: equation at degree m is x_m + ηx_{m−1}
   = δ_{m0} with x_{m−1} = 0); then x_0 = 1, x_d = (−η)^d, top:
   η·x_M = 0 gives η^{M+1} = 0.
3. RankNormalForm.lean (THEOREM 3 + normalization): c ∈ span
   (levelMonomials q):
   a. IsUnit c ↔ IsUnit (its balancedEmbed matrix) — have
      exists_balancedEmbed_eq + injectivity + multiplicativity in
      BalancedStableRank; inverse stays balanced.
   b. c = g·e·h with g,h balanced-VALUED units of A and e a 0/1
      diagonal cylinder idempotent (Matrix.Pivot diagonal + absorb
      units into diagonal scaling).
4. ZeroKOne.lean (THEOREM (P), the keystone):
   statement: [Nontrivial A] (hdiv …) {c ζ : A} (hc : c ∈ span deg 0 0)
   (hζ : ζ ∈ span deg 1 1) (u : Aˣ) (hu : ↑u = c + ζ) : IsUnit c.
   Proof skeleton (sessions 24/25, VERIFIED numerically):
   - normalize c = geh (3b); pass to unit w := g⁻¹uh⁻¹-value e + ζ'.
   - suppose e ≠ 1 (else done).  x := w⁻¹; decompose (1); graded
     equations; (R1/R2): x_dζf = δ_{d,−1}f, fζx_d = δ_{d,−1}f
     (f := 1−e); downward expansion x_d = Σ_j (−ζ)^j f x_{d−j};
     corner system Σ_j G_j Y_{−1−j} = f, G_j := (−1)^j fζ^{j+1}f,
     Y_c := fx_cf.
   - shapes: pick interface ℓ big; G_j ∈ span(shape ℓ (ℓ−1−j)), Y_c ∈
     span(shape (ℓ−1−j) ℓ) (padding); exists_shapeRep; shapeRep_mul;
     f's canonical matrix at (ℓ,ℓ) is 0/1-diagonal with D_ℓ = |T|·2^{ℓ−q}
     ones; shapeRep_unique identifies Σ M(G_j)M(Y_j) with it.
   - rank: D_ℓ = rank(diag) ≤ Σ_j rank(M(G_j)M(Y_j)) ≤ Σ_j 2^{ℓ−1−j}
     ≤ 2^ℓ − 2^{ℓ−1−J}.  Wait — need the SHARPER f-corner bound only
     if e-rank enters; actually the plain bound suffices when f = 1…
     NO: correct bound: rank ≤ min dims = card(Fin (ℓ−1−j) → Fin 2)
     = 2^{ℓ−1−j}, and D_ℓ ≥ 2^{ℓ−q} ≥ … CHECK: need Σ_j 2^{ℓ−1−j} <
     D_ℓ?  D_ℓ = |T_f|2^{ℓ−q} with |T_f| ≥ 1: Σ_{j=0}^{J}2^{ℓ−1−j} =
     2^ℓ−2^{ℓ−1−J} which EXCEEDS D_ℓ when f is small — MUST use the
     corner-supported rank bound: Y_c = f·x_c·f ⟹ M(Y_c) = M(f at
     (ℓ−1−j))·M(x-part) ⟹ rank ≤ rank M(f at ℓ−1−j) = D_{ℓ−1−j};
     then Σ_j D_{ℓ−1−j} = D_ℓ(1−2^{−(J+1)}) < D_ℓ ✓.  (Session 25
     proof used exactly this; keep f-factorization of Y explicit.)
   - Mathlib rank lemmas: Matrix.rank_mul_le_left/right,
     rank_add_le (check name; else via LinearMap.range sup),
     rank_diagonal, rank_one.
5. WidthTwoReduction.lean: every unit with value ∈ 1 + span(window
   [0,1])… general: value ∈ span(window 0 1) ⟹ u ∈ stableUnits:
   (P) → c unit → c-balanced-valued ∈ H (mem_stableUnits_of_val_mem_
   levelSpan via span_degree_zero_le_levelSpan); tail 1 + c⁻¹ζ:
   Theorem 2 nilpotency; κ₁-transport (pairKappaUnit s₁ t₁) to
   1 + s₁(ηt₁) with ηt₁ balanced (window mult); nilpotency transports
   ((s₁ηt₁)^D = s₁η^Dt₁); NilpotentTailKill.  Mirror [−1,0] version
   via the same argument on the anti-side OR omit (probably only one
   side needed).
6. Width-3 → width-2: MATH STILL OPEN (session 25b: Bruhat/LPU with
   swap pivots; swaps now ∈ H).  THE remaining mathematical gap.
   After it: NarrowReduction ⟹ ScalarReduction (ResidualReduction
   wiring, written) ⟹ B4 ⟹ Theorem C.

## Session 25e: GradedComponents.lean written
- exists_components: window element = Σ_{d ∈ Icc lo hi} y d with
  y d ∈ span(deg d d), vanishing outside window (span_induction;
  if-then-else component functions; Finset.sum_eq_single).
- components_unique: via graded_independence_all on differences.
- exists_mem_span_degreeMonomials ALREADY EXISTS (BinaryLeavittWindow,
  compiled green) — exhaustion is done.
- NEXT MODULES TO WRITE (roadmap in 25d): PureTailNilpotency (use
  exists_components on u⁻¹ + components_unique on the product
  equations — the product of window elements decomposes via
  window_mul_mem_span then extract componentwise equations by
  comparing the two decompositions of ↑u·↑u⁻¹ = 1);
  RankNormalForm; ZeroKOne (the (P) keystone); WidthTwoReduction;
  then the width-3 math.

## Session 26: PureTailNilpotency + RankNormalForm written
- PureTailNilpotency.lean (Theorem 2 formalized): widen inverse's
  window to lo ≤ −1 ≤ 0 ≤ hi; exists_components on ↑u⁻¹; two
  decompositions of 1 over Icc lo (hi+1) (shifted sum via
  addRightEmbedding + Finset.map_add_right_Icc + insert-argument);
  components_unique; upward kill of negatives (ℕ-indexed induction
  from lo); y 0 = 1; y n = (−η)^n; top equation ⟹ η^(hi.toNat+1) = 0
  (even/odd sign handling via Even.neg_pow/Odd.neg_pow).
  NAME RISKS for sweep: Finset.sum_ite_eq' arg order,
  Finset.map_add_right_Icc, addRightEmbedding simp,
  add_eq_zero_iff_eq_neg, pow_succ' direction, neg_mul_eq_neg_mul.
- RankNormalForm.lean: balancedEmbed_diagonal (diagonal ↦ weighted
  cylinder sums via matrixRingEquiv_diagonal + diagonal_map);
  balancedEmbed_indicator (Finset.sum_ite_mem + univ_inter);
  isUnit_matrix_of_isUnit (singular ⟹ zero divisor via
  Matrix.exists_mulVec_eq_zero_iff, all-columns-v matrix X);
  inv_mem_levelSpan_of_val_mem (THEOREM 3: balanced units have
  balanced inverses — inverse-uniqueness calc);
  exists_rank_normal_form (Pivot decomposition, D = D₁·E splitting,
  transvection products invertible via det route, g/h :=
  Units.map balancedEmbed of Pu⁻¹/Qu⁻¹, value = cylinder sum over
  S := filter (dvec ≠ 0), S = univ → IsUnit c).
  NAME RISKS: Matrix.exists_mulVec_eq_zero_iff (field/domain +
  direction), Matrix.TransvectionStruct.prod_mul_reverse_inv_prod,
  Units.map_inv direction, Matrix.dotProduct vs dotProduct in simpa,
  RingHom.mapMatrix_apply, Matrix.diagonal_map hypothesis.
- Registered in aggregator.  NEXT: ZeroKOne.lean (the (P) keystone —
  see 25d roadmap step 4), then WidthTwoReduction, then width-3 math.

## Session 27: THE KEYSTONE IS WRITTEN — ZeroKOne.lean and supports
- DegreeShapeBridge.lean: exists_ofFn_eq, monomial_mem_shapeSpan
  (r-induction over trailing pads), exists_shapeSpan_of_degreeSpan
  (uniform interface thresholds via span_induction + max),
  shapeRep_add, shapeRep_finsetSum, rank_finsetSum_le
  (RISKS: Matrix.rank_add_le, Matrix.rank_zero, Finset.induction_on
  case-binder names).
- CylinderCornerRank.lean: appendFun + ofFn_appendFun
  (List.ext_getElem / getElem_ofFn / getElem_append — API RISK),
  appendFun_injective, wordT_cylSum_wordS (full delta computation),
  cylSum_mem_shapeSpan, card_le_rank_of_shapeRep_cylSum (U·M·V = 1
  certificate over {γ // γ ∈ T} × (Fin (ℓ−n) → Fin 2); rank_one,
  rank_mul_le_left/right, Fintype.card_fun), and
  rank_le_card_of_shapeRep_cylSum (per-cylinder s_γ·t_γ isometry
  factorization; rank_le_card_width RISK).
- ZeroKOne.lean: balanced_component_isUnit — the FULL (P) proof:
  by_contra; rank normal form ⟹ e, f = Σ_T cylinders, T ≠ ∅;
  hcyl/hfe/hff orthogonality; w := g·u·h with value e + ζ';
  graded components of w⁻¹ + componentwise equations (same
  sum-splitting pattern as PureTailNilpotency); hsubst
  (y d = f·y d − ζ'·y (d−1) for d ≤ −1, both in-window and
  out-of-support cases); the remainder induction hclaim
  (GG j := f·ζ'·(−ζ')^j, YY j := f·(y(−1−j)·f) — NOTE: GG has NO
  trailing f so the induction is pure noncomm_ring + pow_succ; hff
  needed only in the base case); termination at M := (−lo).toNat;
  interface ℓ := n + M + 1 + B (B := sup of shape thresholds);
  dependent choose over range M with attach-sums (Finset.sum_attach);
  lower bound via card_le_rank_of_shapeRep_cylSum, upper via
  factor-through-Mf; geometric-sum contradiction (sum_range_reflect,
  sum_two_pow, mul_lt_mul_of_pos_left, pow_pos).
  RISKS: Finset.sum_ite_eq' arg-order, Finset.sum_mul_sum shape,
  add_eq_zero_iff_eq_neg, attach/sum_attach forms, set-vs-rw
  interactions, `simp only [] at` beta-reduction usages.
- All registered in aggregator.  REMAINING: WidthTwoReduction.lean
  (assembly: (P) + Theorem 3 + κ₁-transport + NilpotentTailKill ⟹
  every [0,1]-window unit ∈ H); the width-3 → width-2 mathematics;
  then NarrowReduction assembly and the compile-and-fix sweep.

## Session 27b: WidthTwoReduction written — the (P)-chain is complete in Lean
- WidthTwoReduction.lean: window_zero_one_mem_stableUnits — full
  assembly: components split (Icc 0 1 = {0,1});
  balanced_component_isUnit; balanced unit uc ∈ H with balanced
  inverse; residual v := uc⁻¹u value 1 + η; pure_tail_nilpotent;
  κ₁ := pairKappaUnit s₁ t₁ transport to 1 + s₁(ηt₁) (balanced,
  nilpotency transported via (s₁ηt₁)^{m+1} = s₁η^{m+1}t₁);
  nilpotent_tail_mem_stableUnits; assembly u = uc·(κv⁻¹)⁻¹·κ.
  hdiv from LeavittSimplicity.exists_mul_mul_eq_one (implicit-x
  signature: exists_mul_mul_eq_one k hx).
  RISKS: t_one_mem_window name, pairKappaUnit explicit-arg order.
- STATUS: the entire width-2 story is now WRITTEN in Lean end-to-end:
  ZeroKOne (P) → RankNormalForm (Thm 3) → PureTailNilpotency (Thm 2)
  → κ-transport → NilpotentTailKill → H.  What remains
  mathematically: ONLY width-3 → width-2 (narrow units to [0,1] or
  [1 + s₁z] form mod H).  Then: NarrowReduction := width-3 step +
  window_zero_one_mem_stableUnits (+ flip for [−1,0]-forms if
  needed); ScalarReduction wiring already written
  (ResidualReduction); then B4; then the single compile-and-fix
  sweep over all uncompiled modules (list: ResidualMoves,
  ResidualReduction, BalancedRegularity, TailSupportReduction,
  WindowProductClosure, NilpotentTailKill, GammaReduction,
  IncomparableUnipotents, ShapeCalculus, GradedComponents,
  PureTailNilpotency, RankNormalForm, DegreeShapeBridge,
  CylinderCornerRank, ZeroKOne, WidthTwoReduction).

## Session 28: width-3 analysis sharpened (math turn)
- NEW STRUCTURAL FACT (corollary of (P)!): right- or left-
  multiplication by [0,1]-window H-units can NEVER kill a nonzero
  degree-(−1) part: (u·m)₋ = u₋·m₀ and m₀ is INVERTIBLE by (P).
  So width-3 → width-2 requires movers with genuine negative parts:
  the incomparable unipotents 1 + S(α)yT(β), |β| > |α| (∈ H ✓), and
  their products, plus two-sided balanced units.
- Canonical form for the bottom: rank-normalize a's rectangular
  coefficient matrix (balanced g·a·h): WLOG a = τ_r = Σ_{i<r}
  S(α_i)T(β_i), canonical partial isometry (orthonormal families).
- c-invertible sub-case: u ~ 1 + A + B (A := c⁻¹a).  If A nilpotent
  with (1+A) ∈ H then (1+A)⁻¹u = 1 + (1+A)⁻¹B still has negative
  parts from the inverse tail ((−A)^jB ∈ L_{1−j}) — one-sided
  clearing insufficient.  LDU needs Riccati C'(1+C') = −AB
  (Artin–Schreier over 𝔽₂ — not always solvable): exact LDU fails,
  mod-H version open.
- NEXT SESSION PLAN:
  1. COMPUTATIONAL probe (leavitt_search.py is ready): (a) do
     width-3 units with invertible c always have nilpotent c⁻¹a?
     (test 1 + t₀ + B ansatz over 𝔽₂); (b) explicitly H-reduce the
     rebalancer ρ = S(0)T(00)+S(11)T(01)+S(10)T(1) by hand/machine
     to discover the general move pattern (ρ IS in H by K₁ = 0; find
     the witness!).  ρ's reduction pattern likely IS the algorithm.
  2. Try: u·(1+ν) with ν = −ρ₀-pattern... general scheme: mixed
     unipotent right-movers 1 + ν (ν ∈ L₋₁, monomial-incomparable
     form) change a by c·ν (constraint a·ν = 0) — set up the
     linear-algebra of {ν : aν = 0} acting on a via c·ν, iterate
     with balanced renormalizations; measure: rank r of a.
  3. Remember: [−1,0]-window units ∈ H by the MIRROR of the width-2
     chain (s↔t antiautomorphism — formalizable as the op-algebra
     family or by rerunning the argument on xw = 1 side).

## Session 29: EXPLICIT H-witness for the rebalancer; (P) generalizes to [0,N]
- COMPUTED BY HAND (exact monomial calculus, verified stepwise):
  ρ = S(0)T(00) + S(11)T(01) + S(10)T(1) (the basic tree rebalancer),
  σ₁ := swap(01, 1) (incomparable ✓ ∈ H), σ₂ := swap(00, 1)
  (incomparable ✓ ∈ H):
    ρ·σ₁ = S(0)T(00) + S(11)T(1) + S(10)T(01)
    ρ·σ₁·σ₂ = S(0)T(1) + S(10)T(01) + S(11)T(00)  — ALL BALANCED!
  Hence ρ = (balanced unit)·σ₂·σ₁ ∈ H.  **Explicit witness found.**
- THE SWAP-MOVE CALCULUS (general step): right-mult by σ_{β,w}
  (|w| = |β|−1, w incomparable to β): kills a's β-column
  (S(α)T(β) ↦ S(α)T(w), balanced), constraints: a·p_w = 0 (else
  deg −2 junk) and c·p_w = 0 (else NEW deg −1 junk c·S(w)T(β));
  b's β-column up-shifts to degree +2 — so the cascade lands in
  window [0,2], NOT [0,1].
- **(P) GENERALIZES TO [0,N] WINDOWS** (derivation done): for
  w = e + ζ₁ + … + ζ_N, the downward elimination with GROUPED
  coefficients gives f = Σ_{c≤−1} H_c·(f x_c f), H_c ∈ f·L_{−c}·f a
  SINGLE element per degree (sum over composition paths — grouping
  is essential: raw term-counting gives Fibonacci growth and fails);
  the rank argument is unchanged: Σ_c D·2^c < D.  COROLLARIES:
  (i) no units with all-positive windows (e = 0 case);
  (ii) [0,N]-unit ⟹ balanced part invertible.
  Lean note: ZeroKOne's induction needs upgrading from single
  remainder to remainder-per-depth (vector/strong induction) for
  general N — or a separate ZeroKOneN module; N = 2 would suffice.
- REMAINING GAPS in the width-3 plan: (a) free-cylinder supply for
  the swap cascade: need w with a·p_w = 0 AND c·p_w = 0 — after
  rank-normalizing c → e, free-for-c columns are Sᶜ but a's columns
  may cover them; need a pre-move to shrink/align a's column support
  (candidates: prefix kills a ↦ a·(1−p), balanced right-units,
  a's OWN rank normal form τ_r with column family orthogonalized —
  note a·h-normalization changes column support freely!
  a-CANONICAL: a = τ_r = Σ S(α_i)T(β_i): columns = the β-family,
  SMALL (r of them) — then need e's support to avoid β's: e·p_{β_i}
  = 0 ⟺ β_i ∈ Sᶜ-cylinders... adjust by swapping WITHIN balanced
  (permutation units) to relocate Sᶜ onto the β-family?? — the
  β-family sits at depth m+1, S at depth n: refine and match counts:
  |Sᶜ|·2^{m+1−n} ≥ r needed — rank inequality!  This smells like
  exactly the E ≥ D bound from session 24.  DERIVE next session.);
  (b) tail-kill for [0,2]: 1 + η₁ + η₂ ∈ H (κ-transport gives
  z := (η₁+η₂)t₁ ∈ [0,1] NOT balanced — NilpotentTailKill needs an
  upgrade to mixed nonneg tails, or a two-step split).
- The endgame is now a bounded list of concrete lemmas.  NO open
  conceptual mysteries remain — all remaining items have identified
  attack routes.

## Session 29b: [0,2]-tail-kill (B2) reconnaissance
- Unit 1 + τ (τ ∈ [1,N]) has pure-nonneg inverse 1 + τ' with x₀ = 1
  (bottom-up recursion — same as PureTailNilpotency's first half).
- Circularity check: κ-transport → p-split → prefix-kill → corner
  transport returns exactly to 1 + τ (t₁s₁ = 1 collapses zs₁ = τ).
  Flips conserve the window under every row/column split tried
  (first-letter, last-letter, depth-N splits all return [1,N]).
- Corner-localization: κ₁₁-transport (pair S(11), T(11)) puts the
  tail in the p₁₁-corner; right-mult by ν := S(0)yT(11β′) acts as
  PURE ADDITION ((κv)ν = ν since T(11)S(0) = 0); left-mult mixes via
  T(β′)τ.  Free-corner arithmetic is available but no kill found yet.
- MOST PROMISING for (B2, N = 2): generalize NilpotentTailKill's
  induction (lemma i′) to mixed z ∈ [0,1]-window tails 1 + s₁z:
  the p-split z ↦ zp₁ is free for mixed z (session 22), and the
  pseudo-inverse/mover machinery (BalancedRegularity) needs the
  balanced PART of z only — investigate whether the index-drop
  recursion survives with the degree-1 part of z along for the ride.
  Alternatively: (B2) via the session-22-style unipotent factor
  1 − s₀a₀t₁ (∈ H, βα = t₁s₀a₀ = 0) which keeps windows nonneg —
  look for the right composite.
- Meta-status: remaining math = (a) free-cylinder supply for the
  swap cascade (rank-inequality flavored, session 24's E ≥ D bound
  is the template) + (B2, N = 2).  Both concrete, both bounded.

## Session 30: the stable block-move calculus for width-3
- KEY IDENTITY (elementary, two E-ops, all sizes): for ANY unit u and
  any row P, column Q: [diag(u, I)] = [[[u − PQ, −P],[Q, I]]] mod E.
  (M₀ = diag(u,I); right-mult E₂₁(Q): [[u,0],[Q,I]]; left-mult
  E₁₂(−P): [[u−PQ, −P],[Q, I]].)
- Applied with the RIGHT-split of the negative part w₋ = Σ(w₋sᵢ)tᵢ
  (P := (w₋s₀, w₋s₁) balanced row, Q := (t₀; t₁)):
  M₁ := [[w − w₋, −C₀, −C₁],[t₀, 1, 0],[t₁, 0, 1]] — the negative
  content of the class becomes EXACTLY the canonical column (t₀; t₁).
- MIXED-DEPTH TRANSPORT: through prefixMatrixFamily with a complete
  code of lengths (ℓ₁, ℓ₂, ℓ₂), entry (i,j) picks up degree ℓᵢ − ℓⱼ.
  CONSERVATION OBSTRUCTION: any split w₋ = PQ has deg P + deg Q = −1,
  and transport shifts P, Q degrees oppositely — P and Q can never
  both land in [0,1] in ONE move.  With Q-fix (ℓ₂ = ℓ₁ + 1) the
  C-entries land at degree −1; with P-fix the t's stay at −1.
- Col-op kills of the t-column against the I-block exactly undo
  move 1 (trivial circle); row-op kills need inverting non-units;
  support-shrinking subtraction (row₂ −= (t₀s₁)row₃) does not
  terminate.  Iterating the block-move relocates the t-column
  forever (Sisyphus) — monotone depth assignments contradict.
- CONVERGENCE: everything reduces to ONE normalization: make the
  C-row vanish against the code — i.e. pre-kill w₋'s column content
  outside a controlled cylinder set, using (i) rank-normalization
  w₀ → e, (ii) mixed unipotents u(1+ν) shifting w₋ by e·ν (e-row
  content controllable), (iii) the free-cylinder supply question =
  session-24's E ≥ D rank bound.  If w₋ can be arranged with
  C₁ = 0 (single-branch: w₋ = C₀t₀, i.e. w₋p₁ = 0), then code
  (ℓ, ℓ+1, ℓ) — u-block ℓ, t₀-block ℓ+1, spare ℓ — puts M₁ entries:
  X: [0,1] ✓, −C₀ at (1,2): ℓ−(ℓ+1) = −1 ✗ ... still blocked; but
  C₀ = w₋s₀ and single-branch w₋ = C₀t₀ allows instead P := (w₋),
  Q := (t₀) 1×1-split: M₁ = [[w − w₋, −w₋],[t₀, 1]]: (1,2)-entry
  w₋ degree −1 at code (ℓ, ℓ+1): −1 + ℓ − (ℓ+1)?? no: (1,2): ℓ₁−ℓ₂ +
  (−1) = −2 ✗; code (ℓ+1, ℓ): (1,2): +1−1 = 0 ✓✓ (2,1): ℓ−(ℓ+1)−1 =
  −2 ✗.  STILL conserved.  → The block-move ALONE cannot do it; must
  be combined with genuine content-kills (swap cascade / e-row
  unipotents).  NEXT: formalize-friendly plan: (1) rank-normalize
  w₀ → e; (2) use e-row unipotents + swaps to force w₋ = e·w₋ and
  w₋-columns inside Sᶜ-free-cylinders (supply from |Sᶜ|-count vs
  rank w₋ ≤ ... session-24 E ≥ D!); (3) THEN the swap cascade
  (session 29) balances w₋ term by term without new negatives
  (constraints a·p_w = 0, e·p_w = 0 satisfiable by construction);
  (4) land in [0,2]; (5) (P)-N=2 + B2-N=2.  And B2-N=2 itself:
  revisit via the SAME block-move: 1 + η₁ + η₂: P := (s₀,s₁)·η-split
  top-down: [diag] ~ [[1+η₁, −P'],[Q', I]] with P' ∈ L₁-entries,
  Q' = (t·η₂) ∈ L₁-entries: ALL ENTRIES [0,1]-window ALREADY —
  deg P' + deg Q' = +2 splits as 1+1 ✓✓ NO obstruction for the
  POSITIVE side!!  **B2-N=2 SOLVED**: η₂ = Σᵢ sᵢ(tᵢη₂), P := (s₀,s₁)
  (deg 1), Q := (t₀η₂; t₁η₂) (deg 1): M₁ = [[1+η₁, −s₀, −s₁],
  [t₀η₂, 1, 0],[t₁η₂, 0, 1]]: window [0,1] entrywise; transport via
  EQUAL-depth code (any 4-code, pad to M₄ with 2-deep words): entries
  keep [0,1]; matrixRingEquiv → [0,1]-window unit of L →
  WidthTwoReduction → ∈ H; descent: mem_stableUnits_of_cornerDiag /
  glFour-machinery relates [diag(v, I₃)] to [v].  Same for all N by
  induction (top-split drops window by one each time).
  **THE (B2) GAP IS CLOSED.**

## Session 30b: negative-side analysis; conservation law; test queue
- CONSERVATION LAW (proved): under E-block-moves + mixed-depth
  transport, the sum of entry-degrees around any directed cycle of
  the block structure is invariant; DIAGONAL entries' degrees are
  absolutely invariant.  So negative content can never be removed by
  block-moves/transport alone — genuine content-kills (swaps, e-row
  unipotents) are required.  (Positive-side B2 escaped because
  deg-sum +2 splits into two nonneg slots.)
- Case c invertible (e = 1): swap cascade blocked (no free columns:
  c = 1 has full support).  HOPE: A := c⁻¹·w₋ is NILPOTENT for units
  1 + A + B (then 1+A ∈ H by mirror width-2; but naive factoring
  widens the window — needs care even if true).
  Graded equations give: A x_m = 0, x_m = −A x_{m+1},
  (1 − BA) x_{m+1} = −A x_{m+2}, … — nilpotency-flavored.
- COMPUTATIONAL QUEUE (leavitt_search.py ready, run next turn):
  (1) is 1 + s₀ + t₀ a unit in L_F2(1,2)?  (Toeplitz symbol says no
  within ⟨s₀,t₀⟩, but L(1,2) is simple — inverse could use s₁,t₁!)
  (2) search units 1 + A + B with A non-nilpotent (A = t₀-ansatz,
  random B); (3) if all A's nilpotent: conjecture + prove via the
  graded chain; (4) exhaustive small-window [−1,1]-unit census to
  map the singular-c stratum.

## Session 31: computational evidence + the A-nilpotency conjecture
- 1 + s₀ + t₀ is NOT a unit (B=4,5 both fail) — consistent with the
  Toeplitz symbol heuristic even inside simple L(1,2).
- 10/10 randomly-found width-3 units 1 + A + B have NILPOTENT A
  (all index 2); 180 adversarial trials with forced comparable
  monomials (S(0)T(00), t₀, S(1)T(11)) in A: ZERO units.
- CONJECTURE (A-nilp): 1 + A + B unit ⟹ A nilpotent.  Proof
  candidates: (i) T-deformation: U := A + T + T²B is a unit of
  L_{k(T)} (scalar·scaling-automorphism image); clearing
  denominators U·Ṽ = q(T)·1 in L_k[T]; specialize/valuate at T = 0;
  (ii) (P)-style rank argument on the two-sided graded recursion
  A x_{d+1} + x_d + B x_{d−1} = δ_{d0}.
- Under positive-unipotent movers (1+τ, τ ∈ [1,N]) u₋ is INVARIANT
  (both sides); balanced movers act by u₋ ↦ g u₋ h; only swaps and
  negative-unipotents genuinely change u₋.
- NEXT: BFS/greedy move-search engine over H-moves (swaps, balanced
  pivots, unipotents) on the 10 instances + ρ: extract the general
  reduction algorithm from machine-found witnesses, then prove
  termination.  This closes the last math gap empirically first.

## Session 31b: the Ω-homogeneous cofactor system for A-nilpotency
- U := A + T·1 + T²B ∈ L_k[T] is HOMOGENEOUS of weight 1 for the
  grading Ω := deg_T − deg_L.  From unit-ness over k(T): clearing
  denominators UṼ = ṼU = q(T)·1 and PROJECTING onto Ω-components:
  for ANY j with q_j ≠ 0 there is an Ω-homogeneous two-sided
  cofactor P with U·P = P·U = T^j·1.
- Choosing j := r := ord_T(q): r ≥ 1 is FORCED — r = 0 would make U
  invertible in L_k[T], and T := 0 gives A two-sided-invertible of
  pure degree −1, contradicting no-homogeneous-units.  ✓
- The cofactor system (P = Σ T^i P_i, P_i of L-degree i−r+1):
    A·P_i + P_{i−1} + B·P_{i−2} = δ_{ir},   (two-sided versions)
  with A·P₀ = P₀·A = 0 at the bottom and the window finite — the
  same shape as the (P)-corner system with A in the pivot slot.
  REMAINING: extract A-nilpotency (or directly 1+A+B ∈ H) from this
  system by the rank/factorization method; the specialization
  T := 0 of U·P = T^r·1 gives A·P(0)... wait P(0) = P₀: A·P₀ = 0 —
  consistent; the content is in the higher T-coefficients.
- Alternative still open: BFS move-search engine to machine-discover
  H-reduction witnesses for the 10 concrete instances (swaps +
  balanced pivots + unipotents), then generalize.  ENGINE NEXT TURN.

## Session 31c: A-nilpotency — the toy case resolves; BVP structure
- B = 0 toy: U = A + T: polynomial cofactor P with (A+T)P = T^r
  forces P_i = ±A^{r-1-i} by the (now clean, first-order) downward
  recursion, and the bottom boundary A·P₀ = 0 gives **A^r = 0** —
  the mechanism works exactly.  Conversely non-nilpotent A (e.g. t₀)
  makes A+T non-invertible over k(T) (graded independence of powers
  blocks resummation).
- General B ≠ 0: the system A P_i + P_{i-1} + B P_{i-2} = δ_{ir} is
  a two-point BOUNDARY VALUE problem (the BP_{i-2} term refers
  downward), not a recursion; the cofactor P is UNIQUE (U regular);
  boundary: A P₀ = P₀ A = 0.  The claim A^r-ish = 0 should follow
  from solvability + uniqueness + the bottom boundary — likely via
  eliminating B by the SAME grouped-coefficient trick as (P)-N≥2
  (group all paths reaching depth i into a single coefficient).
  Concretely: iterate the substitution P_{i-1} = δ − AP_i − BP_{i-2}
  into itself to express P_{-1} = 0 as (grouped polynomial in A, B
  acting on seeds) — the resulting identity at the bottom is the
  nilpotency statement.  FINISH NEXT TURN.

## Session 32: THE COMPILE SWEEP IS DONE — full tree GREEN (3723 jobs)
All ~20 previously-unverified modules now compile with
-DwarningAsError=true, INCLUDING:
- NilpotentTailKill (lemma i′), GammaReduction, TailSupportReduction,
  ResidualMoves, ResidualReduction, WindowProductClosure,
  BalancedRegularity, IncomparableUnipotents,
- ShapeCalculus, GradedComponents, DegreeShapeBridge,
  CylinderCornerRank (both rank certificates),
- PureTailNilpotency (Theorem 2), RankNormalForm (Theorem 3),
- **ZeroKOne (THEOREM (P)) — the manuscript's [ABC09] K₁-input
  replacement is now MACHINE-VERIFIED**,
- WidthTwoReduction (window_zero_one_mem_stableUnits) — the complete
  width-2 chain, first-try green.
Fix-log highlights (for future reference): z₋-subscript-minus is not
a valid Lean ident; beta-redexes block rw after refine-with-lambda
(beta_reduce); noncomm_ring CANNOT float -1• out of mid-product
factors — isolate negation in pure-rewrite pow-identities
(hpow0-pattern) and distribute subs with mul_sub/sub_mul + congr
before noncomm_ring; Even.neg_pow needs explicit base arg;
prefixCode_orthogonal needs an ofFn-typed have-binding;
obtain-destructuring clears the source hypothesis;
Matrix rank_add_le doesn't exist at pin (proved matrix_rank_add_le
via finrank_sup_add_finrank_inf_eq + finrank_mono);
exists_mulVec_eq_zero_iff lives in ToLinearEquiv;
isUnit_of_mul_eq_one absent — det-route via
left_ne_zero_of_mul_eq_one; Units.coe_map_inv not map_inv;
Int intervals: Mathlib.Data.Int.Interval.
AUDIT: full build green; audit flags = exactly the width-3 frontier:
LAUNDERED_PROP [NarrowReduction def], UNUSED [rank-normal-form &
pseudo-inverse chains awaiting the final wiring], STALE_DISCLAIMER
[3 main-theorem docstrings to update at assembly time].
REMAINING: width-3 math (A-nilpotency finish + swap-cascade supply),
its formalization, NarrowReduction proof + assembly, docstring
updates, final audit.

## Session 33: B2-N=2 is fully formalizable with COMPILED tools; H is normal
- KEY REALIZATION: the commutator lemma is already formalized
  (commutator_mem_elementaryGroup_of_division): H ⊴ Units and
  Units/H is ABELIAN — free rearrangement of products mod H.
  (Scaling-automorphism tricks die over 𝔽₂: k* trivial.)
- B2-N=2 FORMALIZATION ROUTE (all ingredients compiled TODAY):
  v = 1 + η₁ + η₂ ⟹ M₄-matrix M := E₁₂(−P)·diag(v,I₃)·E₂₁(Q),
  P := (s₀,s₁,0), Q := (t₀η₂; t₁η₂; 0): entries in window [0,1];
  transport via the EQUAL-depth code {00,01,10,11} (matrixRingEquiv,
  formalized): û has value in span[0,1] ⟹ WidthTwoReduction ⟹ H;
  diag(v,I₃)-descent via pairKappa/cornerDiag machinery (formalized);
  elementary factors via transvection-pullback (formalized).
  Degree-shift embeddings CANNOT exist (ring homs preserve 1; any
  (s,t) with ts = 1 has balanced degree) — confirmed the transport
  must use equal depths for nonneg windows, mixed depths otherwise.
- Conservation law re-confirmed on 4-element mixed-depth codes
  ({0,10,110,111}): the direct block-move on the NEGATIVE part
  remains impossible (C-row and t-column degrees sum to −1 around
  the cycle).  The negative side genuinely requires content-kills:
  A-nilpotency (cofactor BVP, toy case done) + swap-cascade supply.
- NEXT CONCRETE STEPS: (1) write BlockMoveTailKill.lean (B2-N=2 as
  above — mechanical, all deps green); (2) finish A-nilpotency via
  the grouped-coefficient elimination on the cofactor BVP;
  (3) mirror width-2 chain ([−1,0]-windows) — either θ-antiauto
  formalization or rerun of the chain on the xw-side;
  (4) singular-c width-3 assembly (swap cascade with supply from
  E ≥ D-rank-bound); (5) NarrowReduction wiring, docstrings, audit.

## Session 33b: BVP notes for the fresh session
- Upward elimination of the cofactor BVP produces
  1 = A·P_r + (1−BA)·P_{r−1} − B²P_{r−3} + ... with B^{2j}·A-middle
  terms — A not left-factorable; elimination alone insufficient.
- Modular trace in char 2: τ(AP_r) = τ(BP_{r−2}) = 0 (doubling dies),
  so (L_r) gives τ(P_{r−1}) = 1 — the balanced middle coefficient has
  full normalized trace.  One more constraint for the rank attack.
- The decisive step is expected from combining: degrees of P_i
  (P_i ∈ L_{i−r+1}, so the BOTTOM half P₀..P_{r−2} has negative
  degrees = SHAPE-SHRINKING maps), the boundary AP₀ = P₀A = 0, and
  the shape-rank method: at level ℓ, express the identity-block
  certificate of 1 (from L_r) through composites that factor through
  the bottom chain — mirror of the (P)-argument with the roles of
  raising/lowering swapped.  START HERE NEXT SESSION.

## Session 34: GammaDischarge GREEN — the normal-form case is a THEOREM
- VERIFIER BUG FOUND AND FIXED in leavitt_search.py: monomial-set
  comparison misses equalities needing p₀+p₁ = 1; replaced final
  verification with the faithful stream action.  ρ now correctly
  certified as a unit.  (P)-experiments re-validated with the fixed
  net: still zero counterexamples.  A-nilpotency: FALSE for singular
  c (ρ itself: a = S(0)T(00), a^k = S(0)T(0^{k+1}) ≠ 0); still
  plausible for c = 1 (co-isometric-A searches: zero hits) — BUT NOW
  IRRELEVANT:
- **GammaDischarge.lean (COMPILED FIRST TRY): every unit with value
  1 + s₁(z₋ + z₀) lies in stableUnits.**  Proof: (P) applied to the
  unit's own [0,1]-window value gives IsUnit(1 + s₁z₋); flipUnit
  gives the γ-partner g with value 1 + z₋s₁; inv_mem_levelSpan gives
  the balanced inverse; the double flip w₂ := flip(Y,s₁, g⁻¹·flip(u))
  exposes the pure tail and PureTailNilpotency supplies D; then the
  compiled gamma_reduction closes.  NO dynamics, NO A-nilpotency, NO
  swap cascade needed for this case.
- REMAINING GAP (the only one): NARROW → NORMAL FORM plumbing:
  every [−1,1]-window unit is mod-H equivalent to one with value
  1 + s₁z, z ∈ [−1,0]-window.  Inventory: exists_narrow_representative
  (compiled) gives the [−1,1] window; exists_corner_move (Φ-move,
  compiled) gives [u] = [s₀(u+vw)t₀ + s₀vt₁ + s₁wt₀ + s₁t₁];
  ResidualMoves (compiled) has blockDiagUnit/kill_move machinery;
  exists_prefix_kill + exists_corner_transport (compiled).
  Next: derive the funnel from the Φ-move: choosing v, w to make the
  2×2-corner-form 1 + s₁(·)-shaped — the sr1-pivot (compiled:
  exists_balanced_sr1_pivot) supplies the invertible block.

## Session 34b: the last gap is EXACTLY one termination measure
- With GammaDischarge + WidthTwoReduction compiled, the assembly gap
  reduces to: **[−1,1]-window unit → [0,1]-window unit mod H** (the
  residual c + s₁w forms are [0,1]-window, so WidthTwo covers them
  directly; GammaDischarge covers 1+s₁z, z ∈ [−1,0]).
- Φ-move funnel computations (v := 1, w := −X₋): relocates ALL
  negative content into the (1,0)-corner slot as s₁X₋t₀ — relocation
  only; iterating migrates it deeper (S(1^k)X₋T(0^k)), never kills.
- 3×3 mixed-depth-code E-op game: (1,3)/(3,1)-slots shift degrees by
  ±1, but the conservation law (deg P + deg Q = −1 vs slot-sum ≥ 0)
  blocks every single-split placement.  CONFIRMED yet again: only
  genuine content-kills advance; the compiled ones are the
  p-split/prefix kills (z ↦ zp₁ column-kills on 1+s₁z forms, any z).
- The κ₁-transport of a narrow unit gives 1 + s₁z with z ∈ [−2,0];
  the naive p-split → corner-transport cycle is exactly the identity
  (t₁s₁ = 1).  The cycle must be run with the KILL inserted:
  z ↦ zp₁ destroys z·p₀-content permanently; the corner transport
  then re-expands.  The termination measure must count column
  content across the cycle.  **NEXT SESSION: run the machine BFS
  (fixed verifier!) on 10 narrow units + ρ through the compiled
  move-set (p-splits, swaps, balanced pivots, incomparable
  unipotents, κ-transports, flips) and extract the decreasing
  measure from the machine-found witnesses.**  The ρ-cascade
  (σ-swaps by hand) is one data point; get ten more.

## Session 35: WIDTH-3 SOLVED — the swap/unipotent kill algorithm
Machine campaign (sound verifier): 9/9 random + 6/8 nasty narrow
units reduced to [0,1]-window by 1-3 H-moves; the two stragglers
reduce with depth-4 moves — witnesses reveal the complete mechanism:

**THE TWO KILLS** (for u with value 1 + A + c₀ + B, A = Σλᵢ S(xᵢ)T(yᵢ)
degree −1, WLOG all xᵢ ≠ ε by the padding identity
T(b) = Σⱼ S(j)T(b++j)):
1. UNIPOTENT KILL (right; left is mirror): for an A-monomial (x,y)
   with x incomparable to y, to every T-side of A−ν, and to every
   T-side of c₀ (the "supply condition"): u·(1 − λS(x)T(y)) has
   degree-(−1) part A − ν EXACTLY (junk c₀ν = 0, Aν = 0, deg-(−2)
   = 0, balanced junk Bν harmless).  Monomial count DROPS.
   [1 − λS(x)T(y) ∈ H: incomparable unipotent, COMPILED.]
2. SWAP CONVERT (left): for x-rooted A-content failing supply or
   with comparable sides: σ_{x,β}·u with β FRESH (deep, incomparable
   to x, to all S-sides of A and of c₀'s positive-depth part —
   exists since finitely many non-ε cylinders never cover depth
   |β| ≫ 0): (1−p_x) annihilates ALL x-rooted A-monomials
   ((1−p_x)S(xw) = 0); junk σ₋·(scalar μ of u₀) = μS(x)T(β) is ONE
   fresh monomial with incomparable sides satisfying supply
   (killable by move 1); σ₋·c₀-deep = 0 and σ₋A-deg-(−2) = 0 by
   freshness.  ρ's witness (swap(0,10) left, one move) is the
   μ = 0 special case.
**TERMINATION**: lexicographic (#A-monomials failing supply-or-
comparable, #A-monomials): move 2 strictly drops the first
coordinate (converts ≥1 bad to exactly ≤1 good); move 1 strictly
drops the second keeping the first at 0.  All moves ∈ H via
compiled certificates (signedSwap_mem, incomparable_unipotent).
THEN: [0,1]-window reached ⟹ WidthTwoReduction ⟹ H.  **This
completes NarrowReduction**: narrow → (this algorithm) → [0,1] → H.

LEAN PLAN (final modules):
- NegativePartKill.lean: (i) the padding-WLOG lemma (S-sides
  nonempty); (ii) the two kill lemmas as class-moves with their
  junk computations (pure word calculus + compiled H-certificates);
  (iii) the induction on the finite monomial family (represent A
  via a Finset of monomials with coefficients — use the span-
  induction-friendly formulation: ∃ list of monomials, induct on
  its length/badness); (iv) narrow_to_width2:
  every narrow unit ~mod-H a [0,1]-window unit.
- NarrowReductionProof.lean: assemble with
  exists_narrow_representative + window_zero_one_mem_stableUnits +
  ResidualReduction wiring → ScalarReduction → B4 unconditional.
- Then: docstring updates (STALE_DISCLAIMER×3), audit re-run
  (LAUNDERED_PROP/UNUSED clear once wired), README.
NOTE: user is now handling all compilation — I write, they build.

## Session 35b: honest junk audit — swap raising-part creates degree-2
- CORRECTION to session 35: the swap σ_{x,β} (left) has raising part
  −S(β)T(x), and S(β)T(x)·R hits R's x-comparable S-roots → degree-2
  junk.  Right-swaps have the mirror problem (y vs R's T-sides).
  The machine witnesses succeeded because junk cancelled per-instance
  or was re-killed by later moves — the clean "junk-free swap" needs
  a hypothesis we cannot always discharge.
- REVISED (final) PLAN:
  1. B2-all-N in Lean (units 1 + τ, τ ∈ span[1,N], are in H) via the
     session-30/33 block-move route — ALL ingredients compiled
     (transvection pullback, matrixRingEquiv/equal-depth transport,
     cornerDiag descent, WidthTwoReduction endpoint).  This absorbs
     ALL upward junk permanently.
  2. KillMoves.lean: unipotent_kill_step WRITTEN (exact value
     formula, supply hypotheses, class-iff — no sorry); swap lemma
     restated with honest junk formula (positive junk unconstrained,
     negative-side exactness): A_new = a' + S(x)T(β), positive part
     arbitrary-but-window-bounded.
  3. Induction on the COUNT of negative monomials with the 2-move
     macro (swap-convert then unipotent-kill nets −1 per round;
     positive window grows but B2 doesn't care).
  4. narrow → [0,≤N]-window → c-invertible ((P) generalized: hmm —
     (P)-Lean is N = 1 only!  For the assembly, after killing ALL
     negatives we land in [0,N]: split u = c(1+τ) needs (P)-N.
     EITHER extend ZeroKOne to general N (grouped-coefficient
     remainder vector — session-29 math) OR note c = 1-preserving:
     the kill moves shift c only by junk... simplest: B2 handles
     1 + τ directly; for general c + τ: rank-normalize c and rerun —
     NO: cleanest is (P)-N.  Add ZeroKOneN to the plan (the Lean
     induction upgrades hclaim to a remainder VECTOR indexed by the
     N shifts; rank argument unchanged).
  Order of writing: B2 (BlockMoveTailKill.lean), ZeroKOneN,
  KillMovesSwap, NegativePartInduction, NarrowReductionProof,
  assembly + docstrings.

## Session 36: BlockMoveTailKill.lean WRITTEN (B2, all N)
- pure_positive_tail_mem_stableUnits: units 1 + τ, τ ∈ span[1, N+1],
  are in stableUnits — plain induction on N.  Base: WidthTwo.
  Step: top-component split via exists_components + Icc-insert;
  branch coefficients q_i := t_i·η; corner embed κ at word 00
  (pairKappaUnit, value 1 + S(00)τT(00)); multipliers
  m₂ := (1 − S(00)s₀T(01))(1 − S(00)s₁T(10)),
  m₁ := (1 + S(01)q₀T(00))(1 + S(10)q₁T(00)) — products of compiled
  incomparable unipotents, cross terms die by T(0i)S(00) = 0 /
  T(00)S(i0) = 0; the 18-term expansion of m₂·κ·m₁ collapses
  (X_iK = KY_i = X₀Y₁ = X₁Y₀ = 0; X₀Y₀ + X₁Y₁ = S(00)ηT(00) via the
  completeness split) to value 1 + S(00)aT(00) − X₀ − X₁ + Y₀ + Y₁
  with tail ∈ span[1, N] — IH closes; assembly through κ·u⁻¹ ∈ H.
- All negation isolated (m₂-value via -(s i)-middle in
  incomparableUnit; no mid-product sub before distribution lemmas).
  Cast discipline: window top stated as (N : ℤ) + 1; succ-case
  normalizes ↑(N+1)+1 → ↑N+2 once at entry.
- Registered in aggregator.  Awaiting user's compile.
- REMAINING WRITES: ZeroKOneN (grouped-coefficient (P) for [0,N] —
  needed to factor c out before B2 in the assembly);
  NegativePartInduction (the kill-move induction, needs the honest
  swap lemma with positive junk); NarrowReductionProof + B4 wiring;
  docstrings.

## Session 37: THE WIDTH-3 PROOF IS COMPLETE
**Theorem (W3).** Every narrow unit lies in the diagonal class group.
Proof structure (every move compiled or in written modules):
0. GENERALIZED B2 (upgrade of BlockMoveTailKill, same proof): every
   unit with value in span[0, N] is in H — the block-move step never
   used balanced-part = 1: with value v, κ-value = 1 + S(00)(v−1)T(00)
   and the same X/K/Y collapse lands in span[0, N−1].  Induction to
   N = 1 = WidthTwo.  ⟹ ZeroKOneN IS UNNECESSARY.
1. κ₀₀-TRANSPORT (compiled): [u] = [1 + S(00)(↑u−1)T(00)] puts ALL
   content in the 00-corner: S-sides and T-sides ⊆ 00-cylinder.
   ⟹ INFINITE FRESHNESS SUPPLY: all fresh words chosen in the
   1-cylinder, pairwise-disjoint across rounds.
2. THE MACRO (one round, kills all x-rooted negative monomials):
   for x an S-side root of the negative part A:
   (a) LEFT swap σ_{x,β}, β fresh: (1−p_x) annihilates all x-rooted
       A-monomials ((1−p_x)S(xw) = 0; β-incomparable-to-x extends to
       all x-rooted words); adds ONE monomial λ'S(x)T(β)
       (λ' = 1 + scalar-part, may vanish); junk: balanced
       −S(β)T(x)A-terms and positive; NO deg-(−2) (T(β)S-sides = 0
       by freshness).
   (b) RIGHT swap σ_{v,β}, v fresh: refreshes the S-side:
       λ'S(x)T(β) → S(v)T(β) (A'p_β = 0 freshness; junk S(β)T(v) is
       degree +1; all probes hit fresh v ⟹ vanish).
   (c) RIGHT unipotent kill of S(v)T(β) (KillMoves lemma):
       supply UNCONDITIONAL — A'·ν and C·ν probe T-sides against
       fresh v: zero.  NO resurrection: the balanced junk from (a)
       has OLD T-sides; right-mults probe T-sides only.
   Net: |A| drops by |A_x| ≥ 1.  Comparable and supply-blocked
   monomials handled uniformly (the swap kill needs NO
   incomparability of the monomial's own sides).
3. Induction on the negative monomial count (list-representation of
   A) ⟹ value ∈ span[0, N] ⟹ generalized B2 ⟹ H.
KEY DISCOVERIES en route: the resurrection channel (left-kill of the
fresh monomial hits S(β)T(x)A junk giving back p_xA — hence the
S-side REFRESH step (b)); covering obstruction for freshness (S-sides
can cover the tree — hence the κ-corner transport step 1).
REMAINING LEAN: (i) upgrade BlockMoveTailKill statement to
span[0,N]-values (small); (ii) SwapKill.lean: the two swap-step value
formulas ((a) and (b), word calculus, hypotheses = freshness
incomparabilities); (iii) NegKillInduction.lean: list-induction over
the negative part with the macro; (iv) NarrowReductionProof +
B4/docstrings.  NO other mathematics remains.

## Session 37b: generalized B2 written; swap-macro post-mortem; ρ anatomy
- WindowNonnegReduction.lean WRITTEN (built from the user's fixed
  BlockMoveTailKill by systematic transform, incorporating their
  abel-fix, hK-fold fix, and base-case fix): **every unit with value
  in span[0, N] is in stableUnits** — the block move never needs the
  balanced part invertible.  ZeroKOneN permanently unnecessary.
- GammaDischarge is actually SUBSUMED by window_zero_one (its value
  1 + s₁z₋ + s₁z₀ lies in span[0,1]!) — keep as milestone, note for
  the audit's redundancy pass.
- SWAP-MACRO POST-MORTEM (3 failed repairs, each by the conservation
  daemon): (i) left-kill of the fresh monomial resurrects p_xA via
  the σ's S(β)T(x)A junk; (ii) the S-side-refresh second swap's
  −p_v junk shields the kill (net zero); (iii) the balanced-swap
  refresh's S(x)T(v) half resurrects via the kill.  LESSON: swaps
  are invertible conjugations — content genuinely dies ONLY in
  fully-supplied unipotent kills.
- ρ-WITNESS ANATOMY (exact recompute): over 𝔽₂ the unsigned swap
  contains 1 + p_x which annihilates x-rooted content BY DUPLICATION;
  ρ has NO scalar part, so no fresh monomial appears; and the machine
  chose β = 10 COMPARABLE to content so σ₋-junk collapsed into
  balanced terms (T(10)S(10) = 1).  The machine plays 𝔽₂ billiards —
  not a formalizable uniform strategy.
- STRATEGIC RESET for the remaining gap ([−1,1] with genuine negative
  part): write the MIRROR CHAIN (mechanical mirrors of compiled
  proofs, xw-side): mirror-(P) → mirror-PureTail → mirror-WidthTwo →
  mirror-window-nonneg ⟹ [−N, 0]-window units die.  Then the final
  mixing question is sharply: value = c + A + B with A ≠ 0 ≠ B, and
  the two one-sided theorems + abelian Units/H available.

## Session 37c: the endgame statement — Bruhat/LPU over the tree
With both one-sided theorems (nonneg compiled-track + mirror chain to
write) and V-elements ∈ H (swaps + 3-cycles; Higman–Thompson
generation), the remaining gap is exactly:
**(LPU) every narrow unit factors mod H as
  (nonneg-window unit)·(V-element)·(nonpos-window unit)** —
the Leavitt/tree analog of banded-operator triangular factorization
(the V-pivot absorbs the band's index, cf. the conservation law).
Attack: strip the bottom degree: rank-normalize A_{−M} to a canonical
partial isometry τ_r (compiled machinery), multiply by the matching
rebalancer ω_r ∈ H; bookkeeping of what re-enters the bottom is the
termination question — weighted-depth measure candidate.
This is classical-shaped (Birkhoff via Gauss with pivots).  Next
session: (1) write the mirror chain (mechanical, ~4 modules:
mirror-(P) via xw-side, mirror-PureTail, mirror-κ-transport pieces,
mirror-WidthTwo/window-nonpos); (2) prove LPU by bottom-stripping
with the weighted measure; (3) V-generation lemma; (4) assembly.

## Session 38: the θ-route — mirror chain in THREE files, all written
- OppositeTranspose.lean: oppositeFamily (op-ring carries the family
  with s↔t; relations via op_mul reversal); θ := lift(oppositeFamily
  (family k)); θ̂ := unop∘θ with add/mul-anti/one/zero/smul/sub
  lemmas; generator exchange (lift_generator); word reversal
  θ̂(S(a)) = T(a); adjoin_generators_eq_top (mkAlgHom_surjective +
  FreeAlgebra.adjoin_range_ι + map_adjoin); INVOLUTION via
  adjoin_induction; WINDOW FLIP span[lo,hi] → span[−hi,−lo];
  thetaUnit.
- ThetaStable.lean: thetaMat := entrywise-θ̂ transpose;
  anti-multiplicativity (mul_apply + thetaHat_sum);
  thetaMat_single; thetaMatUnit; closure transport
  (Subgroup.closure_induction: transvections ↦ transposed
  transvections, products reverse — subgroups don't care);
  thetaMatUnit_diagUnit (diagonal is transpose-fixed);
  **thetaUnit_mem_stableUnits_iff** (both directions via involution).
- WindowNonposReduction.lean: [−N,0]-window units ∈ H, three-line
  transport through window_nonneg.
- All registered.  This replaces the planned 4-module mechanical
  mirror chain (mirror-(P), mirror-PureTail, mirror-WidthTwo,
  mirror-nonneg) with one anti-automorphism — and transports ANY
  future one-sided theorem for free.
- REMAINING: the mixing step (narrow with both signs → product of
  one-sided factors mod H: the LPU statement) + V-generation +
  NarrowReduction assembly + docstrings.

## Session 38b: THE MIXING CASE IS SOLVED — the Ω-intertwiner argument
**Theorem (final gap).** Every narrow unit u (value A + c + B,
A ∈ span[−1,−1], B ∈ span[1,1]) lies in H·[V], hence in
centralClassGroup once V-elements are certified in H.
PROOF:
1. Rank-normalize A to the canonical partial isometry
   τ = Σ_{i<r} S(aᵢ)T(bᵢ) (|a|=m, |b|=m+1, orthonormal families) by
   balanced H-units (rectangular pivot — small new lemma).
2. THE INTERTWINER: complete {bᵢ} and {aᵢ} to full prefix codes with
   a bijective pairing whose degree profile is ⊆ {0, +1}: exactly r
   completion pairs of degree +1 (volume bookkeeping:
   Σ 2^{−|a'|}(1−2^{−d}) = r·2^{−m−1} is satisfiable with r
   degree-1 pairs and the rest degree-0), with ALL completion pairs
   (b'ⱼ, a'ⱼ) chosen FRESH: mutually incomparable and incomparable
   to every S/T-side of the value.  Ω := Σ S(a-code)T(b-code), a
   V-element (code-change unit).
3. u·Ω⁻¹ computation: τ·Ω⁻¹ = Σ p_{aᵢ} (balanced!); the negative
   part of u·Ω⁻¹ is EXACTLY c·(degree-(−1) part of Ω⁻¹) =
   Σⱼ (c-column content)·S(b'ⱼ)T(a'ⱼ):
   - c singular: place the degree-1 completion pairs in the FREE
     columns (Sᶜ, refined deep) ⟹ negative part ZERO outright.
   - c = 1 (invertible, normalized): the negative part is the r
     FRESH canonical monomials S(b'ⱼ)T(a'ⱼ) themselves — both sides
     fresh ⟹ the unipotent kills are FULLY SUPPLIED (hasup, hcsup
     hold against all content by construction; no resurrection).
   Either way: u·Ω⁻¹ ~ nonneg-window unit ⟹ ∈ H (compiled).
4. Hence [u] = [Ω]; Ω ∈ H by the V-GENERATION LEMMA: refine to a
   common deep code, factor into incomparable transpositions
   σ (compiled ∈ H) with 3-cycles through incomparable spares for
   comparable moves (Higman's induction on code size).
REMAINING LEAN (fully specified, no open math):
  (a) rectangular rank normal form for degree-(−1) parts;
  (b) the Ω construction + the u·Ω⁻¹ value computation + kills;
  (c) V-generation (induction on codes);
  (d) NarrowReduction assembly → ScalarReduction (wiring compiled)
      → B4 → Theorem C; docstrings; audit.

## Session 38c: V-GENERATION PROOF (the last open item, now closed)
**Lemma.** For complete prefix codes {cᵢ}, {dᵢ} of equal size, the
code-change unit Ω = Σᵢ S(dᵢ)T(cᵢ) lies in H.
PROOF (induction on code size, all steps formalization-friendly):
1. RE-REPRESENT: pad each pair equally (S(d)T(c) = Σ_γ S(dγ)T(cγ))
   so the SOURCE code is the full depth-D code (element unchanged!).
2. SIBLING-PAIR EXISTENCE: any complete prefix code of size ≥ 2
   contains a sibling pair at maximal depth (the sibling of a
   maximal-depth element must itself be in the code: an ancestor
   would violate prefix-freeness).  Classical, 10-line proof.
3. ALIGN: right-multiply by a permutation of the (full) source code
   and left-multiply by a permutation of the target code — both are
   products of transpositions of same-code elements, which are
   pairwise incomparable, so each σ ∈ H (COMPILED) — to place a
   target sibling pair over a source sibling pair.
4. MERGE: S(ev0)T(w0) + S(ev1)T(w1) = S(ev)T(w) (the completeness
   relation).  Both codes shrink by one; induct.  Size 1: Ω = 1.
Composition law Ω_{e,d}·Ω_{d,c} = Ω_{e,c} available throughout.
**NO OPEN MATHEMATICS REMAINS.**  Full endgame stack:
  narrow (compiled width-reduction)
  → A-rank-normalization (rectangular pivot lemma, to write)
  → Ω-intertwiner with {0,+1} degree profile & fresh completions
    (session 38b; to write)
  → u·Ω⁻¹: negative part = r fresh fully-supplied monomials
    → KillMoves (COMPILED) → nonneg window → dies (COMPILED)
  → [u] = [Ω], Ω ∈ H (this lemma; to write)
  → NarrowReduction → ScalarReduction (COMPILED wiring) → B4
  → Theorem C unconditional; docstrings; audit.

## Session 39: CodeChangeInfrastructure.lean written
- IsCompleteCode (list-based: pairwise incomparability + cylinder
  sum = 1); wordS_ne_zero; exists_max_length_mem (list induction);
  exists_term_mul_ne_zero (sum-kill helper);
  merge_identity_one (s_{v0}t_{w0} + s_{v1}t_{w1} = s_v t_w);
  IsCompleteCode.incomp (Pairwise.forall with symmetry);
  **exists_sibling_pair** (max-depth element m = w++[a]; m ≠ ε via a
  second element + nil_prefix; completeness × wordS-nonzero forces a
  code element comparable to the sibling w++[b]; length bookkeeping
  pins it to equal the sibling; proper-prefix branch contradicts
  prefix-freeness through v <+: w <+: m);
  signFlip (1 − 2p_b as p+p, self-inverse via idempotency + abel);
  signFlip_mem (balanced value in levelSpan b.length);
  cylTransposition := signFlip · signedSwap ∈ H with value
  1 − p_a − p_b + s_at_b + s_bt_a (the p_b-collapse calc).
- Registered.  NEXT: CodeChangeUnits.lean — the generation induction:
  code-change units Ω_{d,c} := Σ S(dᵢ)T(cᵢ) ∈ H by induction on
  length, using: sibling pairs on both sides, ≤3 cylTransposition
  multiplications to align the pairing, merge_identity_one to drop
  to length−1, composition law Ω_{e,d}Ω_{d,c} = Ω_{e,c}.
  Then: rectangular pivot; the Ω-intertwiner narrow-reduction;
  assembly.

## Session 39b: CodeChangeSwap.lean written; generation-induction design
- pairValue (list of (target, source) pairs), perm-invariance;
  swapWord; cylTransposition_mul_term (the three-branch collapse
  computation: t = x ↦ y, t = y ↦ x, incomparable ↦ fixed);
  cylTransposition_mul_pairValue (list version).  Registered.
- MAIN INDUCTION DESIGN (CodeChangeUnits.lean, next write):
  theorem: ∀ n P, P.length = n → IsCompleteCode (P.map .snd) →
    IsCompleteCode (P.map .fst) → ∀ u, ↑u = pairValue P → u ∈ H.
  n = 0: complete-empty impossible (0 = 1 vs Nontrivial).
  n = 1: cylinder w = 1 forces w = ε (else the opposite-letter word
    kills it: p_w = 1 ⟹ S(other) = p_w·S(other)·... contradiction
    via wordT_mul_wordS_of_incomparable + wordS_ne_zero);
    both codes = [ε]: value = 1: u = 1 ∈ H.
  n ≥ 2: source siblings (w0, w1) via exists_sibling_pair on
    (P.map .snd); extract their pairs to the head via
    List.perm_cons_erase twice (pairValue-perm-invariant; the pair
    containing w1 survives the first erase since sources are
    distinct); target siblings (v0, v1) on (P.map .fst);
    ALIGN with ≤2 cylTransposition multiplications (4 by_cases on
    x = v0 / y' = v1, using the transposition-mul-pairValue lemma;
    all targets pairwise equal-or-incomparable since they form a
    prefix-free code — IsCompleteCode.incomp);
    MERGE via merge_identity_one: pairValue ((v0,w0)::(v1,w1)::Q) =
    pairValue ((v,w)::Q); new codes complete (cylinder sum unchanged
    by the merge identity; prefix-freeness of the merged word by the
    10-line children argument); IH at n−1; unwind the ≤2
    transposition units (∈ H via cylTransposition_mem).
- After that: rectangular pivot lemma; the Ω-intertwiner
  narrow-reduction (session 38b design); assembly.

## Session 40: CodeChangeUnits.lean — THE V-GENERATION THEOREM WRITTEN
- codeChange_mem_stableUnits: for pair lists P with both projections
  complete prefix codes, any unit valued Σ S(tᵢ)T(sᵢ) is in H.
  Strong induction on |P|:
  n = 0: completeness gives 0 = 1, absurd.  n = 1: cylinder = 1
  forces ε (eq_nil_of_cylinder_eq_one via the opposite first letter),
  value = 1.
  n = m+2: source siblings extracted to the head via perm_cons_erase
  (twice, mem_erase_of_ne); hypotheses transported (IsCompleteCode.
  perm, pairValue_perm); target siblings from exists_sibling_pair;
  TWO alignSteps (uniform id-or-transposition, alignStep_mul_pairValue
  handles both) sending head targets to (v0, v1) — the key
  distinctness hv0y₁ by three-way case analysis on swapWord;
  target-code completeness maintained via map_swapWord_perm
  (nodup + membership); explicit head structure hP₂struct; MERGE via
  merge_identity_one; merged codes complete via IsCompleteCode.merge
  (children-prefix argument + cylinder-sum preservation); IH at m+1;
  unwind with alignStep_mem + group.
- Supporting: swapWord_self/left/right/other; map_swapWord_perm
  (erase-erase decomposition, fixes off-support, Perm.swap);
  eq_nil_of_cylinder_eq_one; alignStep (dependent-if unit) + action
  + membership; IsCompleteCode.{nodup, perm, merge}.
- User is live-fixing binder/deprecation issues in parallel
  (Perm.pairwise_iff symmetry witness inline — thanks!).
- REMAINING WRITES: rectangular pivot; the Ω-intertwiner narrow
  reduction (session 38b); NarrowReduction/B4 assembly; docstrings.

## Session 41: Ω-argument full degree-audit — simplification AND a gap
POSITIVE (real, keeps): **the rectangular pivot is unnecessary.**
Column-canonicalization of the negative part comes from the COMPILED
balanced rank normal form via the squaring trick:
  Â := s₀·A is balanced; g·Â·h = E := Σ_{γ∈S} p_γ;
  then A·h = t₀·g⁻¹·E  (A = t₀s₀A = t₀Â — three lines).
So mod a right H-unit, A = t₀·M·E-form with M balanced: its COLUMN
code is the canonical S-cylinder family.  One-sided suffices.
NEGATIVE (gap in session 38b, found by full degree bookkeeping):
after the κ-corner transport and the profile-balanced Ω
(deg-(−1) pairs 00γ→1γ, deg(+1) pairs 1γ→01γ, deg-0 rest at common
depth D = n+2 — sizes match exactly at that depth!), the value·Ω⁻¹
computation gives negative part = Σ_γ S(1γ)T(01γ) from the scalar,
BUT the balanced image Ã·Ω⁻¹ = Σ (WS(γ))T(1γ) has T-sides exactly
{1γ} — the kill of S(1γ)T(01γ) fails hcsup there, and the kill
formula replaces the monomial by (WS(γ))T(01γ); summed:
new-negative = W·E_S·T(01) vs old Ã = W·E_S·T(00) — A PURE CORNER
ROTATION, zero net progress (conservation in purest form).
Also: the c-singular free-column supply is NOT joint-free in general
(relative column positions are invariant under one-sided moves).
STATUS: the mixing case ([−1,1] with both signs) is STILL OPEN.
What IS newly available and free: the θ-transported mirror of
GammaDischarge (units 1 + z·t₁, z ∈ span[0,1] are in H — three-line
transport), and the t₀ME-structure of the negative part.
SHARPEST REMAINING QUESTION: units with value 1 + t₀M·E + C + B
(M balanced-unit-times-cylsum): kill the t₀-column.  All conserved
quantities identified; the un-conserved handle must involve the
INTERPLAY (the unit equations), as in (P)'s proof — likely a second
shape-rank argument on the mixed system, not a move-hunt.

## Session 41b: TriangularFactorization.lean — the frontier is ONE Prop
- TriangularFactorization k (Prop): every narrow unit factors as
  (nonpos-window unit)·(code-change unit)·(nonneg-window unit).
- narrowReduction_of_triangularFactorization: the factorization
  implies NarrowReduction — each factor dies by a compiled/written
  theorem (window_nonpos [θ-transport], codeChange_mem_stableUnits
  [session 40], window_nonneg [block-move]) — hence ScalarReduction,
  B4, GL₂ = EL₂ etc. all follow through the COMPILED
  ResidualReduction wiring.
- THE ENTIRE FORMALIZATION IS NOW ASSEMBLED MODULO EXACTLY ONE NAMED
  STATEMENT: TriangularFactorization k — the Birkhoff/LPU
  factorization over the binary tree (session 37c; the honest
  remaining mathematics after session 41's audit killed the 38b
  shortcut).  Proof route: level-wise Gaussian elimination on the
  tower with code-change pivots (banded-operator triangular
  factorization); the compiled complement/section machinery
  (StableRankOne) and the shape calculus are the intended tools.
- Registered in aggregator.

## Session 42: RANK-ONE NORMAL FORM — the negative part is ONE monomial
**Breakthrough.** The stable block move with P := A (the whole
degree-(−1) part) and Q := 1 needs NO invertibility: through the
mixed-depth code {00, 01, 1},
  v̂ := (1 − S(00)·a·T(1)) · κ₀₀(u) · (1 + S(1)T(00))
has value  [1 + S(00)(z−a)T(00) − S(00)aT(1)]  +  S(1)T(00),
i.e. a [0,1]-window element plus the FIXED universal monomial
s₁t₀₀ — verified by direct hand computation (the cross terms die by
T(00)S(1) = 0, T(1)S(00) = 0; the T(1)S(1) = 1 collapse performs the
A-kill).  Both multipliers are compiled incomparable unipotents; the
corner embedding is compiled pairKappa.
**RankOneNormalForm.lean WRITTEN** (exists_rank_one_normal_form,
with the two-way stableUnits equivalence).  Registered.
THE REMAINING QUESTION IS NOW (Q): units with value w + s₁t₀₀,
w ∈ span[0,1], lie in central·H.  Notes toward (Q):
- naive kills/code-changes rotate (computed: the S(00)aT(1)-junk
  resurrects A; ρ-style Ω rotates the monomial corner);
- if w is invertible ((P)-rank-one analog — OPEN), then
  [v̂] = [1 + W⁻¹s₁·t₀₀] and the flip gives [1 + t₀₀W⁻¹s₁] — window
  of W⁻¹ uncontrolled either way;
- (Q) is (P)'s sibling: a shape-rank/graded-equation analysis of
  units W + N with N the fixed rank-one lowering monomial.  The
  inverse's graded equations now have the SPECIFIC N with N² = 0,
  N = s₁t₀₀: very rigid.  ATTACK NEXT: mimic ZeroKOne — normalize
  w's balanced part, corner system, but keep N as a known pivot.
TriangularFactorization now follows from (Q) + this module (much
weaker than full Birkhoff!) — next session: derive (Q) or replace
TriangularFactorization by the (Q)-form as the named frontier.

## Session 42b: STRUCTURE THEOREM for nonneg narrow units
NonnegUnitStructure.lean WRITTEN:
- nonneg_narrow_unit_structure: every unit with value in span[0,1]
  equals c·(1+η) with c invertible balanced (balanced inverse cinv,
  via balanced_component_isUnit = compiled (P) + rank normal form +
  inv_mem_levelSpan_of_val_mem) and η pure-degree-1 NILPOTENT
  (pure_tail_nilpotent).
- nonneg_narrow_unit_inv_window: inverses of [0,1]-window units have
  NONNEG windows (truncated geometric series (Σ(−η)^i)·cinv, via
  geom_sum_mul; explicit inverse formula proved by left-inverse
  uniqueness).
This is the rigorous UPPER-TRIANGULAR LEG of Birkhoff.  θ-transport
gives the lower leg for free when needed.
CONSERVATION SHARPENED (derivation this session): for ANY block-move
family, deposits P at (1,j)/Q at (j,1) must share the block pair, so
deposit degrees sum to deg P + deg Q = −1 — one deposit is always
negative; multi-pair splits ΣPᵢQᵢ with all deposits nonneg force
window(ΣPᵢQᵢ) ≥ 0 ≠ deg(−1).  Hence the rank-one normal form
(single monomial S(1)T(00) deposit with scalar 1) is OPTIMAL within
stable elementary moves; (Q) requires using the unit structure of w.
ANSATZ RESULT for (Q): v = w + s₁t₀₀ factors as
(1 + s₁·y·t₀₀)·(nonneg unit)  ⟺  y·(t₀₀·c) = t₀₀ solvable with y
balanced (c := balanced part of w; the quadratic term dies via
t₀₀s₁ = 0!).  Solvable ⟺ V₀·c = V₀ at some level (V₀ := rowspace of
t₀₀, i.e. the 00-corner coordinate subspace).  c = 1 case: y = 1 ✓
(v = 1+N unipotent).  General c fails ⟹ the code-change factor Ω is
genuinely needed exactly when V₀·c ≠ V₀: Ω must move the defect of
the 00-corner flag under c into position.  NEXT: use unit-ness of v
(graded equations c x₀ + b x₋₁ + N x₁ = 1 etc. + the structure
theorem) to prove the corrected flag condition is always reachable
in the H-orbit {g·v·g′} — the last mathematical gap.

## Session 42c: THE SCALAR-PENCIL REDUCTION (derived, not yet formalized)
Level-n corner recoding linearizes every narrow unit COMPLETELY:
for v = a + c + b narrow with all parts representable at level n,
the 2^n × 2^n block matrix V[i,j] := t_i · v · s_j (|i| = |j| = n) has
  t_i c s_j = C[i,j] · 1          (SCALAR — c balanced at level n),
  t_i b s_j = Σ_x B[i·x, j] s_x   (k-combination of s₀, s₁ only),
  t_i a s_j = Σ_x A[i, j·x] t_x   (k-combination of t₀, t₁ only).
So v ≅ the PENCIL  V = A₀t₀ + A₁t₁ + C + B₀s₀ + B₁s₁  with SCALAR
matrices A₀, A₁, C, B₀, B₁ ∈ M_{2^n}(k), invertible over M_m(L).
H-transport: M_m(L)-elementary ops (arbitrary L off-diag entries) and
GL_m(k) row/col ops are all stable-elementary = compiled H-moves.

INFLATION (one more corner level, m → 2m), computed exactly:
  t₀ ↦ [[t₀,0],[t₁,0]], t₁ ↦ [[0,t₀],[0,t₁]], 1 ↦ I₂,
  s₀ ↦ [[s₀,s₁],[0,0]], s₁ ↦ [[0,0],[s₀,s₁]] (entrywise recoding), so
  Â₀ = [[A₀,A₁],[0,0]], Â₁ = [[0,0],[A₀,A₁]], Ĉ = diag(C,C),
  B̂₀ = [[B₀,0],[B₁,0]], B̂₁ = [[0,B₀],[0,B₁]].
C = 0 is inflation-stable.

ELIMINATION STEP (Smith on C): GL_m(k) both sides → C = diag(I_r, 0);
the scalar pivots I_r clear ALL other L-entries in their rows and
columns via elementary H-ops → V ~ diag(I_r, V′) with V′ an
(m−r)-pencil with C′ = 0, still invertible.
CRUX (the whole remaining problem, now finite-dimensional):
  (Q-pencil, C = 0): classify invertible pencils
  A₀t₀ + A₁t₁ + B₀s₀ + B₁s₁ over M_m(k) up to GL_m(k)·(inflation)·
  (elementary H): show they reduce to direct sums realizing
  code-change units (⟹ TriangularFactorization ⟹ K₁ = 0).
Facts derived: pure-t and pure-s pencils are NEVER invertible
(m = 1 checked; grading argument general); m = 1 C = 0 pencils are
never units (to verify); code-change units have C ≠ 0 in general
(every complete-code bijection with only ±1 length shifts must
contain a balanced pair — dyadic mass equation P = 2/3 obstruction;
unbalanced-only code-changes exist but need mixed shift sizes ±2 at
staggered depths).
NEXT SESSION: (1) python-verify the pencil recoding + elimination on
ρ and on v̂ of random narrow units (leavitt_search.py stream solver);
(2) solve (Q-pencil): likely via the "column space filtration"
argument — B̄ := [B₀;B₁] : k^m → k^{2m} and Ā := (A₀,A₁) : k^{2m} → k^m
with invertibility forcing exact interlocking (Fredholm/dimension
count: rank conditions per inflation level stabilize), then peel
rank-1 code-change pivots; (3) formalize: PencilTransport.lean
(corner recoding ≅ + H-transport), PencilElimination.lean (Smith +
clearing), PencilClassification.lean ((Q-pencil)) → discharge
TriangularFactorization.

## Session 42d: (Q-pencil) constraints derived
For V = A₀t₀ + A₁t₁ + B₀s₀ + B₁s₁ (C = 0) invertible over M_m(L):
1. PARITY: V has only odd degrees ⟹ V·X_even = 0 ⟹ X := V⁻¹ is
   supported on ODD degrees only.
2. If 𝔅 := [B₀;B₁] (2m×m scalar) had full column rank m, the top
   equation B∘X_T = 0 (T ≥ 1) kills X_T (left-multiply by t_y and use
   a scalar left inverse of 𝔅), forcing X = X_{−1} pure; then the
   balanced part of V·X_{−1} = 1 splits over the M₂-corner blocks
   into  Bᵢ·Ξⱼ = δᵢⱼ·I_m  (Ξⱼ := X_{−1}sⱼ ∈ M_m(L₀)), i.e.
   𝔅·(Ξ₀|Ξ₁) = I_{2m} — impossible: row-reduce 𝔅 by G ∈ GL_{2m}(k)
   to put ≥ m zero rows; those rows of G·I_{2m} can't be zero.
   CONCLUSION: rank 𝔅 < m, and dually rank(A₀|A₁) < m (row rank),
   via the mirrored bottom equations on X·V = 1.
3. Hence ∃ v ≠ 0 with B₀v = B₁v = 0: column V·v = (A₀v)t₀ + (A₁v)t₁
   is PURE-t (and dually a pure-s row) — the Kronecker
   minimal-index chains begin.  Expected endgame: induction peeling
   Kronecker chains until the pencil is a direct sum of shift blocks
   = pencil forms of unbalanced code-change units; each peel uses a
   stabilized block move (the pure-t column as P with its scalar
   content pivoted by GL_m(k)).
Everything in 1–2 is elementary and formalizable with the compiled
graded-component machinery.  NEXT: finish the peeling induction
(does a pure-t column always split off a shift block after
inflation?), python-check on random invertible C = 0 pencils
(construct from unbalanced code-changes, e.g. shifts +2/−2 at
staggered depths), then formalize the pencil pipeline.

## Session 43: (Q-pencil) SOLVED — complete elimination proof
Setting: V invertible p×q matrix over L, every entry in
k-span{t₀,t₁} ⊕ k ⊕ k-span{s₀,s₁}; write V = A₀t₀ + A₁t₁ + C +
B₀s₀ + B₁s₁ with SCALAR A_z (p×q), C, B_z.  Rectangular allowed
(L^p ≅ L^q via Leavitt).  Two master objects:
  τ_q := [t₀I_q; t₁I_q]  (2q×q):  τ_q'τ_q = I_q (p₀+p₁=1),
         τ_qτ_q' = I_{2q} (t_zs_w = δ_zw), τ_q' := (s₀I_q | s₁I_q).
  ς_a := (s₀I_a | s₁I_a) (a×2a):  ς_aς_a† = I_a, ς_a†ς_a = I_{2a},
         ς_a† := [t₀I_a; t₁I_a].
KEY FACTORIZATION: any pure-t block T' = A₀'t₀+A₁'t₁ = (A₀'|A₁')·τ
with τ two-sided invertible ⟹ T' left-invertible over L ⟺ the
horizontal scalar concat (A₀'|A₁') has FULL COLUMN RANK (rank
argument both ways; scalar left-inverse composed with τ').  Dually
pure-s S' right-invertible ⟺ [B₀''; B₁''] vertical stack full ROW
rank (θ-transpose duality).

STEP 0 (Smith on C): GL(k) two-sided → C = diag(I_r, 0); scalar
pivots clear their rows/cols by elementary L-ops → V ~ I_r ⊕ V',
V' invertible with C' = 0.  [For square m×m narrow-unit pencils.]

STEP 1 (parity): C'=0 ⟹ X := V'⁻¹ supported on ODD degrees.

STEP 2 (branch dichotomy): top equation ((B∘X)_top = 0, strip with
t_y) and bottom (X_bot·(A-part) = 0, strip with s_w):
 (b) if 𝔅 := [B₀;B₁] (2p×q) full column rank: X = X_{−1} pure
     deg −1; corner-split of VX=1 gives B_aΞ_b = δ_ab I_p where
     Ξ_z := X_{−1}s_z, i.e. 𝔅·(Ξ₀|Ξ₁) = I_{2p}, and XV=1 deg-0
     gives Ξ₀B₀+Ξ₁B₁ = I_q ⟹ q = 2p, 𝔅 ∈ GL_{2p}(k), Ξ scalar
     = arrangement of 𝔅⁻¹; deg −2 equations kill A: X = G·τ_p
     (G scalar invertible) ⟹ V = ς_p·G⁻¹ ~ ς_p.  TERMINAL.
 (c) mirror (Ā := (A₀|A₁) p×2q full row rank): V ~ G'·τ_q.  TERMINAL.
 (d) both: X pure deg−1 AND pure deg+1 ⟹ X = 0 absurd. VACUOUS.
 (a) both deficient: rank 𝔅 < q and row-rank Ā < p: proceed.

STEP 3 (block extraction, branch (a)): right-GL: ker𝔅 = last
q−β coords (β := rank𝔅) → cols > β PURE-t; left-GL: coker rows →
rows > α PURE-s (α := row-rank Ā); zero block (rows>α)×(cols>β).
Invertibility blocks of X give: T' (α×(q−β) upper part of pure-t
cols) LEFT-invertible ⟹ (A₀'|A₁') full column rank 2(q−β) ≤ α;
S' ((p−α)×β) RIGHT-invertible ⟹ [B₀'';B₁''] full row rank
2(p−α) ≤ β.  Normalize: left-GL_α: (A₀'|A₁') = [I_{2b}; 0]
(b := q−β) → t-cols become [τ_b; 0]; right-GL_β: [B₀'';B₁'']G =
[I_{2a}|0] (a := p−α) → s-rows become (ς_a | 0 | 0).

STEP 4 (elimination): column-op (block unipotent, sources cols>β,
targets cols≤β, DISJOINT sets ⟹ product of incomparable
unipotents = 1 − Σ s_i x t_j ∈ H): subtract τ_b·(τ_b'·Y) — kills
rows 1..2b of cols ≤ β entirely (τ_bτ_b' = I_{2b}).  Row-op with
ς_a: kills cols 1..2a of rows ≤ α (ς_a†ς_a = I_{2a}); no
interaction (multipliers vanish on already-cleared rows).  Result
after permutation: V' ~ τ_b ⊕ M̃ ⊕ ς_a with M̃ ((α−2b)×(β−2a))
invertible (block-diagonal inverse argument using one-sided
inverses of τ, ς to kill off-diagonal blocks of the inverse),
C(M̃) = 0.  Sizes strictly decrease ⟹ RECURSE (rectangular).
Bases: 0×0 ✓; p×0/0×q force p=q=0; 1×1 impossible.

STEP 5 (assembly): square narrow-unit pencil ⟹ V ~ I_r ⊕ perm ⊕
(⊕ᵢ τ_{bᵢ} ⊕ ⊕ⱼ ς_{aⱼ}).  The transported L-element of this
direct sum: each τ-column j with entries t₀,t₁ at rows i,i'
contributes pairs (i ← j0), (i' ← j1); each ς-row i with s₀,s₁ at
cols j,j' contributes (i0 ← j), (i1 ← j'); each diagonal 1 at
(i,j) contributes (i ← j).  Sources: every col index appears once
as source-block (children for τ-cols, itself otherwise) ⟹
COMPLETE CODE; targets likewise ⟹ pairValue of a complete-code
pair list = codeChange unit ∈ H (codeChange_mem_stableUnits).
All moves: balancedEmbed(GL(k)) units ∈ H, incomparable-unipotent
products ∈ H, permutation-balanced ∈ H ⟹ v ∈ H directly ⟹
NarrowReduction k (no central factor even needed; bypasses
TriangularFactorization, which stays as historical scaffolding).

PENCIL TRANSPORT (level-n form; needed for Step 0 input): for v
narrow with all monomials of depth ≤ n on both sides:
t_i·S(a)T(b)·s_j (|i|=|j|=n) = T(i')S(j') (i = a++i', j = b++j',
zero unless prefix-compatible) ∈ k-span{1, s₀, s₁, t₀, t₁} since
||i'|−|j'|| ≤ 1: entries via wordT_append/wordS_append +
wordT_mul_wordS_self/incomparable.  v = Σ_{ij} s_i V[i,j] t_j via
Σ_{|i|=n} p_i = 1 (complete level-n code).

FORMALIZATION PLAN (in order):
 M1 PencilForm.lean: level-n entry decomposition + scalar-content.
 M2 PencilMoves.lean: balancedEmbed-GL mult (entry transform),
    block-unipotent col/row ops as products of incomparableUnit,
    permutation moves.
 M3 PencilRank.lean: field-linear-algebra: full-col-rank ⟹ GL
    normalization [I;0] (reuse rank-normal-form guts / Mathlib),
    Smith diag(I_r,0).
 M4 PencilBranches.lean: parity, dichotomy (graded top/bottom
    equations via exists_components on the inverse, corner strips).
 M5 PencilRecursion.lean: Steps 3–4 induction.
 M6 NarrowDischarge.lean: Step 5 ⟹ NarrowReduction k; rewire.

## Session 43b: Pencil pipeline M1 + M2 WRITTEN
- PencilCore.lean (M1): balancedEmbed_unit_mem_stableUnits (scalar
  moves ∈ H via levelSpan) and sum_incomparable_unipotent_mem[′]
  (block unipotents with disjoint row/col supports ∈ H, by
  cons-induction peeling incomparable unipotents; cross terms die on
  prefixCode_orthogonal).  Transport layer itself was ALREADY
  compiled: prefixRingEquiv (fullBinaryCode n) : M_{2ⁿ}(A) ≃+* A with
  matrixRingEquiv_apply/symm_apply and unitsEquiv.
- PencilForm.lean (M2): wordT_balancedEmbed_wordS (entry extraction
  via RingEquiv.symm_apply_apply), smul_t/s_expand, pencil_entry_A/B
  (asymmetric peeling: row word's LAST letter → t-generator with
  balanced residue evaluated at level m via a·s_z splits; column
  word's LAST letter → s-generator via s_z·(t_z·b) splits),
  exists_pencil_form: every narrow element = level-(m+1) matrix with
  entries A₀ᵢⱼ•t₀ + A₁ᵢⱼ•t₁ + Cᵢⱼ•1 + B₀ᵢⱼ•s₀ + B₁ᵢⱼ•s₁.
NEXT (M3–M6): Smith-on-C elimination; C=0 branch dichotomy (parity,
rank arguments on 𝔅/Ā via graded equations of the inverse matrix);
the τ/ς extraction recursion; NarrowDischarge.  See session 43 notes
for the complete paper proof.

## Session 43c: CORRECTION to the elimination — Step 0 (Smith-on-C +
## pivot clearing) as stated is WRONG; corrected recursion derived
BUG: after Smith on C the pivot entries are 1 + (odd content), not
clean scalars; Gaussian clearing multiplies odd·odd and creates
degree-±2 debris, leaving the pencil class.  Block-UDL needs the
pivot block invertible — not available.  So DROP Step 0.
FIX: run the τ/ς-extraction on FULL pencils (C included):
- Pure-t columns exist ⟺ ker [B₀; B₁; C] ≠ 0 (the C-row joins the
  stack); pure-s rows ⟺ coker (A₀ | A₁ | C) ≠ 0.
- The extraction + exact elimination (τ_bτ_b' = I_{2b}, ς_a†ς_a =
  I_{2a}) go through verbatim; crucially the correction terms kill
  entire row/column blocks EXACTLY, so the middle block M̃ is the
  ORIGINAL sub-block verbatim — still a (full) pencil.  One-sided
  extraction (only τ or only ς available) also recurses fine.
- Branches: (a) both stacks deficient → extract both, recurse;
  (b)/(c) one deficient → extract one, recurse; sizes strictly drop.
- (d) BOTH stacks full column/row rank: THE REMAINING OPEN CASE
  (parity closed it when C = 0; with C present the top-equation
  chain is B∘x_T = 0; C x_T + B∘x_{T-1} = 0; … — a Wiener–Hopf
  filtration argument is needed).  Examples in (d): V = 1;
  V = 1 + nilpotent-odd-triangular (units ✓).  CONJECTURE (d):
  forces C invertible, and then C⁻¹V = 1 + W with W odd and the
  even-odd decoupling ((1+W) unit ⟺ (1−W²) unit with even inverse)
  or a direct filtration closes it.  NOT YET PROVED.
- Rectangular pure-inverse branches from the C = 0 analysis
  (V = ς·G, V = G·τ) reappear inside (b)/(c) terminals — re-derive
  with C when writing.
STATUS: M1 (PencilCore) + M2 (PencilForm) written and registered.
M3 next = pencilVal transport lemmas (scalar-GL congruence action on
the five matrices; single incomparable-unipotent col/row ops at the
value level) — independent of the branch analysis, safe to build.
M4 = the dichotomy + extraction; its (d)-case needs the filtration
derivation FIRST (paper math next session).

## Session 43d: (d)-branch analysis — top level CLOSED, inner case framed
KEY REALIZATION: at the TOP level (square, word-indexed) the pencil
is just the narrow unit v itself, so window theorems apply:
- If [B₀;B₁] (2p×q, C-less stack) has full column rank: the top
  equation B∘x_T = 0 left-strips (t_y·B∘ = B_y) to B₀x_T = B₁x_T = 0
  ⟹ x_T = 0 for every T ≥ 0 ⟹ the inverse has window ⊆ [−R, −1] ⟹
  v⁻¹ is a NONPOS-window unit ⟹ v⁻¹ ∈ H (window_nonpos_mem_
  stableUnits, COMPILED) ⟹ v ∈ H.  INSTANT.
- Mirror: (A₀|A₁) full row rank ⟹ x's window ⊆ [1, T] via right
  t-strips (x_{−R}A_z = 0) ⟹ v⁻¹ nonneg-window ⟹ v ∈ H.  INSTANT.
- So the top level only needs extraction when BOTH C-less stacks are
  deficient — and then ker[B₀;B₁] ≠ 0 hmm NOTE: pure-t columns need
  ker[B₀;B₁;C] ≠ 0 (with C).  Remaining top-level case: [B₀;B₁]
  column-deficient but [B₀;B₁;C] full — extraction unavailable, window
  argument unavailable.  Handle via the relation system below, or:
  v ∈ ker[B₀;B₁], Cv ≠ 0: column = t-content + constant-content —
  a "quasi-pivot" column; possibly clearable by scalar ops first
  (GL-normalize so that ker[B₀;B₁]-columns have C-content in pivot
  position, then those columns are t₀,t₁,constant-only…).
STRIP CALCULUS facts (all derivable from compiled word lemmas):
- t_y·(B₀s₀+B₁s₁) = B_y;  (A₀t₀+A₁t₁)·s_y = A_y (right-strip);
- s-sums do NOT right-strip (y·s₀ + z·s₁ = 0 does not force y = 0:
  p₁s₀ = 0), so only VX-top and XV-bottom equations strip cleanly.
- XV = 1 expands in PURE T-monomials when X is a scalar t-polynomial:
  exact relation system (S0) Σ_z X_{[z]}B_z = I and
  (S_u) X_u C + Σ_z X_{z::u}B_z + [|u|≥2] X_{tail u}A_{head u} = 0.
- VX = 1 has mixed s_zT(v) monomials; boundary depth 1 gives corner
  relations B_zX_{[y]} = δ_{zy}I via double strips
  (t_a·(eq·S(u))·s_b); deeper: entangled but finite linear algebra.
INNER RECURSION CAVEAT: the rectangular children of the extraction
cannot use window theorems directly (the ambient matVal mixes the
frozen τ/ς blocks' windows).  Options: (i) solve the (S_u)-system
combinatorially for rectangular 4a/4b terminals; (ii) restructure the
recursion to stay at L-level (re-transport each child through a
corner isomorphism p_w L p_w ≅ L so children are again NARROW UNITS
of L at a deeper level — then the WHOLE recursion is: narrow unit →
either window-killed (∈ H instantly) or extraction reduces the
pencil size at fixed level → eventually window-killed; each child is
an honest L-unit and the top-level trichotomy applies verbatim!!).
Option (ii) is much better for formalization: need the corner
transport "unit of p_R·L·p_R-corner with identity complement ↦ unit
of L via a code-change conjugation" — i.e. τ_b⊕M̃⊕ς_a-value ~ (code
change moves) ~ 1⊕M̃'-value with M̃' the SAME pencil re-indexed at
possibly UNEQUAL row/col cylinder sets — needs the rectangular-corner
code-change conjugation lemma (source/target cylinder counts differ;
Leavitt L^p ≅ L^q makes the corners isomorphic via explicit
code-change conjugators).  NEXT SESSION: derive option (ii) cleanly
(the conjugator: pair the R-rows-complement to the C-cols-complement
by a mixed-depth complete-code bijection — exists for any two
nonempty cylinder sets; conjugation by that code-change unit maps
matVal(τ⊕M̃⊕ς) to 1 + (corner content of a DEEPER-level narrow
element) — then recurse as L-units, no matrices).

## Session 44: M3 WRITTEN + the refinement move (index shift) found
- WindowDichotomy.lean (M3) WRITTEN: matrix-free statements!
  mem_stableUnits_of_deg_one_left_full: if ∃ g₀ g₁ with
  g₀·(t₀b) + g₁·(t₁b) = 1 (b := deg-1 part of the narrow unit v),
  then v ∈ H — proof: graded equations of v·v⁻¹ = 1 via
  exists_components + components_unique (z_D := a·y(D+1) + c·y_D +
  b·y(D+(−1)); sum-reindexing via addRightEmbedding +
  Finset.map_add_right_Icc + sum_subset trimming), top-down kill of
  positive components (b·y_d = 0 ⟹ y_d = g₀t₀(b y_d) + g₁t₁(b y_d)
  = 0), then window_nonpos on v⁻¹ and inv_mem.  Mirror:
  mem_stableUnits_of_deg_neg_one_right_full via v⁻¹·v = 1 and
  (a·s₀)h₀ + (a·s₁)h₁ = 1.  NOTE: the full-rank hypothesis is
  equivalent to balanced-coefficient fullness (project g's to their
  degree-0 components), i.e. to the scalar stack ranks.
- THE REFINEMENT MOVE (new, replaces inflation for the stuck branch):
  in a pencil over a PAIR OF COMPLETE PREFIX CODES (row code, column
  code — not necessarily uniform level), any column j whose entries
  are s-FREE (B-content zero, i.e. j ∈ ker of the B-stack after
  right-GL normalization) may be REPLACED by its two children j0, j1:
  E(i, j0) = E(i,j)·s₀ = A₀(i,j)·1 + C(i,j)·s₀ (pencil-legal!), and
  E(i, j1) = A₁(i,j) + C(i,j)·s₁.  No multiplication — same v, refined
  column code.  Effect: the refined columns' A-content → C-content,
  C-content → B-content, A-content of children = 0.  Dually t-free
  rows refine.  This is the Wiener–Hopf partial-index shift.
- LOOP: T1-fail ⟹ ker[B-stack] ≠ 0 ⟹ (right-GL) B-free columns
  exist ⟹ zero columns impossible (invertibility), pure-t columns →
  τ-extraction, else refine.  OPEN: (i) the dichotomy/extraction
  lemmas must be stated CODE-RELATIVE (the current WindowDichotomy is
  intrinsic — fine at top level, but the loop needs the code-relative
  B-stack); (ii) TERMINATION of the refine loop — candidate measure:
  rank of the A-stack (refinement zeroes refined columns' A-content;
  never creates A-content), needs a second tier for rank-preserving
  steps.  Next session: settle code-relative statements + termination
  (python experiments on small pencils can guide), then M4/M5.

## Session 44b: termination probe + recursion without padding
- experiments/pencil_loop.py (exact F2 monomial arithmetic, fresh):
  random narrow units (products of incomparable unipotents, cylinder
  transpositions, ρ-type code changes, filtered to window [−1,1]),
  full round loop [T1/T2 rank checks → extraction availability →
  GL-normalize + refine a B-free column/row].  RESULT: 120/120 reach
  extraction; worst case needed 2 refinements; no illegal entries, no
  stuck states.  Strong evidence for within-round termination.
- NO-PADDING REALIZATION: the cross-round recursion needs no
  squaring-up at all — matVal generalizes to a PAIR of complete
  prefix codes of DIFFERENT sizes (v := Σ S(rᵢ)·E(i,j)·T(cⱼ); unit
  transport works since Σ p_r = 1 = Σ p_c).  The extracted middle M̃
  re-embeds along any complete codes with |R'| resp. |C'| words as an
  honest NARROW UNIT whose pencil is M̃ verbatim; total size |R'|+|C'|
  strictly decreases each round (a, b ≥ 1 blocks extracted).  So
  termination across rounds is BY SIZE; only within-round refinement
  termination needs a proof (probe: ≤ 2 in practice; conjecture: the
  A-stack rank strictly drops per refinement round or extraction
  becomes available — prove next session).
- README now tracks the NarrowReduction program as a checklist under
  B4; tick items as modules land (per user request).
REMAINING LEAN (in order): M4a mixed-code matVal + unit transport
(generalize PencilCore/prefixRingEquiv to code pairs); M4b the
extraction lemma; M4c refinement legality lemma (pure bookkeeping:
E(i,j0) = E(i,j)·s₀ identities); M5 the round recursion (strong
induction on |R|+|C|); M6 NarrowDischarge → NarrowReduction k; then
cleanup + full build.

## Session 45: M4 support modules landed
- CodePairTransport (user-polished): codePair_mul (middle-code
  collapse; outer word maps arbitrary), codePair_mul_eq_one,
  codePairUnit (rectangular two-sided inverses transport to units
  along code pairs of DIFFERENT sizes).
- WindowDichotomy REFACTORED to single-witness hypotheses
  (w·b = 1 / a·w = 1) — strictly stronger interface, simpler kills.
- CodeScalarMoves: codeScalar (scalar-matrix transport along ANY
  complete code), one/mul lemmas, transvections ↦ incomparable
  unipotents, diagonal(d) with d ≠ 0 ↦ product of pairKappaUnit
  insertions of central scalars (Finset product identity with
  orthogonality cross-kills), codeScalar_unit_mem: EVERY invertible
  scalar matrix transports into H along every complete code, via
  Matrix.Pivot transvection decomposition.
- CodeRelativeFullness: smul_mul_smul', t_combo_mul_s_combo
  ((Σα_z•t_z)(Σβ_w•s_w) = (Σα_zβ_z)•1), stack_left/right_inverse_
  transport: scalar stack one-sided inverses give the WindowDichotomy
  witnesses w over ANY code pair.  KEY DESIGN WIN: the witness w is
  written directly in pencil-entry form (t-combos between C-words and
  R-words), so codePair_mul does the whole collapse — no appended
  words, no incomparability side lemmas.
REMAINING: M4b atom-peel factorization (single pure-t column ⟹
v = (moves)·u₁·u₂ with u₁ a code-change and u₂ a strictly smaller
code-pair pencil unit); M4c refinement identities; M5 master
induction (on |ι| + |κ|) assembling: dichotomy-with-witnesses /
peel / refine; M6 NarrowDischarge.  Within-round termination proof
still needed (probe says ≤ 2 refinements; candidate: A-stack rank
drops or extraction fires).

## Session 45b: glue + termination evidence strengthened
- CodeChangeGlue.lean: isCompleteCode_of_family (Fintype → list
  interface), codeBijection_mem_stableUnits (Σᵢ s_{τᵢ}t_{σᵢ} ∈ H via
  the compiled generation theorem), cylinder_split,
  incomparable_append_single, split_family_free/sum (one-word split
  of a complete family, indexed Fin 2 ⊕ {i ≠ j₀}).  These are the
  u₁-ingredients of the atom peel.
- Probe extended (400 random narrow units): every case terminates;
  refinement needed in 183 cases, ALWAYS exactly one refinement, and
  afterwards the s-side extraction fires.  A-stack rank at the refine
  moment is often 0, so the naive rank measure is NOT the mechanism.
- Worked by hand the minimal stuck example (2×2):
  v = s₀t₀² + s₁t₀ + s₁s₀t₁, pencil [[t₀,0],[1,s₀]], unit with
  explicit inverse [[s₀,p₁],[−1,t₀]].  One col-refinement produces
  [[1,0,0],[s₀,s₁,s₀]] over {00,01,1}; row 2 becomes pure-s (u₀ = e₂
  annihilates the A′-stack AND the children's C-content, since
  children's C-cols are the old A-cols); one scalar col-op + one
  exact t-multiplier row-op reach ς ⊕ (−1).  KEY PARTIAL FACT toward
  termination: after refining ALL B-free kernel columns, any
  u₀ ∈ coker(A-stack) automatically annihilates the children's
  C-content (children C-cols = old A-cols); the only obstruction to
  the s-extraction firing is u₀·(C-content of the surviving columns).
  CONJECTURE (matches all 583 machine cases): iterating the batch
  refine forces this obstruction to die — candidate second-tier
  measure: dim(coker A-stack ∩ (surviving-C-cols)^⊥) strictly grows.
- User expanded the goal: after formalization completes → fully
  update nonsofic_groups_exist.tex → pursue new results beyond it.

## Session 46: M4b — the atom peel WRITTEN
AtomPeel.lean: atom_peel — given pencil data E over (R, C) with a
normalized shift-atom column (E i₁ j₀ = t₀, E i₂ j₀ = t₁, rows i₁ i₂
zero elsewhere) and ANY complete code D on {i // i ≠ i₂}, produces
u₂ with value the residual pencil over (D, C) (untouched block + one
scalar pivot at (⟨i₁⟩, j₀)) and u ∈ H ↔ u₂ ∈ H.  Mechanism:
- σ := the split of D at d₁ := ⟨i₁⟩ (children d₁·0 ↦ row i₁,
  d₁·1 ↦ row i₂; others untouched); prefix-freeness by four-way case
  analysis on incomparable_append_single; completeness by
  double-erase + sum_bij' bridge + cylinder_split.
- u₁ := codePairUnit(R, σ-code, δ, δ) — value Σ S(Rᵢ)T(σᵢ) by
  codeDelta_collapse; u₁ ∈ H by codeBijection_mem_stableUnits.
- hrow: a word colliding with D in exactly one place collapses the
  residual double sum to one row (reused 3×: t₁/t₀/scalar patterns).
- hfact: u = u₁·W by per-row case analysis; u₂ := u₁⁻¹·u — NO
  inverse data for the residual needed.
- NOTE: user fixed orientations live in parallel; remaining swaps +
  unused hlen applied.  Recurring bug-class: incomparable_append_
  single argument orientation — ALWAYS instantiate v := the
  non-appended word, w := the appended-to word, and check which of
  .1/.2 matches the goal.
STILL NEEDED for the extraction branch: (i) peel-normalization —
from "ker[B₀;B₁;C] ≠ 0" produce the (h1–h5)-normalized pencil via
codeScalar GL-moves (pair-extension-to-basis linear algebra) and the
exact right-multiplier (1 + N) clearing rows i₁,i₂ outside j₀
(disjoint-support block unipotent, value computation like
BlockMoveTailKill); (ii) the ς-mirror of the peel (or θ-transport);
(iii) M5 master induction; (iv) the stuck-branch progress theorem
(one batch refine ⟹ extraction/dichotomy — see session 45b notes for
the coker-A structural fact); (v) M6 NarrowDischarge; cleanup.

## Session 46b: peel-normalization support modules
- MixedCodeMoves.lean: code_unipotent_mem (block unipotents with
  disjoint supports along ANY prefix code ∈ H — generalizes
  PencilCore from uniform depth); t_combo_not_left_invertible
  (x·(λ₀•t₀ + λ₁•t₁) ≠ 1 via s_z-right-strips forcing s₁ ∈ k·s₀,
  killed by t·s-corners) — this forces the linear independence of
  the shift-column pair from unit-column left-invertibility.
- GLPairNormalization.lean: exists_isUnit_matrix_mulVec_pair —
  independent pair ↦ (Pi.single i₁ 1, Pi.single i₂ 1) by an
  invertible matrix: Basis.extend + two-swap index bijection +
  Basis.equiv + toMatrix'/toLin' transport.  Mathlib-API-heavy
  (name risks: to_subtype_range, extend_apply_self,
  fintypeBasisIndex, finrank_pi, basisFun_apply, toLin'_toMatrix').
NEXT (the extraction-normalization assembly, then M5):
 exnorm: from a unit-pencil (R,C,E) with kernel data
 (v₀ scalar, B_z·v₀ = 0, Cm·v₀ = 0, v₀ ≠ 0):
 (1) right-GL by any G with G⁻¹-hmm column-mix so col j₀ carries
     E·v₀ (pure-t); value-transform via codePair_mul with
     codeScalar-data; membership via codeScalar_unit_mem;
 (2) independence of the resulting (A₀-col, A₁-col) from
     t_combo_not_left_invertible + the left-invertibility witness
     T(Cⱼ₀)·u⁻¹ of the column u·S(Cⱼ₀);
 (3) left-GL from exists_isUnit_matrix_mulVec_pair putting the
     column into atom shape;
 (4) right block-unipotent (code_unipotent_mem, support
     {j₀}×(κ\{j₀})) clearing rows i₁ i₂ exactly (t₀s₀ = 1-cross);
 (5) atom_peel.  All five composed give: extraction-eligible unit ⟹
     ∃ smaller-code-pair pencil unit, H-membership equivalent.

## Session 46c: PencilEntryArith landed
pencilEntry (a₀•t₀ + a₁•t₁ + c•1 + (b₀•s₀ + b₁•s₁)) — matches
exists_pencil_form's parenthesization exactly (definitional bridge);
smul_mul_algebraMap / algebraMap_mul_smul; pencilEntry_mul/
mul_pencilEntry (coefficientwise scalar action); sum_pencilEntry;
pencilVal_mul_codeScalar and codeScalar_mul_pencilVal: right/left
transported-GL moves act as right/left matrix multiplication on the
five coefficient matrices (via codePair_mul + beta_reduce pattern).
ASSEMBLY MAP for exnorm (next session, all ingredients now exist):
 given kernel vector v₀ of [B₀;B₁;Cm]:
 (1) G_right := any invertible G with G·e_{j₀}-column = v₀
     (single-vector case of GLPairNormalization — need the 1-vector
     variant: v₀ ≠ 0 extends to a basis; SIMPLER: take the pair
     (v₀, any-independent-partner) or prove exists_isUnit_matrix_
     mulVec_single analogously; or transpose-trick);
     u' := u · codeScalarUnit(C, G_rightᵀ-hmm orientation: want
     new-col-j₀ = Σₗ E l·v₀ l: pencilVal_mul_codeScalar gives
     coefficients Σₗ A₀ i l G l j: col j₀: Σₗ A₀ᵢₗG_{l j₀}: need
     G-COLUMN-j₀ = v₀: same single-vector normalization, inverted;
 (2) new col j₀: B/C-coefficients vanish (kernel!), A-pair columns
     (a := A₀G-col, b := A₁G-col); independence: else t_combo_not_
     left_invertible contradicts left-invertibility of
     u'·S(C.word j₀) (witness T(C.word j₀)·u'⁻¹);
 (3) left move by exists_isUnit_matrix_mulVec_pair-G';
     codeScalar_mul_pencilVal;
 (4) clear rows i₁,i₂ outside j₀: right multiplier
     1 − Σ_{j≠j₀} S(C j₀)·x_j·T(C j), x_j := s₀·pE(i₁-row) +
     s₁·pE(i₂-row); membership code_unipotent_mem
     ({j₀}×(κ\{j₀})-support); value via codePair_mul with
     (δ + N)-data; entry-identities t₀s₀ = 1 kills exactly;
 (5) atom_peel.  Note: also need the 1-vector GL-normalization
     lemma (exists G invertible with G.mulVec e_{j₀} = v₀ — i.e.
     v₀ as a COLUMN of an invertible matrix; equivalently extend
     {v₀} to a basis — write exists_isUnit_matrix_col_eq next).

## Session 47: normalization toolkit COMPLETE
All extraction-step ingredients now written (pending user compile):
- CompleteCodeSupply: family_transport, exists_complete_family
  (induction: root code + split_family via equivOfCardEq),
  exists_complete_family_of_nonempty.
- GLVectorNormalization: exists_isUnit_matrix_col (v ≠ 0 as the
  j₀-column of an invertible matrix, via linearIndependent_unique +
  linearIndepOn_id + Basis.extend + one swap; NOTE the modern name
  linearIndepOn_id replaces to_subtype_range — user fixed the pair
  version).
- RowClearMove: pencilVal_mul_wordS (column collapse),
  t_zero/one_collapse, row_clear — the correction N (square-zero,
  code_unipotent_mem on {j₀}×erase j₀), the atom-column value
  (u·S(C j₀) = S(R i₁)t₀ + S(R i₂)t₁), the correction identity
  u·N = Σ_{j≠j₀}(atom-row terms), and the final six-way
  add_sum_erase split closed by abel.
REMAINING for goal (1): (a) FullExtraction.lean — compose:
 exists kernel vector of [B₀;B₁;Cm]-stack ⟹ (right codeScalar move
 with exists_isUnit_matrix_col putting v₀ into column j₀;
 pencilVal_mul_codeScalar) ⟹ (column j₀ pure-t; independence via
 t_combo_not_left_invertible against the witness T(C j₀)u⁻¹ +
 dependence-dichotomy over k) ⟹ (left codeScalar move with
 exists_isUnit_matrix_mulVec_pair; codeScalar_mul_pencilVal) ⟹
 row_clear ⟹ atom_peel (D from exists_complete_family_of_nonempty;
 nonempty since independence forces card ι ≥ 2).
 (b) the ς-mirror (mirror FullExtraction: pure-s ROW: either θ-
 transport or the symmetric proofs — the row-versions of
 pencilVal_mul_wordS-hmm wordT-mul-pencilVal etc).
 (c) M5 master induction (strong induction on card ι + card κ;
 branches: b = 0/a = 0 window-kill-direct; witness-dichotomy via
 CodeRelativeFullness + WindowDichotomy; extraction via
 FullExtraction; stuck-branch: batch refine + progress theorem).
 (d) M6 NarrowDischarge (exists_pencil_form bridge; top-level codes
 are fullBinaryCode; conclude NarrowReduction k).
 (e) cleanup + full build.

## Session 48: FullExtraction WRITTEN — the size-reduction engine
FullExtraction.full_extraction: from a kernel vector v₀ of
[B₀;B₁;Cm] (columnwise scalar equations), produces i₂, a complete
code D on {i ≠ i₂}, residual five-matrix data over (D, C), and u₂
with u ∈ H ↔ u₂ ∈ H.  Composition: exists_isUnit_matrix_col →
pencilVal_mul_codeScalar → (independence: LinearIndependent.pair_iff
by_contra, both dependence cases reduced to t_combo_not_left_
invertible against the witness (T(C j₀)·u1⁻¹)·(u1·S(C j₀)) = 1;
t = 0 case gives a = 0 directly, t ≠ 0 gives b = (−t⁻¹s)•a) →
fintype_card_le_finrank + finrank_pi + exists_pair_of_one_lt_card →
exists_isUnit_matrix_mulVec_pair → codeScalar_mul_pencilVal →
row_clear → atom_peel, with the residual-data bridge (per-(p,j)
split_ifs; pivot row becomes the Cm'-scalar 1 at (⟨i₁'⟩, j₀)).
H-chain: four-step iff-calc through uG, uG', row-clear m, u₁-peel.
REMAINING (goal 1): (a) ς-mirror of full_extraction; (b) the
rank-fullness → scalar one-sided inverse lemma (feeds
CodeRelativeFullness witnesses from stack-rank facts; via
LinearMap.exists_leftInverse-machinery); (c) M5 master induction
(measure card ι + card κ; branches recorded) + the stuck-branch
progress theorem (the only open math; 583/583 machine-verified);
(d) M6 NarrowDischarge; (e) cleanup + build; then goals 2–3.

## Session 49: MirrorExtraction landed + M5 architectural finding
- MirrorExtraction.lean WRITTEN: thetaHat_pencilEntry (θ̂ swaps t/s
  coefficient slots), thetaHat_pencilVal (θ̂ transposes code
  pencils), mirror_extraction: row-stack kernel vector ⟹ pencil
  unit over one fewer COLUMN, by full_extraction on the transposed
  side + thetaUnit_mem_stableUnits_iff transport.  Short (θ-route),
  no re-mirroring of the six modules.
- M5 FINDING (important): WindowDichotomy is a TOP-LEVEL argument —
  it needs the pencil parts to be pure-degree components, i.e.
  UNIFORM-depth codes.  Inner recursion nodes have mixed-depth codes
  (the peel's intermediate D), where deg(S(Rᵢ)t_zT(Cⱼ)) =
  |Rᵢ|−|Cⱼ|−1 varies.  So the inner T1/T2-full branches need a
  DIFFERENT terminal.  DERIVED (mostly): the ENTRYWISE-GRADED KILL:
  strip the unit equations to Σⱼ xᵢⱼ·y_{ji'} = δᵢᵢ' with
  y_{ji} := T(Cⱼ)u⁻¹S(Rᵢ); at the top entry-degree D of Y the
  s-part gives Σⱼ B_wᵢⱼ·y^{(D)}_{ji'} = 0 (t_w-strips; SCALAR
  combinations of the entry components!), so a full B-stack kills
  all positive entry components: Y-entries nonpositive.  MIRROR
  (A-stack full): entries nonnegative.  REMAINING QUESTION: the
  terminal conclusion from "u⁻¹ has nonpos-degree pencil entries"
  at mixed codes.  Candidate resolutions, ranked:
  (1) BOTH-FULL SANDWICH: if the node has BOTH stacks full (can the
      branching arrange this?), entries are balanced ⟹ u⁻¹ is a
      balanced-entry code-pair matrix ⟹ u⁻¹ = (code change)·
      (balanced unit)-decomposable ⟹ H by compiled machinery.
      Check: is inner-T1-full ∧ T2-deficient reachable? If the
      branch order tests extraction FIRST (both kernels empty in the
      T-branches), T1-full ∧ ker[B;C] = 0 ∧ coker[A;C] = 0 forces…
      analyze: T1-full ⟹ kerB = 0 ⟹ ker[B;C] = 0 ✓ consistent;
      coker[A;C] = 0 does NOT give A-stack-full.  So one-sided-full
      is reachable.  BUT: with Y-nonpos from T1, RERUN the kill on
      the OTHER equation side (u⁻¹u = 1, strips by T(Cⱼ)·…·S(Cⱼ')):
      gives the A-stack-of-u¹-hmm — the second kill needs the
      A-stack of u to be full, not given.  Partial.
  (2) UNIFORMIZING CONJUGATION: code-change ω's re-index (C,R) to
      uniform codes; blocked by the size-vs-depth constraint
      (Σⱼ2^{dⱼ} = 2^P forces varying dⱼ, which re-mixes degrees).
      Might be fixable by conjugating with ω on ONE side only and
      re-running the dichotomy at the new mixed shape.
  (3) Restate the master induction so inner nodes carry uniform
      codes: replace the peel's D by "refine everything to uniform
      after each peel" — needs re-narrowing (compiled window
      reduction) but breaks the size measure; would need a new
      measure (e.g. number of atoms extracted is NOT monotone…).
  (4) Prove the nonpos-entry terminal directly: u⁻¹-value lies in
      span{S(Cⱼ)·x·T(Rᵢ) : x nonpos}; seek a compiled-adjacent kill
      for this "code-window" class (θ of a code-nonneg class; the
      BlockMoveTailKill induction might generalize code-relatively —
      its moves are already code-flavored!).  Perhaps simplest:
      mimic WindowNonnegReduction's induction with the uniform
      level-1 code replaced by C-children; its engine
      (block move + κ-transport + orthogonality) is code-agnostic.
  NEXT SESSION: settle the inner terminal (try (4) seriously first —
  reread WindowNonnegReduction's proof shape; then (1)); then M5.

## Session 50: INNER TERMINAL FULLY DERIVED
The M5 branch structure is now: (extract) ∨ (mirror-extract) ∨
(col-refine: kerB ≠ 0) ∨ (row-refine: cokerA ≠ 0) ∨ TERMINAL-(a)
[kerB = 0 ∧ cokerA-rows = 0, i.e. BOTH C-less stacks full].
TERMINAL-(a) — complete derivation, all with compiled pieces:
 (a1) ENTRYWISE KILL, both directions: entries y_{ji} :=
      T(Cⱼ)u⁻¹S(Rᵢ); strip equations Σⱼ x_{ij}·y_{ji'} = δᵢᵢ'•1
      (x = pE-entries; insertion of Σ p_{Cⱼ} = 1) and the mirror
      Σᵢ y_{j'i}·x_{ij} = δ_{j'j}•1.  Downward induction at the top
      entry-degree: only B-part·y^{(D)} survives at degree D+1; t_w
      strips give Σⱼ B_wᵢⱼ y^{(D)}_{ji'} = 0; the scalar left
      inverse (G₀,G₁) of the B-stack combines these to
      y^{(D)}_{j₀i'} = 0.  B-full ⟹ entries nonpos.  Mirror: bottom
      equations + s_z-strips + right inverse of (A₀|A₁) ⟹ entries
      nonneg.  Both ⟹ Y-BALANCED.
 (a2) PADDING: balanced entries live in levelSpan(M) for common M;
      u⁻¹ = Σ scalar·S(Cⱼα)T(Rᵢβ) over the M-refinements of C and R
      (uniform under-word refinement keeps codes complete/free —
      have split machinery; M-fold refinement = words ++ level-M).
 (a3) SQUARENESS: the scalar matrix W over the refined code pair is
      invertible over k: a kernel vector v₀ of W gives (after the
      right codeScalar move, compiled) a ZERO COLUMN of a unit:
      0 = u⁻¹·S(word) ⟹ S(word) = 0 ⟹ contradiction (t·s = 1).
      Applied to both W and Wᵀ: |C-ref| = |R-ref| AND det W ≠ 0.
 (a4) DECOMPOSITION: pick a common index equiv; ω := code bijection
      (C-ref → R-ref) ∈ H (codeBijection_mem_stableUnits);
      ω⁻¹·u⁻¹ = codeScalar(R-ref, W′) ∈ H (codeScalar_unit_mem)
      ⟹ u⁻¹ ∈ H ⟹ u ∈ H.
With this, THE ONLY REMAINING OPEN MATH is refine-branch
termination (unchanged; 583/583 machine-verified).  FORMALIZATION
ORDER: EntryStrip.lean (insertion identity + two-sided entry
collapse); EntrywiseKill.lean (a1); BalancedCodePencil.lean
(a2+a3+a4); StackDichotomy.lean (scalar left-inverse-or-kernel);
M5 shell; M6.

## Session 50b: EntryStrip + EntrywiseKill WRITTEN
- EntryStrip.lean: wordT_pencilVal_wordS (two-sided strips recover
  entries, arbitrary E), strip_insert (products strip through a
  complete code's partition of unity).
- EntrywiseKill.lean: t_zero/one_strip_scombo helpers;
  entry_window_nonpos_of_B_full — common window via choose +
  Finset.sup, per-entry graded components via choose, strip
  equations from strip_insert + Units.mul_inv + entry extraction,
  degreewise equations via components_unique (z-function summed over
  Icc(−N−1, N+1) with the three shifted sums per code entry), the
  downward kill with the two t_w-strip relations and the scalar
  left-inverse combination (sum_smul/smul_smul juggling), and entry
  reassembly into span(dM(−N, 0)).
STILL FOR M5: the mirror kill (θ or symmetric: entries nonneg of A
full — likely via thetaHat on this theorem); BalancedCodePencil
(a2–a4: padding to scalar W over refined codes, squareness via
zero-column impossibility, ω·codeScalar decomposition);
StackDichotomy (left-inverse-or-kernel linear algebra); the M5 shell
(strong induction, five branches); refine-branch termination; M6.

## Session 51: StackDichotomy + RefinedCodes + combo independence
- StackDichotomy.lean: stack_left_inverse_or_kernel (via mulVecLin
  kernel cases + LinearMap.exists_leftInverse_of_injective +
  toMatrix'/toLin' transport; entries via Fintype.sum_sum_type) and
  the transposed mirror with mul_comm massage.
- RefinedCodes.lean (user-polished): not_prefix_append_of_
  incomparable/same, cylinder_level_split (induction with consEquiv;
  NOTE user fixes: append_assoc+singleton_append instead of
  append_cons chains; Fintype.sum_prod_type must NOT be applied with
  explicit `_` — higher-order unification times out), refined_free,
  refined_sum, codePair_partition.
- BalancedCodePencil.lean (installment 1): wordS/wordT_combo_eq_zero
  — k-independence of code words via one-sided strips; these are the
  zero-column/row engines for the squareness argument.
REMAINING for BalancedCodePencil (installment 2, next session):
 main theorem balanced_entries_mem_stableUnits following session-50
 notes: common level via choose+sup (EntrywiseKill pattern); W-data
 via exists_balancedEmbed_eq; hval: the four-fold reindex
 u⁻¹ = Σ_pΣ_q S(CM p)·map(W' p q)·T(RM q) (codePair_partition +
 matrixRingEquiv_apply + wordS/T_append + sum_prod_type);
 hinj/hinj' via x₀ := Σ v₀•S(RM q), u⁻¹x₀ = 0 ⟹ x₀ = 0 ⟹ combo
 lemmas; hcard via finrank_le_finrank_of_injective + finrank_pi;
 ω via codePairUnit-δδ (AtomPeel u₁ pattern) along equivOfCardEq;
 u₂ := ω·u⁻¹ = codeScalar(RM, W''); IsUnit W'' via
 injective_iff_surjective + LinearEquiv + toMatrix'-two-sided;
 codeScalar_unit_mem; conclude u⁻¹ = ω⁻¹u₂ ∈ H.
THEN: mirror entrywise kill (θ-transport of entry_window_nonpos —
gives entries nonneg when (A₀|A₁) full); M5 shell; refine
termination; M6.

## Session 52: BalancedCodePencil COMPLETE + StackDichotomy
balanced_entries_mem_stableUnits fully written (no sorries): common
level (choose+sup), scalar data (exists_balancedEmbed_eq per entry),
the four-fold reindex hval (codePair_partition + rfl-embed-expansion
+ append-collapses + sum_prod_type/sum_comm), zero-column hinj
(x₀ := Σ v₀•S(RM q); u⁻¹x₀ = 0 by orthogonality collapse + map_sum;
x₀ = u(u⁻¹x₀) = 0; wordS_combo), zero-row hinj' (p₀-sum FIRST, then
sum_comm and map_sum against hu₀ — note the vanishing only holds
after summing p₀!), hcard via mulVecLin-injectivity + finrank_pi,
ω := codePairUnit-δδ along equivOfCardEq (AtomPeel pattern),
hu₂val via codePair_mul + δ-collapse + sum_equiv-reindex,
hdet via exists_mulVec_eq_zero_iff + hinj, codeScalar_unit_mem,
u⁻¹ = ω⁻¹(ω u⁻¹).
REMAINING for goal (1):
 (i) mirror entrywise kill: entries NONNEG when (A₀|A₁) full — via
     θ-transport of entry_window_nonpos_of_B_full (θ̂ swaps the
     pencil B-data with A-data and reverses entries:
     θ̂(T(Cⱼ)u⁻¹S(Rᵢ)) = T(Rᵢ)θ̂(u)⁻¹-hmm θ̂(u⁻¹)-S(Cⱼ);
     thetaHat_mem_span_degree flips the window sign) — OR prove
     symmetrically with s_z-right-strips (bottom equations).
 (ii) window-intersection lemma: x ∈ span[−N,0] ∩ span[0,N'] ⟹
     x ∈ span[0,0] (components_unique on the two decompositions).
 (iii) M5 shell: strong induction on card ι + card κ; branches via
     stack_left_inverse_or_kernel ×2:
     - both left/right-inverses ⟹ EntrywiseKill + mirror + (ii) ⟹
       balanced entries ⟹ BalancedCodePencil ⟹ H;
     - B-kernel v₀: if also Cm·v₀ = 0-condition (check the C-column
       against v₀!): full_extraction; else refine-branch;
     - A-side mirror likewise (mirror_extraction);
     NOTE the extraction needs ker[B;C] (WITH C); the dichotomy
     gives ker[B] only — the M5 branch logic must test the
     C-inclusive stack for extraction and fall to refine when only
     the C-less kernel exists (the stuck branch).
 (iv) refine termination (open; 583/583 verified; the coker-A
     structural fact from session 45b is the key).
 (v) M6: exists_pencil_form at fullBinaryCode-codes (uniform level)
     feeding M5; conclude NarrowReduction k; rewire; cleanup.

## Session 53: M5 SHELL + M6 DISCHARGE WRITTEN — chain closed mod ONE Prop
- EntrywiseKillMirror.lean: mem_balanced_of_nonpos_nonneg (component
  uniqueness on the two window decompositions),
  entry_window_nonneg_of_A_full (θ-transport of the direct kill:
  entries of (θu)⁻¹ are θ̂ of entries of u⁻¹ with codes swapped;
  thetaHat_mem_span_degree flips the window).
- MasterInduction.lean: def StuckReduction (the isolated refinement
  configuration: pencil unit, no C-inclusive kernel on either side,
  but a C-less kernel exists); pencil_unit_mem — strong induction on
  card ι + card κ: empty-index contradiction, column/row extraction
  branches recursing via full_extraction/mirror_extraction
  (card_subtype_compl arithmetic), both-stacks-full terminal via the
  two kills + intersection + balanced_entries_mem_stableUnits, and
  the two stuck arrivals dispatched to StuckReduction.
- NarrowDischarge.lean: narrowReduction_of_stuckReduction —
  exists_pencil_form at fullBinaryCode(m+1) + pencil_unit_mem +
  stableUnits_le_centralClassGroup.  THE ENTIRE K₁-VANISHING CHAIN
  (NarrowReduction → ScalarReduction → B4 → GL = EL → Theorem C) NOW
  RESTS ON THE SINGLE PROP StuckReduction k.
REMAINING for goal (1): discharge StuckReduction (the refinement
termination argument — 583/583 machine-verified; the batch-refine +
coker-A structural fact from session 45b is the plan); then
retire/derive TriangularFactorization, refresh stale docstrings,
audit, full build.  Then goal (2): manuscript rewrite; goal (3):
novel results.

## Session 54: StuckReduction SOLVED — the two-exit algorithm (no
## extraction, no termination measure)

Numerics first (experiments/pencil_loop.py, case4_probe /
rank_evolution_probe / stall_probe, 3000 trials): every narrow unit
resolves by extraction at uniform starting codes; case 4 (both
C-less stacks deficient) is real (264 events, chains up to 9,
consecutive rank-stalls up to 4); the batch-refine ⟹ row-extract
conjecture from session 45b is FALSE (8/264).  So the extraction
route needs a genuine termination argument.  It turns out none is
needed: the master induction can be BYPASSED entirely.

KEY REALIZATIONS.
(1) `refine_column` needs only a B-free column — no condition on
the C-data.  Any kernel vector of [B₀;B₁] can be normalized into a
B-free column by a codeScalar move (compiled) and split (compiled).
So whenever ker[B₀;B₁] ≠ 0 we may grow κ by one at FIXED ι.
Once κ > 2ι the kernel is automatic (rank ≤ 2ι), so the refinement
loop can always continue to any target κ.
(2) FREE EXIT.  A pencil unit u = Σ S(R_i) E_ij T(C_j) (E narrow,
degrees in [−1,1]) with κ ≥ 2·2^⌈log₂ ι⌉ lies in stableUnits
directly: conjugate by two codeChange units (compiled), replacing R
by a complete code P of size ι with max depth M_ι := ⌈log₂ ι⌉ and C
by a complete code Q of size κ with min depth ≥ M_ι + 1 (exists
since κ ≥ 2^{M_ι+1}: split the full level-(M_ι+1) code).  Value
degrees ≤ max|P| + 1 − min|Q| ≤ 0, so window_nonpos_mem_stableUnits
(compiled) applies.  Kraft bounds show this aspect threshold is
achievable exactly when stated.
(3) STRICT NEGATIVITY.  If [B₀;B₁] has full column rank (scalar
left inverse G, compiled dichotomy), the compiled kill pins
X_ji := T(C_j) u⁻¹ S(R_i) to the window [−N, 0]; then the
degree-(+1) component of the strip Σ_j E_ij X_ji' = δ_ii' reads
Σ_j (B₀ij s₀ + B₁ij s₁) X⁰_ji' = 0 (X⁰ := balanced component; the
A- and C-slots cannot reach degree +1 against a nonpos window).
Stripping with t₀, t₁ gives Σ_j B_zij X⁰_ji' = 0 in L, and the
SCALAR left inverse G applies verbatim to L-valued vectors:
X⁰ = G·(BX⁰) = 0.  Hence X_ji ∈ span dM(−N, −1): strictly negative.
(4) PADDED EXIT.  With entries ≤ −1 the reshaped value needs only
max|Q| ≤ min|P| + 1.  Rounding can obstruct this (e.g. ι=5, κ=9),
but corner padding fixes it: κ_w-insertion at a word w of depth m
(κ_w(u) = s_w u t_w + (1 − p_w), value = S(w)uT(w) + Σ_{comp(w)}
S(v)T(v)) realizes the block sum u ⊕ I_m as a pencil over codes
(wR ∪ comp(w), wC ∪ comp(w)); code changes then redistribute the
words freely.  Choose d := ⌈log₂ ι⌉, m := 2^{d+1} − κ (≥ 0 since
κ ≤ 2ι ≤ 2^{d+1}; rank bound + the loop invariant κ ≥ ι).  Take
Q̃ := full level (d+1) (old block max depth d+1, pads at d+1) and
P̃ := a complete code of size ι+m, all depths ≥ d, with the m pad
words at depth ≥ d+1 — constructed from the full level-d code by
s := ι + 2^d − κ splits of which x := 2^d − ι hit level-d words
(0 ≤ x ≤ s ⟺ ι ≤ 2^d and κ ≤ 2ι ✓; deep-word count s + x =
2^d − ι + s ≥ m ✓).  Old entries: (d+1) − 1 − d ≤ 0 ✓; pad
diagonal: (d+1) − |P̃pad| ≤ 0 ✓.  Value nonpos ⟹ padded unit ∈ H
⟹ κ_w(u) ∈ H (code changes) ⟹ u ∈ H (kappa corner transfer).

THE ALGORITHM (proves: EVERY pencil unit over complete codes with
κ ≥ ι lies in stableUnits; narrow units enter at ι = κ = 2^{m+1}):
  while κ < 2·2^⌈log₂ ι⌉:
    if ker[B₀;B₁] ≠ 0: codeScalar-normalize; refine_column  (κ += 1)
    else: B full ⟹ strict-negativity ⟹ padded exit.  STOP.
  free exit.  STOP.
Termination: the loop counter 2·2^⌈log₂ ι⌉ − κ strictly decreases;
ι never changes.  No extraction, no atom peel, no terminal theorem,
no master induction needed for the main chain (they remain as
standalone structure results).  StuckReduction k follows a fortiori
(the stuck hypotheses are simply unused), which closes
NarrowReduction, ScalarReduction, B4, GL = EL, and Theorem C
unconditionally.

FORMALIZATION PLAN:
 N1 StrictNegativePencil.lean: (3) — balanced component of the
    inverse entries dies under a full B-stack.
 N2 CodeShapeSupply.lean: complete codes of size n with max depth
    ⌈log₂ n⌉; of size n ≥ 2^M with min depth ≥ M; the padded pair
    (P̃, Q̃) with its pad pairing (list-based, split-construction).
 N3 PencilReshape.lean: value window of Σ S(Q_j) X_ji T(P_i) from
    entry windows and depth bounds; the codeChange conjugation
    identity ω₁ u ω₂ = reshaped pencil.
 N4 KappaBlockSum.lean: κ_w(u) as a pencil over the augmented
    codes; κ_w(u) ∈ H ⟺ u ∈ H from the compiled corner machinery.
 N5 RefineLoopDischarge.lean: the κ-growth loop (induction on
    2·2^⌈log₂ ι⌉ − κ) + assembly: pencil_unit_mem_unconditional,
    stuckReduction_holds : StuckReduction k, and NarrowReduction k
    outright via narrowReduction_of_stuckReduction.

### Session 54b: exits made fully explicit (only ONE new code construction)

The row code NEVER changes in the algorithm: it stays
fullBinaryCode r, r := m+1, ι = 2^r.  This collapses the code
supply to a single construction:
  (a) exists_complete_deep_family: complete code of size n with all
      depths ≥ M, for any n ≥ 2^M — from fullBinaryCode M by
      n − 2^M arbitrary splits (split_family_free/sum, compiled);
      splitting preserves the depth lower bound.
FREE EXIT (fires at exactly κ = 2^{r+1} = 2ι): reshape only the
column code, Q := fullBinaryCode (r+1) — uniform, no splits.  Value
degrees ≤ r + 1 − (r+1) = 0.  One codeChange unit on the right.
PADDED EXIT (B full at κ ≤ 2ι, entries ≤ −1 by StrictNegativePencil):
pad count m' := 2^{r+2} − κ (≥ 2ι since κ ≤ 2ι).  Column side
Q̃ := fullBinaryCode (r+2) — uniform!  Row side
P̃ := 1·(fullBinaryCode r)  ∪  0·D,  D := deep code of size m' with
depths ≥ r+1 (construction (a); m' ≥ 2^{r+1} ✓): old block = the
1-subtree (ι words at depth r+1: old entries (r+2) − 1 − (r+1) ≤ 0 ✓),
pads = the 0-subtree (depths ≥ r+2 = |Q̃pad| ✓ diagonal nonpos ✓).
Pairing: any bijection pads(Q̃) ↔ pads(P̃).  The padded unit is
ω₁ · κ_w(u) · ω₂ with |w| = ... realized instead directly as the
block-sum unit ũ⁻¹ := g u⁻¹ h + e (g := Σ S(Q̃old_j)T(C_j),
h := Σ S(R_i)T(P̃old_i), e := Σ_pads S(Q̃pad)T(P̃pad)); proof of
unitality: gg'' = π_Qold, hh'' = 1, cross terms vanish on distinct
code words, π_Qold + π_Qpad = 1.  Recovery: u = h·ũ·g with
ũ := h''ug'' + e'', so u ∈ H once ũ ∈ H via the kappa/corner
transfer (u = compression of ũ; check compiled pairKappaUnit /
corner lemmas — or prove ũ = ω₁·κ_w(u)·ω₂ for w of depth matching
the pad count and ω's code changes, then use the κ_w-transfer).
STILL TO FORMALIZE: N2 (construction (a)), N3 (reshaped value
window bound), N4 (block-sum/κ_w transfer), N5 (the loop:
induction on 2^{r+1} − κ; codeScalar normalization of a kernel
vector into a B-free column + refine_column, both compiled;
assembly stuckReduction_holds).

## Session 54c: N1–N5 WRITTEN — the chain is closed in Lean (pending compile)

Landed modules (registered in the aggregator, in dependency order):
 - StrictNegativePencil.lean (N1): `entry_window_negative_of_B_full`
   — generated from EntrywiseKill with the downward induction bound
   relaxed from `1 ≤ d` to `0 ≤ d` and windows retargeted to
   `[-N, -1]`.
 - CodeShapeSupply.lean (N2): `exists_complete_deep_family` /
   `exists_deep_code` (size ≥ 2^M, depths ≥ M; fullBinaryCode +
   splits) and `exists_shallow_family` / `exists_shallow_code`
   (1 ≤ κ ≤ 2^r, depths ≤ r; recursive halving with κ₀ = κ − κ/2,
   κ₁ = κ/2, prepending 0/1, sum via cylinder_cons + sum_s_mul_t).
   The shallow construction ELIMINATED the padding/kappa module: in
   the loop κ never exceeds 2^{r+1}, so the full-stack exit needs
   only a shallow column code (≤ r+1) against a deep row code (≥ r).
 - PencilReshape.lean (N3): `reshaped_pencil_mem_iff` +
   `exists_reshaped_pencil` (conjugation by two codePairUnits with
   δ-data = codeBijection units) and `pencilVal_window_mem`.
 - RefineLoopDischarge.lean (N5; N4 obsolete): pencilEntry_mem_window,
   codePair_expansion, pencil_free_exit, pencil_full_exit,
   pencil_unit_mem_pow (induction on the κ-deficit n with
   2^{r+1} ≤ κ + n; branches: free exit / empty-κ contradiction /
   full-stack exit / normalize+refine recursion reusing the
   FullExtraction codeScalar block verbatim), narrowReduction_holds,
   stuckReduction_from_loop (power-of-two row codes), and the
   unconditional corollaries scalarReduction_holds,
   stableUnits_eq_top_holds, glTwo/glFour_eq_elementary_holds.
Manuscript updated: rem:elementaryK1 now describes the two-exit
elimination; the trust-surface paragraph states the K₁ input is
removed entirely with [ABC09] as independent confirmation.
Compile-risk spots for the fix loop: List.cons_prefix_cons name,
Nat.one_le_two_pow, Fintype.card_fun, `group` on units, inv_mem_iff,
rcases on `e p` in depth transports, beta_reduce before rw [hrc],
`rfl` closing the Sum.elim data conversion, set-variable defeq in
hFF/hGG tails.  NOTE: StuckReduction (arbitrary card ι) has a
power-of-two rounding gap in the full-stack exit and is NOT derived;
the main chain does not need it (NarrowReduction proved directly at
full binary codes).  MasterInduction/extraction pipeline retained as
standalone structure theory.

## Session 54d: goal (3) opened — effective Wiener–Hopf factorization

Added rem:effectiveWH to the manuscript: the two-exit elimination as
an effective factorization theorem — every unit of L_k(1,2) is a
central scalar times tree tables (V), code scalars (GL_n(k) along
complete prefix codes), and one tree-table conjugate of a nonpositive
unit; all computable by Gaussian elimination at codes of ≤ 2^{d+2}
words, total time polynomial in 2^d and the monomial count.  Claimed
novelty: no prior effective factorization or elementary proof of
K₁(L_k(1,2)) = 0 in the literature ([ABC09] is neither).
NEXT (goal 3 continuation candidates): (a) Lean-side headline
export naming the factorization (scalarReduction_holds already
packages L^× = k^×·H; a named `unit_factorization` with the factor
inventory would be stronger); (b) generalize the two-exit loop to
L_k(1,n) (n-ary trees — the same pigeonhole gives κ ≤ n^{r+1});
(c) the elementary-width bound for GL_r(L) = EL_r(L).

## Session 54e: GREEN — the K₁ chain is fully verified

Full `lake build`: 3769 jobs, success (two transient SIGTERM-143
resource kills on the way; incremental resume finished).  Axiom
audit: narrowReduction_holds, scalarReduction_holds,
stableUnits_eq_top_holds, glTwo/glFour_eq_elementary_holds,
K1_trivial all depend on [propext, Classical.choice, Quot.sound]
only — no sorryAx, no residual hypotheses.  The six theorems are now
tracked in Audit.lean.  GOAL (1) COMPLETE: the manuscript's K₁ input
is a machine-verified elementary theorem.  N1/N2/N3/N5 compiled
essentially first-try (the compile loop's earlier touches to
PencilReshape/RefineLoopDischarge included the MatrixDiagonalization
open, include k, and omit annotations).


---

<!-- ======== formerly docs/HISTORY.md ======== -->

# Development history

This file is a changelog, kept because the order in which the pieces were
proved is a genuine record of how the argument was found -- and because the
checklists below are the only place several intermediate results are named.
It is not a description of the finished library; for that see the README,
`NonsoficGroupsExist.Public`, and `docs/CLAIM_MAP.md`.

One bullet in the refine-loop entry below is spliced mid-sentence and ends
in `` `s`-free ``.  It is left as written: repairing it would mean inventing
a claim nobody made.

## Full manuscript scope

- [x] Define the universal algebra `L_{𝔽₂}(1,2)` as the presented quotient
- [x] Prove the universal quotient is nontrivial using its stream representation
- [x] Instantiate the full compression construction directly over the universal quotient
- [x] Prove `EL₄(L_{𝔽₂}(1,2))` is nonsofic and has property `(T)`
- [x] Generalize Theorem A to `EL_{m+1}(L_{𝔽₂}(1,2))` for every `m ≥ 1`
- [x] Define `L_k(1,2)` uniformly for every field `k`, prove its universal
  property and nontrivial stream representation, and provide finite-type,
  countability, infinitude, and canonical-family instances
- [x] Prove finite generation, infinitude, property `(T)`, and nonsoficity for
  `EL_{m+1}(L_k(1,2))` over every finite characteristic-two field and every
  `m ≥ 1`
- [x] Prove the complete rank-four compressor, elementary sign correction,
  involution, conjugation, and generation identities over every ring carrying
  a binary Leavitt family, with no characteristic assumption and no `K₁`
  input
- [x] Generalize elementary-root exponent identities and the finite
  class-two stage reduction from exponent two to arbitrary positive bounded
  exponent
- [x] Replace the irreducible class-two sign-character shortcut by a
  characteristic-free cyclic-orbit argument for central commutators of any
  positive bounded exponent
- [x] Replace the finite-dimensional sign-eigenspace recombination by an
  orthogonal irreducible decomposition with dimension induction, so the
  finite class-two `1 / sqrt 2` estimate and the universal class-two
  orthogonality theorem now hold for central commutators of any one positive
  bounded exponent; the former central-involution eigenspace module is
  removed as dead code
- [x] Generalize the entire A₂ vertex-angle, magic-graph defect,
  compressed-Laplacian gap, and root Kazhdan-subset chain from exponent-two
  roots to roots of any one positive bounded exponent; the elementary
  rank-three Kazhdan-subset theorem now holds over every ring of positive
  characteristic, so the remaining characteristic-two dependence is confined
  to the free-root Fourier relative-property-`(T)` transport
- [x] Generalize the free-algebra word-degree filtration (finite stages,
  monotonicity, degree additivity, generator advancement, word monomials,
  exhaustion) from `ZMod 2` to an arbitrary commutative coefficient
  semiring, with stage finiteness for every finite coefficient semiring;
  only the exact-support monomial expansion remains `ZMod 2`-specific
- [x] Generalize the elementary root-subgroup degree stages and the
  generator shear/commutator advancement identities to free algebras over
  every commutative coefficient ring, with stage finiteness for finite
  coefficients
- [x] Prove that property `(T)` forces finite generation: a Kazhdan pair
  tested on the real `ℓ²` permutation representation of the coset space of
  the subgroup generated by its finite set yields a finite symmetric
  generating set containing the identity (`KazhdanFiniteGeneration`); this
  discharges the manuscript's repeated “Kazhdan, hence finitely generated”
  step internally
- [x] Generalize the two-root coefficient planes — subgroup structure,
  finiteness, commutativity, coordinate factorization, exhaustion, and all
  four generator/unit shear conjugation formulas — to every commutative
  coefficient ring, replacing the plane involution law by exponent dividing
  the characteristic; the `±1` Fourier analysis of the planes is now the
  only remaining `ZMod 2`-specific layer
- [ ] Generalize the kernel-checked property-`(T)` theorem from
  characteristic two to arbitrary finite coefficient fields (the only
  characteristic restriction left in the adjacent-rank nonsoficity route),
  through the following checkpoints:
  - [x] A1. Character-mass foundation for finite-field orthogonal
    actions: positivity, conservation, Fourier inversion, and the
    displacement identity over the dual of a finite vector space, relative
    to any nontrivial complex additive character of any finite coefficient
    field (`CharacterMass`)
  - [x] A2. Mass equivariance under conjugating the representation and
    under automorphisms of the acting vector space, the identification of
    the trivial-character mass with the squared norm of the orbit average,
    and the abstract moving-mass gap bound (`CharacterMass`)
  - [x] A3. Simultaneous masses for the two-root coefficient plane over
    every finite coefficient field: the additive parametrization of the
    plane, instantiated positivity/conservation/displacement/gap bounds for
    every orthogonal representation of the elementary group, coordinate
    characters, and nontriviality of a nonzero plane character on one of
    the two coefficient functionals (`FreeRootPlaneMass`)
  - [x] A4. Moving-mass control: an explicit positive character gap
    constant (the finite minimum of `2 * (1 - Re ψ(c))` over nontrivial
    values), and the scalar-orbit theorem bounding the total mass of all
    characters nonvanishing at a vector by the summed squared displacements
    of its scalar multiples, on any acting space and on the plane
    (`CharacterMass.gap_mul_sum_mass_ne_zero_le`,
    `FreeRootPlaneMass.gap_mul_sum_planeMass_ne_zero_le`)
  - [x] A5. Finite-stage character valuation regions `A/B/C/D` over every
    finite coefficient field and the least-detected-degree descent
    (`FreeRootFunctionalValuation`): the functional valuation with its full
    detection calculus, a satisfiability positive control, the sentinel
    characterization of the zero functional, unit-coefficient detection at
    valuation zero, exact stage restriction below the top layer with the
    min-form boundary law, the leading-letter descent by exactly one, the
    canonical least-leading-generator selector with its descent
    specification and restriction invariance, and the five-way
    `zero/A/B/C/D` region partition with exact numerical data and
    constructors for every region
  - [x] A6. Stage-to-stage mass transport under the dual shears: the exact
    fiber covariance law (`CharacterMass.sum_mass_fiber_comp`, with
    group-side orthogonality and mass negation symmetry), the two adjacent
    shears as linear stage maps with their plane-point conjugation
    identities, the forward and opposite plane mass-transport theorems
    (`planeMass_eq_sum_fiber_forwardShear`/`_oppositeShear`), and the
    identification of both dual shears on coordinate functionals with the
    valuation module's restriction and generator-derived functionals
  - [x] A7. The finite-stage Kassabov transport inequalities over every
    finite coefficient field (`FreeRootPlaneMass`,
    `FreeRootFunctionalValuation`): the vanishing-below-valuation law, the
    valuation min rule and negation invariance, the two same-stage unit
    shears with conjugation identities, mass transport, dual coordinate
    formulas and the exact region movements `C → B` and `A → B` in summed
    form, region-`D` control by scalar unit displacements, nested
    trivial-mass monotonicity with the exact boundary-layer drop identity,
    quantitative mass continuity, the two descent classifications into the
    opposite region or `D`, and the assembled region-`B` descent
    inequality charging every coarse `B`-character through the forward
    shear of its canonical least leading generator
    (`sum_planeMass_B_le_sum_fine`)
  - [x] A8. The limiting two-root moving-mass bound over every finite
    coefficient field (`FreeRootPlaneMass`): summed character-mass
    continuity by a bilinear Cauchy--Schwarz argument with no cardinality
    factor (`CharacterMass.abs_sum_mass_sub_sum_mass_le`), the two
    same-vector descent estimates `A ∪ B ≤ C ∪ D` and `C ∪ B ≤ A ∪ D`
    with one generator displacement per alphabet letter, the cross-stage
    region lift, the finite-stage Kassabov estimate
    (`sum_planeMass_nonzero_le_explicit_errors`), the moving-mass
    identity through the stage fixed projections, and the limiting bound
    (`norm_joinRootMovingProjection_sq_le_explicit_errors`): the squared
    moving projection for the join of the two column roots is controlled
    by scalar, unit, and generator displacements alone, at the character
    gap of any nontrivial additive character
  - [x] A9. Property `(T)` for `EL₃` of the free algebra over every
    finite field with an explicit Kazhdan pair
    (`FiniteFieldElementaryPropertyT`): the control set of all scalar-unit
    and generator root elements, the column-plane moving-projection bound
    at the character gap, descent to every finite-type algebra
    (`finiteFieldElementaryThree_hasKazhdanPropertyT`), and the endpoints:
    `EL₄(L_k(1,2))` is nonsofic for every finite field
    (`FiniteFieldLeavitt.ambient_not_isSofic`), and every elementary rank
    `≥ 2` over `L_k(1,2)` is finitely generated, infinite, Kazhdan, and
    nonsofic (`binaryLeavitt_finiteField_profile`)
  - [x] A10. Full build and audit re-run (3678 jobs, 171 modules, kernel
    closure `[propext, Classical.choice, Quot.sound]`); claim map updated:
    Theorem B's elementary-rank claims are Lean-backed for all finite
    fields, and its unit-group/`GL_r` claims over fields other than `𝔽₂`
    are tracked by the `B`-block checkpoints below
- [x] Formalize arbitrary finite-leaf self-similarity: every ring carrying a
  binary Leavitt family has explicit `M_r(R) ≃ R` for every `r ≥ 1`
- [x] Prove nonsoficity of `EL₂` by the all-positive-ranks Leavitt equivalence
- [x] Prove the separate rank-two compression theorem at its stated
  generality: over every countable nontrivial ring carrying a binary Leavitt
  family, if `Aˣ` and the rank-two unit group are Kazhdan and every
  invertible two-by-two matrix is elementary, then `GL₂(A) = EL₂(A)` is not
  sofic; the compressor, involution, generation, commuting-corner, and
  trivial-intersection identities are all proved by explicit two-by-two
  matrix computation, and finite generation of `Aˣ` is derived from its
  Kazhdan pair rather than assumed
- [ ] Prove the GE/`K₁` inputs and `GL_r(L) = EL_r(L)` for all required
  ranks, through the following checkpoints:
  - [x] B1. Monomial normal form for `L_k(1,2)` (`LeavittNormalForm`):
    the monomials `s_α t_β` span, exhibited as a subalgebra containing
    the generators; products of monomials collapse by the prefix
    trichotomy (`span_monomialSet_eq_top`)
  - [x] B2. `L_k(1,2)` is purely infinite simple, in the strong
    two-sided division form `∀ x ≠ 0, ∃ a b, a·x·b = 1`
    (`LeavittSimplicity.exists_mul_mul_eq_one`): basis-free, via the
    cylinder partition of unity, a minimal-length monomial extraction,
    and annihilation of the `s`-tail by the aperiodic word `0^m 1`
  - [x] B3. GE property (`thm:agp`(a)) at rank two, with a short direct
    proof replacing the exchange-ring machinery
    (`MatrixDiagonalization.exists_elementary_mul_diag`): over any
    nontrivial ring with two-sided division of the identity by every
    nonzero element, one column operation makes the `(0,1)` entry
    left-invertible and one row operation plants a literal `1`; every
    `GL₂(L_k(1,2))` element is `E·diag(u,1)·F` with `E, F` elementary
    (`binaryLeavitt_exists_elementary_mul_diag`)
  - [ ] B4. `K₁(L) = 0` in the form used: `diag(u,1) ∈ EL₂(L)` for every
    unit `u`.  Groundwork formalized in `MatrixDiagonalization`: the
    signed swap, the Whitehead lemma `diag(u, u⁻¹) ∈ E₂`, and the
    unipotent Whitehead lemma `diag(1 + ab, 1) ∈ E₂` when `ba = 0` (which
    puts every prefix-code transvection image `1 + s_w r t_{w'}` in the
    kernel of the diagonal class map).  Newly drafted in
    `DiagonalClassGroup` (pending cluster verification): the subgroup
    `stableUnits R = {u : diag(u,1) ∈ EL₂}` as a comap along the
    diagonal embedding homomorphism, its normality in `Rˣ` (diagonal
    conjugates of transvections are transvections), and — under strong
    division, via the proved rank-two GE theorem — normality of `EL₂`
    in `GL₂` (`elementaryGroup_normal_of_division`), which yields the
    `κ_w`-stability `κ_w(u) ∈ H ⟺ u ∈ H` since
    `X·diag(u,1)·X⁻¹ = diag(κ_w(u),1)` for the explicit
    `X = [[s_w, 1−p_w],[0, t_w]]`.  The Leavitt-side layer is now also
    drafted (`LeavittDiagonalClass`, pending cluster verification):
    corner-insertion units `kappaUnit`, the explicit intertwiner with
    its inverse, the conjugation identity
    `X_w·diag(u,1)·X_w⁻¹ = diag(κ_w(u),1)`, the coset identity
    `κ_w(u)·u⁻¹ ∈ stableUnits` as a commutator via the abelianity of
    `GL₂/EL₂` (`commutator_mem_elementaryGroup_of_division`, itself
    from three Whitehead lemmas through
    `diagPair u u⁻¹ · diagPair v v⁻¹ · (diagPair (vu) (vu)⁻¹)⁻¹`), the
    corner-sum factorization `κ₀(u)·κ₁(u) = s₀ut₀+s₁ut₁`, the central
    scalar collapse (`central_mem_stableUnits`), and the reduced form
    `stableUnits_eq_top` consuming one named hypothesis.  The
    rose-graph `K₁` computation itself (the manuscript's cited
    `[AraBrustengaCortinas09]` input) is now formalized through its
    degree-zero half, all cluster-verified: `StableUnitsGenerators`
    (corner insertion along any one-sided-inverse pair, with the
    `GL₂`-intertwiner coset identity, and unipotent units
    `1 + a·b`, `b·a = 0`, in the diagonal class),
    `FamilyDiagonalClass` (the subgroup `centralClassGroup` of units
    that are a central scalar times a diagonal-class element — the
    rose input says exactly that it is everything; transvection and
    central-diagonal pullbacks through any `CompleteMatrixFamily`,
    by a Finset-induction corner-sum factorization),
    `FieldMatrixReduction` (any unit identified by a family with a
    matrix of central field coefficients lies in `centralClassGroup`,
    via Mathlib's transvection decomposition — Gaussian elimination
    over the field), and `LeavittDegreeZero` (the full depth-`n`
    binary prefix code is complete; units with value in the balanced
    span `span{s_α t_β : |α|=|β|=n}` have scalar matrix entries and
    hence lie in `centralClassGroup`).  Combined with the central
    collapse `c̄ = c̄²` this puts every degree-zero unit in `H`.
    The Laurent width-reduction is now FORMALIZED
    (`LeavittWindowReduction`, `BinaryLeavittWindow`: every unit
    narrows to degrees `[-1,1]` mod the diagonal class), as are
    graded independence over every field (`ScaledStreamRepresentation`,
    `VandermondeExtraction`, `GradedIndependence`,
    `BaseChangeIndependence`), stable rank one with its balanced
    transport (`StableRankOne`, `BalancedStableRank`), the Whitehead
    flip `[1+xy] = [1+yx]` (`WhiteheadFlip`), the residual normal-form
    transports (`ResidualNormalForm`, `ResidualMoves`), balanced von
    Neumann regularity with the square-zero-tail kill
    (`BalancedRegularity`), and the descent at every matrix size
    (`FamilyDescent`).  The whole chain is wired in
    `ResidualReduction`: the single remaining input is
    `NarrowReduction` (units with value in the `[-1,1]` window lie in
    the central class group), from which `ScalarReduction`, B4, and
    `GL₂/GL₄ = EL₂/EL₄` all follow by formalized theorems.  The
    `NarrowReduction` program (attack log in
    `BUILD_ITERATION_NOTES.md`; the most recent modules are written
    and registered, pending the next green build):
    - [x] Theorem (P), the keystone (`ZeroKOne`
      `balanced_component_isUnit`): balanced parts of `[0,1]`-window
      units are invertible — the elementary replacement for the cited
      `[AraBrustengaCortinas09]` input, via the rank normal form,
      graded inverse components, downward elimination to a corner
      identity, and a geometric shape-matrix rank contradiction
    - [x] pure-tail nilpotency (`PureTailNilpotency`), the κ-corner
      transports, the nilpotent-tail kill (`NilpotentTailKill`), and
      the width-two window kill (`WidthTwoReduction`)
    - [x] `GammaDischarge`: units `1 + s₁(z₋ + z₀)` lie in the class
      group, discharging the earlier γ-reduction hypotheses
    - [x] the generalized block-move kill (`BlockMoveTailKill`,
      `WindowNonnegReduction`): every `[0, N]`-window unit lies in
      `H`, for every `N` and arbitrary balanced part
    - [x] the θ anti-automorphism with elementary-group stability and
      the mirrored `[-N, 0]`-window kill (`OppositeTranspose`,
      `ThetaStable`, `WindowNonposReduction`)
    - [x] code-change units and the Higman–Thompson generation
      theorem (`CodeChangeInfrastructure`, `CodeChangeSwap`,
      `CodeChangeUnits.codeChange_mem_stableUnits`): the value of any
      complete-code pair list is a unit of the diagonal class group
    - [x] the rank-one normal form (`RankOneNormalForm`): every
      narrow unit is equivalent mod `H` to one of value `w + s₁t₀₀`
      with `w` in the `[0,1]` window, by the stable block move with
      `P` the whole degree `-1` part and `Q = 1` through the
      mixed-depth code `{00, 01, 1}` — no invertibility hypotheses
    - [x] the structure theorem for nonnegative narrow units
      (`NonnegUnitStructure`): every `[0,1]`-window unit factors as
      (invertible balanced)·(unipotent with nilpotent pure tail);
      inverses of such units have nonnegative windows
    - [x] the pencil move generators (`PencilCore`): scalar-matrix
      embeddings and disjoint-support block unipotents transport
      into `H` through the depth-`n` matrix picture
    - [x] the scalar-pencil form (`PencilForm`): at a deep corner
      level every narrow element is a word-indexed matrix with
      entries `A₀ᵢⱼ•t₀ + A₁ᵢⱼ•t₁ + Cᵢⱼ•1 + B₀ᵢⱼ•s₀ + B₁ᵢⱼ•s₁` for
      five scalar matrices
    - [x] the window dichotomy (`WindowDichotomy`): if the degree
      `+1` part is left-full (`g₀(t₀b) + g₁(t₁b) = 1`) then the
      inverse has a nonpositive window and the unit lies in `H`;
      mirror when the degree `-1` part is right-full — the two
      terminal branches of the elimination
    - [x] the code-pair transport (`CodePairTransport`): matrix data
      indexed by two complete prefix codes of different sizes
      multiplies by middle-code collapse; rectangular two-sided
      inverse pairs transport to units (`codePairUnit`) — the
      Leavitt `L^p ≅ L^q` mechanism the recursion runs on
    - [x] scalar moves along arbitrary mixed-depth codes
      (`CodeScalarMoves`): the transport of every invertible scalar
      matrix along any complete prefix code is a unit of `H` —
      transvections become incomparable unipotents, diagonals become
      products of κ-corner insertions of central scalars, assembled
      through Mathlib's transvection decomposition
    - [x] code-relative fullness witnesses (`CodeRelativeFullness`):
      scalar one-sided inverses of the stacks `[B₀;B₁]` / `(A₀|A₁)`
      transport to one-sided inverses of the degree `±1` pencil parts
      through `codePair_mul` and the corner pairing
      `(t-combo)·(s-combo) = scalar` — feeding the window dichotomy
      at every refinement stage
    - [x] the atom peel (`AtomPeel`): a unit whose pencil has a
      normalized `[t₀; t₁]`-column factors as (code-change unit in
      `H`) · (pencil unit over one fewer row) — the split source
      family, its prefix-freeness and completeness, the three
      collision patterns against the intermediate code, and the
      exact row-collapse factorization `u = u₁ · (u₁⁻¹ u)`
    - [x] the peel-normalization toolkit: block unipotents along any
      prefix code (`MixedCodeMoves.code_unipotent_mem`), the shift
      rigidity `x·(λ₀•t₀+λ₁•t₁) ≠ 1` forcing independent column
      pairs, the invertible-matrix normalization of an independent
      pair to standard atoms (`GLPairNormalization`), and the
      coefficientwise action of transported scalar matrices on the
      five pencil matrices (`PencilEntryArith`)
    - [x] complete-code supply and vector normalization
      (`CompleteCodeSupply`, `GLVectorNormalization`): complete
      prefix families of every positive size by iterated splitting,
      and any nonzero vector as a column of an invertible matrix
    - [x] the row-clearing move (`RowClearMove`): once a column
      carries the exact shift atom, one square-zero block unipotent
      erases the atom rows everywhere else — collision lemmas,
      `t_z`-collapses, and the full value computation splitting both
      double sums at the distinguished rows
    - [x] the extraction step (`FullExtraction.full_extraction`): a
      kernel vector of the scalar stack `[B₀;B₁;C]` yields a pencil
      unit over one fewer row with equivalent class-group
      membership — right scalar move, independence of the `t`-pair
      forced by column left-invertibility against the shift
      rigidity, left scalar move onto standard atoms, the
      row-clearing block unipotent, and the atom peel, composed
    - [x] the ς-mirror (`MirrorExtraction`): `θ̂` transposes pencils
      (swapping `t`- and `s`-data), so a kernel vector of the row
      stack extracts through the transposed side and transports
      back — one fewer column, equivalent membership
    - [x] the inner-node dichotomy engine (`EntryStrip`,
      `EntrywiseKill`): strip equations `Σⱼ xᵢⱼ·y_{ji'} = δᵢᵢ'`
      through any complete code, and the entrywise graded kill — a
      scalar left inverse of `[B₀;B₁]` annihilates every positive
      component of every inverse entry, at arbitrary mixed-depth
      codes (the mixed-code replacement for the window dichotomy)
    - [x] the terminal node (`BalancedCodePencil`,
      `StackDichotomy`, `RefinedCodes`): word-combination
      independence, the stack dichotomy (scalar left inverse or
      kernel vector), uniform code refinements, and the terminal
      theorem — a unit whose inverse has balanced corner entries
      factors as (code bijection)·(scalar move): the scalar matrix
      is forced square and invertible because a kernel vector would
      give a vanishing column/row of a unit
    - [x] the mirrored kill and the window intersection
      (`EntrywiseKillMirror`): θ̂ flips windows, so a right inverse
      of `(A₀|A₁)` pins inverse entries nonnegative; nonpos ∧ nonneg
      = balanced by component uniqueness
    - [x] the master induction (`MasterInduction.pencil_unit_mem`):
      strong induction on total code size — extraction/mirror
      branches recurse, both-stacks-full reaches the terminal, and
      the single refinement configuration is isolated as the named
      hypothesis `StuckReduction`
    - [x] the master-induction discharge (`NarrowDischarge`):
      `NarrowReduction k` now follows from the single named
      statement `StuckReduction k` — the ENTIRE `K₁`-vanishing chain
      (`NarrowReduction → ScalarReduction → B4 → GL = EL`) rests on
      one remaining Prop
    - [x] strict negativity (`StrictNegativePencil`): a full `B`-stack kills the balanced entry components too — the inverse entries live in `[-N, -1]`
- [x] code-shape supply (`CodeShapeSupply`): deep codes (any size `≥ 2^M`, depths `≥ M`) and shallow codes (any size `≤ 2^r`, depths `≤ r`, by recursive halving)
- [x] pencil reshaping (`PencilReshape`): code-pair conjugation preserves the class group; value-window bound over depth-controlled codes
- [x] the refine-loop discharge (`RefineLoopDischarge`): free exit + strict-negative full-stack exit + the bounded column-growth loop — **`narrowReduction_holds`: the entire K₁-vanishing chain (`ScalarReduction`, checkpoint B4, `GL = EL`) closes UNCONDITIONALLY** — **BUILD VERIFIED GREEN** (full `lake build`, 3769 jobs; `narrowReduction_holds`, `scalarReduction_holds`, `stableUnits_eq_top_holds`, `glTwo/glFour_eq_elementary_holds`, `K1_trivial` all audit to `[propext, Classical.choice, Quot.sound]` only, tracked in `Audit.lean`) (no padding, no extraction, no termination measure; the master-induction/extraction pipeline remains as standalone structure theory): `s`-free
      pencil columns split into their two children (the Wiener–Hopf
      index shift — a pure re-indexing, no multiplication), and the
      extracted middle re-transports along mixed-size complete codes
      to an honest narrow unit of strictly smaller pencil size;
      machine-tested (120/120 random narrow units reach extraction
      within ≤ 2 refinements) — the termination proof and the
      code-relative statements remain to be written
    - [ ] `NarrowDischarge`: assemble the trichotomy (window-kill /
      extract / refine-and-recurse) into `NarrowReduction k`, closing
      the chain `NarrowReduction → ScalarReduction → B4 → GL = EL`
    - [ ] cleanup: retire or derive the `TriangularFactorization`
      scaffolding from the completed pipeline, refresh the stale
      docstrings on the three main theorems, clear the audit flags,
      and re-run the full build
  - [ ] B5. `L^×` perfect and `GL_r(L) = EL_r(L)` for every `r ≥ 2`
    (`prop:glel`).  Route fixed: `GL₄(L) = GL₂(M₂(L))` and `M₂(L) ≅ L`
    inherits the strong division property through the self-similarity
    isomorphism, so the proved rank-two GE theorem applies over `M₂(L)`;
    block transvections and block diagonals decompose into ordinary
    `E₄`-elements, giving `GE_r` for `r ∈ {2, 4}` without a general-rank
    induction; perfection of `L^×` awaits the `B4` input
  - [ ] B6. Discharge the rank-two theorem's GE and property-`(T)`
    hypotheses over every finite field; audit
- [x] Prove the full unit group and every positive-rank `GL_r` nonsofic
- [x] Prove every finitely generated nonsofic group has a finitely presented
  nonsofic cover
- [ ] Formalize Shalom's property-`(T)` finitely presented cover theorem
  and the Theorem C refinement, through the following checkpoints:
  - [x] C1. Property `(T)` descends along surjections in the repository's
    Kazhdan-pair form (`HasKazhdanPropertyT.of_surjective` in
    `Kazhdan.lean`: push the Kazhdan set forward along the surjection,
    pull representations back)
  - [x] C2. Shalom's theorem: every Kazhdan group is a quotient of a
    finitely presented Kazhdan group.  Fully formalized and built:
    `Shalom.exists_presented_kazhdan_cover` (presentation-exposed form)
    and `exists_finitelyPresented_kazhdan_cover`, via
    `exists_displacement_one_of_witness` (a single-witness
    strengthening of Bekka–de la Harpe–Valette Lemma 3.2.5 that
    eliminates the ℓ²-direct-sum step), Delorme's theorem
    (`exists_fixed_point_of_hasKazhdanPropertyT`, through the abstract
    Gaussian boundedness principle
    `bounded_of_gaussian_isPositiveDefinite`), Gaussian
    positive-definiteness by the Schur product theorem
    (`GaussianPositiveDefinite`), Chebyshev circumcenters
    (`HilbertCircumcenter`), and a scalar-hyperreal ultralimit
    (`UltralimitGeometry`) replacing the Banach ultraproduct and the
    reduced-cohomology step of the cited proof
  - [x] C3. The Kazhdan finite-table cover (`thm:kcover`), formalized
    and built (`exists_kazhdan_finitelyPresented_nonsofic_cover` in
    `KazhdanCover`): the forbidden-table relators are imposed on the
    Shalom presentation, the family pullback `familyPullbackModel`
    transfers nonsoficity, and finite generation is derived from
    property `(T)` internally rather than hypothesized.  The final
    Theorem C quotient claims (surjections onto the Theorem B list)
    await the `B4` scalar input
  - [x] C4. Audit: the full aggregator builds (3690 jobs), the source
    scan passes, and the kernel audit covers 6575 declarations with
    closure exactly `[propext, Classical.choice, Quot.sound]`, all
    scans at zero and the structural-`Nonempty` ratchet tightened to
    the audited count
- [x] Define Thompson's group `V` and identify the manuscript's tree-table
  and corner copies with it (the existence proof currently uses a stronger
  direct finite obstruction instead), through the following checkpoints:
  - [x] D1. Thompson's `V` defined concretely (`ThompsonV`): the
    boundary `{0,1}^ℕ`, stream prefixes, the covering property of a
    binary prefix code with unique covering indices, the prefix
    substitution bijection of a tree table (`tableEquiv`), and
    `thompsonV` as the subgroup of boundary permutations generated by all
    tree tables
  - [x] D2. The Leavitt tree-table units realize a faithful copy of `V`
    (`ThompsonVEmbedding`, `prop:vembed` embedding half): covering codes
    are complete in every Leavitt family, the finitely supported stream
    representation is faithful by simplicity, each tree table gives a
    unit `Σ s_{β_i} t_{α_i}` acting on basis vectors exactly by its
    prefix substitution, the basis-permuting units map to boundary
    permutations with trivial kernel, and `V` embeds in `L_k(1,2)^×`
    (`vEmbedding`, `vEmbedding_injective`)
  - [x] D3. The corner witness identified inside `V`
    (`ThompsonVWitness`): every cylinder swap acts on the stream basis as
    the boundary transposition (`finsuppStreamRep_cylinderSwap_single`),
    corner insertion carries swaps to swaps of the inserted cylinders,
    the two-generated witness subgroup lies in the basis-permuting units
    (`cornerWitness_le_deltaPermUnits`), and every cylinder transposition
    is a tree table (`swapPerm_mem_thompsonV`)
  - [x] D4. **`prop:vnotlef`, unconditionally**: Thompson's group `V` is
    not LEF (`thompsonV_not_isLEF`), audit-pinned.  The manuscript
    derives this from the cited simplicity and finite presentability of
    `V`; here it is kernel-checked with no cited inputs: LEF passes to
    subgroups (`isLEF_of_injective`) and the finite-obstruction witness
    embeds into `V` through the faithful stream action
  - [x] D5. Audit re-run: 6295 declarations, kernel closure exactly
    `[propext, Classical.choice, Quot.sound]`, all scan budgets at
    baseline, `thompsonV_not_isLEF` statement-pinned
- [x] State and prove the bounded-degree form of the expander decomposition:
  the edited multigraphs carry one explicit occurrence-counting degree bound
- [x] Align every TeX theorem and verification claim with its exact Lean
  declaration or an explicit manuscript-only status: see the
  “TeX ↔ Lean alignment” table below
- [ ] Re-run the complete MSI build and final axiom/source audit after all
  manuscript-scope additions

## Proof status

Checked boxes below mean that the corresponding code has a genuine Lean proof
term and its module has compiled with warnings treated as errors. Manuscript
claims not yet formalized are listed separately in “Full manuscript scope.”

- [x] Standard finite Hamming approximation and soficity infrastructure
- [x] LEF definitions and the finite non-LEF obstruction
- [x] Explicit cylinder-transposition non-LEF subgroup
- [x] Injective embedding of that subgroup into the universal-Leavitt `EL₃` core
- [x] Universal rank-four compression maps and compressor identities
- [x] Characteristic-free elementary compressor and involution words, using
  an explicit Leavitt-unit commutator equal to scalar `-1`
- [x] Closed `UniversalRankFour.compressionSetup`
- [x] Finite-table theorem turning a finitely generated nonsofic group into a
  finitely presented nonsofic cover
- [x] GNS/Kazhdan finite-model contraction and rounding infrastructure
- [x] Terminating Kun finite partition recursion and cut accounting
- [x] Six-vertex A₂ magic graph and its exact Laplacian estimates
- [x] Class-two orthogonality estimate for central commutators of any one
  positive bounded exponent (instantiated at exponent two by the
  characteristic-two route)
- [x] Strict A₂ local and global moving-energy defect
- [x] Genuine Hilbert direct sum, fixed-family subspace, and compressed
  Laplacian
- [x] Real-Hilbert positive-operator gap proved by a convergent Neumann
  iteration (no spectral assumption)
- [x] Positivity, symmetry, and trivial kernel of the compressed A₂
  Laplacian
- [x] Strict moving-energy defect applied to prove the compressed quadratic
  operator gap
- [x] Explicit inverse norm bound for the compressed Laplacian, derived by
  the kernel-checked positive-operator iteration
- [x] Uniform A₂ constant-family/vertex projection bound with an explicit
  contraction factor below `1`
- [x] Transfer the projection contraction to strict vertex codistance and a
  genuine Kazhdan-subset bound for the union of the six root subgroups
- [x] Instantiate the root Kazhdan-subset theorem for the elementary
  rank-three group over every ring of positive characteristic; no
  exponent-law premise remains
- [x] Construct finite word-degree stages of the free characteristic-two
  algebra and prove that they are finite, monotone, and exhaustive (the
  algebraic filtration for the relative-property-`(T)` proof)
- [x] Prove multiplication adds free-word degree bounds and multiplication by
  each free generator advances the finite filtration by one stage
- [x] Construct finite, monotone degree stages inside every elementary root
  subgroup and prove that their supremum is the full root subgroup
- [x] Prove the exact elementary shear/conjugation identity and that
  commutation with each free-ring generator advances root degree by one
- [x] Build the finite two-root coefficient planes, prove that they exhaust
  the full additive plane, and prove the generator shear sends stage `n` to
  stage `n+1` by the explicit coefficient formula; prove separately, as
  ambient elementary-matrix equalities, that the shear fixes the first
  coordinate and sends the second coordinate to the precise first-times-second
  factorization in the next stage
- [x] Construct the positive/negative Hilbert-space splitting for represented
  involutions and prove orthogonality, Pythagoras, displacement, and
  conjugation covariance without a finite-dimensional spectral assumption;
  prove the resulting sign projections are idempotent, complementary, and
  pairwise commuting for commuting involutions
- [x] Iterate the involution splitting over an arbitrary finite family and
  prove exact vector reconstruction and conservation of total squared norm
  across all binary sign components; for commuting families, prove every
  component is a simultaneous eigenvector with exactly its assigned signs
- [x] Prove the simultaneous decomposition is covariant under conjugating the
  entire family, prove distinct sign components are pairwise orthogonal, and
  identify the squared norm of every finite subfamily sum with its exact
  component-mass sum; identify the mass of characters taking value `-1` on
  any finite-plane element with exactly one quarter of that element's squared
  displacement
- [x] Prove quantitative finite-stage character-mass transport under each
  free-generator shear: the next-stage sheared event and the original
  coordinate event differ by at most `2 * ‖z‖` times the displacement of `z`
  under that single elementary generator
- [x] Prove every finite free-root plane is abelian of exponent two, enumerate
  all of its elements, and instantiate the simultaneous Fourier decomposition
  and sign-action theorem for that exhaustive enumeration; prove every
  nonzero component's assigned `±1` eigenvalues are multiplicative and send
  the identity to `1`
- [x] Factor every finite-plane element through its two coefficient roots and
  derive genuine additive `𝔽₂` coefficient characters (addition maps to sign
  multiplication and zero maps to `1`) on every nonzero Fourier component;
  prove every nontrivial plane character is nontrivial on at least one of the
  two coefficient coordinates
- [x] Expand each degree-bounded free polynomial in its exact supported-word
  basis and prove that any nontrivial additive sign character is already
  detected on one of those supported word monomials; decompose every
  positive-degree witness into its first free generator and strictly shorter
  tail, with the corresponding exact monomial factorization
- [x] Define Kassabov's finite-stage character valuation as the least detected
  free-word degree (using `n+1` exactly for a stage-trivial character), prove
  valuation zero is precisely unit-coefficient detection, define the four
  `A/B/C/D` valuation regions, and prove a nonzero component with nontrivial
  plane character has at least one valuation at most `n`; prove the exact
  leading-letter lemma that a positive valuation has a generator-derived
  character whose valuation is smaller by exactly one
- [x] Enumerate the finite free-generator alphabet, collect every generator
  realizing exact valuation descent, prove that set is nonempty whenever the
  valuation is positive and detected, and define a canonical least-index
  selector with its exact descent theorem
- [x] Separate the all-trivial character pair into its own `zero` region
  (rather than incorrectly counting it in `B`), partition `A ∪ B` and `C ∪ B`
  into exact pairwise-disjoint least-leading-generator fibers, and prove both
  finite-stage dual shear formulas carry every fiber into Kassabov's required
  opposite-or-`D` valuation regions
- [x] Prove simultaneous sign projections are additive over finite sums,
  select joint eigenvectors exactly, and instantiate the resulting refinement
  theorem to show each degree-`n` plane component is the exact sum of all
  compatible degree-`n+1` Fourier components
- [x] Construct the concrete forward and opposite conjugated-plane maps into
  the next filtration stage, re-index them in the exhaustive enumeration, and
  prove exact Fourier covariance: an acted-on coarse component is the sum of
  precisely its conjugated fine extensions; identify both restricted
  coefficient characters with the algebraic dual shears and prove the
  transported valuation-region conclusions for every nonzero fine component
- [x] Prove exact squared-mass conservation for arbitrary coarse sign sets
  under refinement and conjugation, derive both concrete per-leading-fiber
  mass bounds, and prove that below the top-degree boundary restriction
  preserves every leading generator and the canonical least leading index
- [x] Prove the actual transported leading-fiber image sets are pairwise
  disjoint below the top-degree boundary, charge each interior fiber only to
  its concrete image set, and prove arbitrary selected Fourier projections
  are contractive and have the required squared-mass continuity estimate
- [x] Prove that every nonmultiplicative binary sign assignment has zero
  Fourier component, remove those invalid assignments from both transported
  image families, prove the valid images lie in the required target regions,
  and derive the two disjoint below-boundary mass-sum inequalities with the
  target mass counted once rather than once per free generator
- [x] Identify each top-degree boundary as the exact drop of a nested
  nonnegative trivial-character mass, prove both boundary masses tend to
  zero, and combine them with the disjoint interior estimates into the two
  full finite-stage Kassabov inequalities
- [x] Construct the two same-stage unit-root conjugations, prove their exact
  Fourier transport sends `A` and `C` into `B`, and bound region `D` by the
  two unit-coordinate displacements
- [x] Prove ordinary refinement preserves every valid valuation region away
  from the two new top-degree layers, charge coarse target mass to the
  same-stage target plus those already-vanishing layers, and combine both
  generator shears with the unit shears into a single explicit finite-stage
  bound for all four nonzero valuation regions
- [x] Pass the finite-stage inequalities to the limiting two-root moving
  mass and complete the uniform relative-property-`(T)` estimate
- [x] Prove property `(T)` for elementary rank three over every finite-rank
  free characteristic-two algebra, using an explicit finite Kazhdan set
- [x] Transfer/instantiate property `(T)` for every universal-Leavitt group used by the
  compression argument
- [x] Close the exact full-sequence Kun expander-decomposition theorem used at the final
  criterion boundary
- [x] Close the exact Kun--Thom centralizer/LEF implication used at the final
  criterion boundary
- [x] Assemble an unconditional universal-Leavitt nonsofic group with no setup,
  literature theorem, property-(T), or non-LEF premise
- [x] Instantiate the finite-table cover to obtain an unconditional finitely
  presented nonsofic group
- [x] Add the two unconditional public headline declarations
- [x] Run the complete `lake build` for the premise-free existence baseline
- [x] Audit the baseline closed headline signatures and run `#print axioms`
- [x] Search the baseline for and eliminate forbidden trust bypasses, stale
  conditional wrappers, dead code, and misleading documentation

The final two declarations have exactly these premise-free mathematical
types:

```lean
theorem nonsofic_groups_exist : NonsoficGroupExists := by
  ...

theorem exists_finitelyPresented_nonsofic_group :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬ IsSofic G := by
  ...
```

The current complete MSI build reports `Build completed successfully (3678
jobs).` The transitive axiom reports for both headline theorems and for
`universalLeavittEL4_not_isSofic` are exactly
`[propext, Classical.choice, Quot.sound]`; there is no project axiom or
unproved placeholder in either proof term. The source audit finds no
declaration of a custom axiom, no proof placeholder, and none of the former
literature-hypothesis parameters. The remaining `KunThomTheorem` matches are
the module and namespace containing the compiled proof, not an assumed
proposition interface. The source audit covers all 171 project modules, and
the whole-namespace kernel audit traverses every project declaration and
reports no disallowed axiom. This build and audit are
the current universal-quotient integration checkpoint; both will be rerun after
each later manuscript-scope checkpoint.

## What is already formalized

What is kernel-checked includes finite Hamming/sofic bookkeeping, localization,
finite-table covers, the universal binary Leavitt quotient and its canonical
family, elementary-matrix embeddings and compression maps, and a genuine
two-generator non-LEF subgroup built from cylinder transpositions.  That
subgroup is embedded injectively into the universal-Leavitt `EL₃` core by explicit
commutator and Whitehead identities.  The rank-four compressor words satisfy
the required conjugacy identities, generate the ambient `EL₄` together with
the core, and have the required centralization and trivial-intersection
properties. `UniversalRankFour.compressionSetup` assembles these facts into a
closed algebraic setup.

The rank-four compressor and involution are now explicit elementary words in
every characteristic. The only sign formerly supplied by characteristic two
is obtained from a proved commutator of two concrete Leavitt units and the
Whitehead identity. Thus the remaining finite-field restriction comes from
the current property-`(T)` formalization, not from compressor membership or
matrix identities.

The analytic development also constructs the GNS Hilbert space of every
limiting sofic correlation, proves the iterated Kazhdan contraction there,
uniformizes it back to all sufficiently large finite models, and controls the
approximate-multiplication error between exact group words and the actual
finite permutation Markov operator.  Consequently, genuine finite-model
Markov displacements satisfy an arbitrarily strong contraction, uniformly over
every centered indicator, with arbitrarily small normalized additive error.  The
one-step displacement is now related to the genuine directed generator-cut
energy, and centering has been eliminated from the threshold-rounding input.
Finite coarea rounding, maximal-bad-set removal, and finite support propagation
are also kernel-checked.  A geometric-series movement estimate now keeps the
replacement-set proximity coefficient independent of the Markov horizon; a
second maximal-bad-set argument removes its additive finite-model error.  The
resulting rounding theorem therefore has a fixed admissible input-cut
threshold even as the requested boundary ratio tends to zero.  Kun's complete
terminating finite partition recursion constructs blocks with a uniform global
cut inequality and a linear small-boundary budget.  The development charges
all inter-block generator edges to exceptional incidence or reference cuts,
constructs an explicit edit witness, performs the selective matching repair,
and proves uniform componentwise expansion.  A slowly growing accuracy level
does this on every model of the original sofic approximation; the theorem does
not discard to a cofinal subsequence.

No decisive mathematics remains hidden behind theorem-shaped parameters. The
exact Kun expander decomposition and Kun--Thom implication are
now proved and compiled. The finite-stage Fourier argument has also been
passed to the exhaustive free-root plane and yields an explicit finite
Kazhdan pair for elementary rank three over every finite-rank free
characteristic-two algebra. The universal quotient map from the free algebra
transfers this property to the universal-Leavitt `EL₃` core, and the explicit
Leavitt rank equivalence transfers it to the `EL₄` ambient group. The stream
representation is used only to prove that the presented quotient is
nontrivial. The non-LEF witness is not yet identified with Thompson's group
`V`; the closed existence proof instead uses its directly proved finite
obstruction.

`TableCover` proves that a finitely generated nonsofic group has a finitely
presented nonsofic cover. `MainResults` instantiates it with
`EL₄(L_{𝔽₂}(1,2))`, proved nonsofic by the closed compression criterion.



---

<!-- ======== formerly docs/REORGANIZATION.md ======== -->

# Phase 2: directory structure mirroring the manuscript

`NonsoficGroupsExist/` is 256 modules in one flat directory, ordered by the
sequence the mathematics was discovered in.  `scripts/reorganize.py` moves
them into eleven directories that track the paper's sections, rewriting every
import as it goes:

```
python3 scripts/reorganize.py          # print the plan; changes nothing
python3 scripts/reorganize.py --apply  # git mv + rewrite imports
```

The assignment is by hand, in `LAYOUT`, because the import graph does not
determine it: `FiniteGraph` is used by the Kun layer and the matching toolkit
alike, and only the manuscript says which section it belongs to.  The script
refuses to run with any module unassigned — a leftover `Misc/` is not a home
chosen on purpose.

## Status: done

The move has been made and the manuscript follows it.  What is written below
is the record of what the blocker was and how it was removed, kept because the
same shape recurs whenever the two artefacts move relative to each other.

## What the blocker was

**The manuscript pointed into the flat directory.**  Two things broke the
moment a module moved:

1. **Every margin-note hyperlink 404s.**  `\leanfileurl` in the preamble is

   ```latex
   \newcommand{\leanfileurl}[1]{%
     https://github.com/SauersML/nonsofic_existence/blob/main/NonsoficGroupsExist/#1.lean}
   ```

   It appends `.lean` to a bare module name.  After the move the file is at
   `NonsoficGroupsExist/Leavitt/Whitehead.lean`, and the paper links to
   `NonsoficGroupsExist/Whitehead.lean`, which no longer exists.  189
   declaration references across 82 modules are affected.

2. **`scripts/check.py` reports every one as a dangling reference**, because
   `\leanmod{Whitehead}{...}` no longer names a module.  That gate also runs
   in the PDF build, so the manuscript stops building.

Both were the checks working: exactly the drift they exist to catch.

## How it was removed

Half of it did not need the manuscript at all.  `claim_map.module_path`
resolves a note's module by path *or* by bare name, searching the tree, so
moving a module is no longer a dangling reference on its own — the checks
follow it wherever it goes.  That is the half worth keeping: it means a future
move costs nothing here.

The hyperlink genuinely needed the `.tex`.  `\leanfileurl` appends `.lean` to
whatever a note names, so a note naming `Whitehead` links to the old flat
path.  Notes now name `Leavitt/Whitehead`, which `\leanfileurl` handles
unchanged — 117 mechanical string edits, no macro change, no mathematics
touched.  The margin displays the path, which reads no worse than the bare
name and says more.

Sequencing: the move and the note rewrite belong in **one commit**, or CI is
red in between.  `docs/CLAIM_MAP.md` is generated, so it follows on its own.

## The eleven directories

| Directory | Backs | Modules |
| --- | --- | --- |
| `Sofic/` | `sec:prelim` | 10 |
| `Kazhdan/` | `subsec:sofic` | 22 |
| `PropertyT/` | `thm:ejz` | 33 |
| `Kun/` | `thm:kun` | 32 |
| `KunThom/` | `thm:kunthom` | 7 |
| `Matching/` | `sec:toolkit` | 39 |
| `Criterion/` | `sec:criterion` | 7 |
| `Leavitt/` | `sec:leavitt` | 42 |
| `KOne/` | `app:K1` | 59 |
| `Covers/` | `sec:fp` | 2 |
| `Endpoint/` | `sec:intro` | 3 |

---

## 2026-08-08 — Thom's monomial models: exact permutationization is impossible

Let

\[
  K=K_0(\mathbf Z[1/p])/\mathbf Z
\]

be Thom's explicit hyperlinear group.  In the second proof of Proposition 3.2
of Thom (arXiv:0810.2180), a finite window with denominators at most `p^k` is
modelled through `K_0(Z/qZ)`, where `(p,q)=1`.  Put

\[
  c_q=\pi_q(1/p^k),\qquad z_q=\pi_q(1)
\]

in the cyclic central subgroup `Z/qZ`.  Then

\[
  c_q^{p^k}=z_q,\qquad c_q^q=1.
\]

### Fixed-support lemma

If `s` is a permutation with `s^q=1` and `(a,q)=1`, then

\[
  \operatorname{Fix}(s^a)=\operatorname{Fix}(s).
\]

Indeed every cycle length `ell` of `s` divides `q`, hence `(a,ell)=1`; the
power `s^a` acts transitively on exactly the same cycles as `s`.  Equivalently,
choose `b` with `ab = 1 mod q`; then `s=(s^a)^b`, giving both fixed-set
inclusions.

### Consequence for Thom's finite models

For every permutation representation

\[
  \rho:K_0(\mathbf Z/q\mathbf Z)\longrightarrow \operatorname{Sym}(X),
\]

the permutations `rho(c_q)` and `rho(z_q)` have exactly the same fixed points:

\[
  \operatorname{Fix}(\rho(c_q))
   =\operatorname{Fix}(\rho(c_q)^{p^k})
   =\operatorname{Fix}(\rho(z_q)).
\]

This remains true after arbitrary direct sums, inductions, product actions, or
any other construction that is still an exact permutation representation of
the finite quotient.  It applies in particular to the exact wreath-product
untwisting of Thom's finite-order monomial phases.

But a sofic approximation of `K` needs opposite asymptotics:

* `z_q` represents the integer `1`, which is the identity in `K`, so its
  fixed-point density must tend to `1`;
* `c_q` represents `1/p^k + Z`, a nontrivial central element of `K`, so its
  fixed-point density must tend to `0`.

Thus **no exact/functorial permutationization of Thom's finite quotient models
can prove that `K` is sofic**.  Removing the phase necessarily requires losing
exact multiplicativity at the growing relation `c_q^q=1`.  This is stronger
and more specific than the general pointwise-rounding obstruction in
`Sofic/NoRounding.lean`: it rules out every exact permutation representation of
the whole finite quotient, not merely pointwise maps from the circle.

### Exact remaining construction problem

One must perform `q`-scale cycle surgery: replace the coprime-order cycles of
`c_q` by approximately `p^k`-torsion cycles so that

\[
  c^{p^k}\approx 1,\qquad d_{\rm Hamm}(c,1)\approx1,
\]

while preserving the multiplication table of the fixed `K`-window.  The long
relation `c^q=1` is not in a fixed window as `q -> infinity`, so the fixed-set
lemma does not itself obstruct such a deliberately inexact construction.
What has to be controlled is the central cocycle of the regular action: after
replacing its `Z/qZ`-valued phases by `Z/p^kZ`-valued shifts, the cocycle law
must fail on only `o(1)` of the base points.  This is the precise phase-surgery
problem; exact untwisting is now closed.

### Route audit

This is a rigorous obstruction/concentration result, not a solution of the
main problem.  It closes the sublane "convert Thom's projective/monomial
microstates without losing multiplicativity" and identifies the only escape:
controlled failure of the growing finite-order relation.

Subjective credence on `hyperlinear => sofic`: **47% true / 53% false**.
Audited progress on this phase-conversion lane: **about 70%** (the exact route
is closed; the inexact cycle-surgery problem remains).  Audited progress toward
the main open problem: **about 20%**.

### Quantitative strengthening: coordinatewise cycle surgery also fails

The obvious inexact escape replaces the `Z/qZ` phase coordinate pointwise by a
map

\[
  f:\mathbf Z/q\mathbf Z\longrightarrow \mathbf Z/p^k\mathbf Z,
\]

with `f(p^{-k}) != 0` but `f(1)=0`.  It cannot have vanishing Hamming defect.

Write `r=p^{-k} mod q`, and set

\[
\begin{aligned}
 \delta(f)&=\Pr_{x,y}[f(x+y)\ne f(x)+f(y)],\\
 \tau_r(f)&=\Pr_x[f(x+r)\ne f(x)+f(r)].
\end{aligned}
\]

**Lemma (uniform two-test obstruction, p-primary target).**  If `(p,q)=1`, the
target is `Z/p^kZ`, and `f(r) != 0`, then

\[
  \max\{\delta(f),\tau_r(f)\}\ge 2/9.
\]

Proof.  If `delta(f) >= 2/9` there is nothing to prove.  Otherwise the
Ben-Or--Coppersmith--Luby--Rubinfeld homomorphism-testing theorem gives a
homomorphism `h: Z/qZ -> Z/p^kZ` differing from `f` on a proportion `eta`,
where `eta` is the smaller root of

\[
  3\eta-6\eta^2=\delta(f).
\]

In particular `eta<0.212` (and `eta<delta(f)` in this range).  Coprimality makes
`h=0`.  On every `x` for which both `f(x)=0` and `f(x+r)=0`, the translation
test fails because `f(r) != 0`.  Hence

\[
  \tau_r(f)\ge1-2\eta>0.576>2/9.
\]

This proves the claim.  The cited homomorphism-testing statement is Theorem 1
of Ben-Or, Coppersmith, Luby and Rubinfeld, *Non-Abelian homomorphism testing,
and distributions close to their self-convolutions*, Random Structures &
Algorithms 32 (2008), 49--70.

There is a stronger form which removes the p-primary restriction and is the
correct statement for arbitrary coordinatewise permutationizations.  For a
map `f:Z/qZ -> B` into any finite abelian group, define also

\[
  \tau_1(f)=\Pr_x[f(x+1)\ne f(x)+f(1)].
\]

**Lemma (uniform three-test obstruction, arbitrary target).**  Suppose
`f(1)=0` and `f(r) != 0`.  Then

\[
  \max\{\delta(f),\tau_r(f),\tau_1(f)\}\ge2/9.
\]

Indeed, if all three quantities were below `2/9`, BOCLR would give a
homomorphism `h:Z/qZ -> B` differing from `f` on a set of density `eta`, with
`eta <= delta(f)/2 < 1/9`.  For `a=r,1`, the intersection of the two sets on
which `f(x)=h(x)` and `f(x+a)=h(x+a)` and the set on which the translation test
at `a` passes has density at least `1-2 eta-tau_a>0`.  Evaluating at one point
of that intersection gives

\[
  h(r)=f(r)\ne0,\qquad h(1)=f(1)=0.
\]

But `1=p^k r` in `Z/qZ`, while `q h(r)=0`; hence both `p^k h(r)=0` and
`q h(r)=0`.  Bezout and `(p,q)=1` force `h(r)=0`, a contradiction.

These two tests occur as **fixed multiplication relations inside Thom's actual
block group**, rather than as artificial tests on the cyclic centre.  In the
notation of the displayed definition of `K_0(R)` in section 3.1 of Thom:

* choose two `a_12` root elements supported in the first and second coordinates.
  On the regular `K_1(Z/qZ)` basis, their phase coordinates are the independent
  uniform entries `(a_24)_1` and `(a_24)_2`.  Multiplying the two elements tests
  `f(x+y)=f(x)+f(y)`, so its Hamming defect is exactly `delta(f)`;
* choose the `a_12` root element with coefficient `r` and the `a_24` root
  element with coefficient `1` in the matching coordinate.  Their product
  picks up the central term `r`; on a uniform basis vector the relation tests
  `f(x+r)=f(x)+f(r)`, so its Hamming defect is exactly `tau_r(f)`;
* make the same choice with coefficient `1` in the `a_12` root.  The product
  picks up the integer central term `1`, which is trivial in `K`; it tests
  `f(x+1)=f(x)+f(1)` with `f(1)=0`, giving `tau_1(f)`.

Thus a pointwise replacement of the finite cyclic phase has defect at least
`2/9` on one of three fixed relations whenever it separates the central element
`1/p^k + Z` and kills the integer centre.

The same obstruction survives arbitrary block weights.  Let `s` be the total
weight of blocks on which `f_l(r) != 0` and `f_l(1)=0`.  Then

\[
  D_{\rm add}+D_r+D_1\ge (2/9)s,
  \qquad
  \max(D_{\rm add},D_r,D_1)\ge (2/27)s.
\]

This is just weighted summation of the blockwise alternatives and then the
pigeonhole principle; it allows unequal block dimensions and different target
groups.  Sofic separation of `1/p^k+Z`, together with convergence of the
integer `1` to the identity, forces `s -> 1`.  Hence one of the three fixed
relations has asymptotic defect at least `2/27`.  For p-primary targets the
two-test version retains the sharper `1/9` global bound.  Allowing a different
pointwise rounding on every character block does not help.

**Exact scope.**  This closes both exact untwisting and every coordinatewise
cycle surgery `f_l` on Thom's published monomial microstates.  A successful
conversion must couple different base points or different character blocks;
equivalently it must be a genuinely nonlocal correction of the phase cocycle.
That surviving nonlocal problem is the same normalized-Hamming cohomological
quadrant encountered in the commutant-pinning and Frobenius audits.

### The surviving nonlocal problem as a finite cochain problem

Fix a finite presentation window with generator set `S`, and a congruence base
`Q_q=K_1(Z/qZ)`.  A fibered permutation model on

\[
  Q_q\times \mathbf Z/p^k\mathbf Z
\]

has the form

\[
  T_s(x,j)=(\bar s x,\;j+d_s(x)),\qquad s\in S,
\]

for functions `d_s:Q_q -> Z/p^kZ`.  Thus `d` is a `1`-cochain on the directed
Schreier graph.  If `w=s_1...s_t` is a relator/path, its fiber displacement is
the path sum

\[
  (\partial d)_w(x)=
  d_{s_t}(x)+d_{s_{t-1}}(\bar s_t x)+\cdots+
  d_{s_1}(\bar s_2\cdots\bar s_t x).
\]

The normalized Hamming defect of the relation is exactly the density of base
points on which this path sum differs from the prescribed central displacement.
A fiber-coordinate change `(x,j) -> (x,j+b(x))` changes `d` by the coboundary
of `b` and leaves every curvature/path-sum class unchanged.

Consequently the nonlocal phase-conversion question for Thom's congruence
microstates is equivalent to the following explicit finite problem.

> **Thom congruence cocycle problem.**  For the presentation `2`-complexes over
> `Q_q`, with `q` coprime to `p`, what is the normalized Hamming distance of the
> central extension datum (read modulo `p^k` on a fixed denominator window)
> from the space of `1`-coboundaries?  Is that distance bounded below uniformly,
> or can it tend to zero along `q -> infinity`?

Uniform positive distance rules out every fibered phase conversion through
Thom's congruence bases.  Distance tending to zero gives the desired nonlocal
phase correction and hence permutation microstates on that window.  Property
(T) only supplies expansion of the `1`-skeleton; this is a `2`-dimensional
cover/cosystolic-stability question.  The relevant general equivalence between
near-cover stability and cosystolic expansion is Dinur--Meshulam, *Near
Coverings and Cosystolic Expansion* (2019).  The arbitrary-finite-Abelian
coefficient expansion technology of Gohla--Thom and of
Oppenheim--Valentiner-Branth applies to their building/KMS complexes, not
automatically to these Abels/de Cornulier congruence presentation complexes.

This formulation does **not** classify all hypothetical sofic models of `K`;
it is the exact endpoint of the published-microstate conversion lane.  A proof
that every sofic model is asymptotically of this fibered congruence form would
be an additional rigidity theorem and is not currently available.

### Audit against arbitrary sofic approximations of K

Fix `c_k=1/p^k+Z`, of order `m=p^k`, in the centre of `K`.  Starting from an
arbitrary sofic approximation, finite-order surgery and finite-group
normalizer/centralizer perturbation can, on a fixed window and at `o(1)` cost,
put the model into the following weak wreath form on almost all points:

\[
  X_n\simeq Y_n\times \mathbf Z/m\mathbf Z,
  \qquad
  \sigma_n(g)(y,j)=(\bar\sigma_n(g)y,j+d_{g,n}(y)).
\]

This is the genuine consequence of centrality: the `c_k`-orbits can be made
exact and almost all have length `m`, and the other window permutations can be
made to commute with the fiber rotation.  It does **not** imply that the base
action is a congruence-regular action, nor that the arbitrary functions
`d_{g,n}` factor through Thom's standard central cocycle.

The model-rigidity statement needed to apply the `2/9` obstruction is:

> **Phase-factorization rigidity (required, presently open).**  Every sofic
> approximation of `K`, after `o(1)` Hamming modification and discarding
> `o(1)` of its points, decomposes into weighted blocks whose base actions are
> regular congruence actions of `K_1(Z/qZ)` and on which there is a single map
> `f_l:Z/qZ -> B_l` such that all window fiber displacements are
> `d_g(y)=f_l(s_g(y))`, where `s_g(y)` is Thom's standard central cocycle
> coordinate.

The `2/9` theorem would contradict this statement's conclusion for a sofic
model, and hence phase-factorization rigidity would prove that `K` is
nonsofic.  Current tools stop strictly before it:

* finite central order/normalizer surgery gives only the weak wreath form;
* the Alekseev--Thom centralizer theorem gives liftability of the relevant
  centralizer, not congruence regularity or pointwise cocycle factorization;
* property (T) controls almost invariant vectors / graph expansion, not the
  required two-dimensional phase factorization;
* character rigidity determines limiting traces, which are already the
  regular character in a sofic model, but does not classify the microstates;
* cosystolic expansion can control a specified family of congruence complexes
  after the model is known to lie in that family; it does not force an
  arbitrary sofic model into that family;
* P-stability or an ergodic-centralizer/LEF theorem strong enough to supply the
  missing classification is itself open here and would already be close to the
  desired nonsoficity conclusion.

There is also a decisive local calibration: the root/Heisenberg subgroup on
which the three tests live is amenable, hence sofic.  It therefore has
non-coordinatewise finite models satisfying all three fixed relations and
separating its central element.  Thus the three root relations alone cannot
rigidify an arbitrary model; any successful rigidity theorem must use the
global Kazhdan/block-group structure.

**Lane verdict.**  The `2/9` theorem is a sharp obstruction to Thom's published
monomial construction and to all coordinatewise phase surgeries of it.  No
presently available model-rigidity mechanism promotes it to arbitrary sofic
approximations.  This phase lane should be considered closed unless a new
global phase-factorization/P-stability theorem appears.

### Agent Two's exterior bridge: local-quantifier audit of the Shulman barrier

`Sofic/ExteriorMFProfile.lean` now proves, with kernel audit, that a pointwise
profile

\[
  \sqrt{d_n}\,\|\phi_n(gh)-\phi_n(g)\phi_n(h)\|_{op}\to0
\]

for every fixed pair, together with eventual pair-dependent operator-norm
separation, implies hyperlinearity.  The Shulman/Kazhdan obstruction above is
compatible with exactly these local quantifiers:

1. choose the one fixed Kazhdan set, the finitely many lamp-commutation pairs,
   and the finitely many multiplication pairs used to evaluate the fixed
   nontrivial free-lamp witness;
2. the maximum of the finitely many pairwise errors, multiplied by
   `sqrt(d_n)`, still tends to zero;
3. eventual separation for the single pair `(w,1)` supplies a fixed
   `alpha_w>0` after one index;
4. the property-(T) pinning estimate on this finite window then gives
   `alpha_w <= C sqrt(d_n) epsilon_n`, contradicting the profile whenever the
   ambient `G` sector is genuine, and gives the stated Frobenius-instability
   alternative when it is only close to a genuine representation.

No globally uniform error sequence over `G` is used.  Therefore the exact
finite-quotient and locally Frobenius-stable subclasses are genuinely excluded
under Agent Two's theorem.  What remains possible is a pointwise square-root
profile with an ambient `G` restriction that is uniformly far, on that fixed
window in unnormalized Frobenius norm, from every genuine representation.  The
published Shulman proof supplies no rate, but this remains a nonexistence of an
extractable rate, not a proof that such exotic pointwise profiles do not exist.

### Halo-product permanence does not decide the Kun--Thom wreath group

A primary-source audit of Alekseev--Bradford, arXiv:2601.18742, fixes the
logical direction.  Definition 4.23 introduces a *sofic C-action* by means of
finite permutation models and injective partial-homomorphism charts.  Their
Proposition 4.26 pushes an ordinary sofic action on the coordinate set forward
to such an automorphic action on a halo, and Theorem 5.1 / Corollary 5.2 then
pushes that chart system forward to a metric approximation of the semidirect
product.  None of these statements has a converse.

For the lamp halo `Delta = directSum_(G/Gamma) C_2`, the converse at the chart
level is in fact impossible for the Kun--Thom pair: the coordinate reverse
transfer recorded above pulls any Definition-4.23 chart system back along
`x |-> delta_x(1)`.  Hence a sofic hyperlinear-action chart would force the
nonsofic coset action `G curvearrowright G/Gamma` to be sofic.  Thus the 2026
halo theorem supplies neither a hidden construction nor a hidden obstruction
to hyperlinearity of the wreath group.

The exact remaining object is

`M_KT = L^infty({-1,1}^{G/Gamma}) rtimes G
      = L((directSum_(G/Gamma) C_2) rtimes G)`.

The Kun--Thom group is hyperlinear iff `M_KT` is Connes embeddable.  Theorem
3.8 of Gao--Kunnawalkam Elayavalli--Patchell and Corollary 5.5 of
Alekseev--Bradford prove this embeddability under the additional hypothesis
that the coordinate action is sofic; Kun--Thom proves that hypothesis false.
Accordingly a successful model must embed the Bernoulli algebra *non-Cartanly*:
it cannot arise from orbit charts, finite quotient coordinates, or any
Definition-4.23 automorphic charts.  This is the direct tracial-microstate
quadrant left open by `CoordinateTransfer.lean`, not another action-permanence
problem.

### Abstract versus Cartan-preserving embeddings: the exact lifting gap

There are three distinct assertions for the Kun--Thom Bernoulli Cartan pair
`A_KT subset M_KT`:

1. an abstract trace-preserving embedding `M_KT -> product_omega M_(d_n)`;
2. an embedding with `A_KT` in the diagonal ultraproduct and the canonical
   group normalizers in the permutation ultraproduct;
3. a theorem converting every embedding of type 1 into one of type 2.

Păunescu, arXiv:1002.0605, Definition 1.4 defines a sofic action by the
existence of an embedding of type 2.  Proposition 1.14 gives the corresponding
Cartan-pair characterization.  Neither statement asserts 3.

The first apparent lifting issue is harmless.

**Lemma (abelian diagonalization in a matrix ultraproduct).**  Let `A` be a
separable abelian finite von Neumann algebra and let
`Theta:A -> product_omega M_(d_n)` be trace preserving.  There is a unitary
`v` in the ultraproduct such that `v Theta(A) v*` is contained in
`product_omega D_(d_n)`.

**Proof.**  A separable abelian von Neumann algebra has a self-adjoint
generator `a`.  Represent the self-adjoint `Theta(a)` by uniformly bounded
self-adjoint matrices `a_n`, diagonalize each `a_n` by a unitary `v_n`, and
put `v=(v_n)_omega`.  Trace preservation makes `Theta` normal, so
`Theta(A)=W*(Theta(a))`; the conjugated algebra is therefore contained in the
diagonal ultraproduct.  End proof.

The normalizer lifting is the real obstruction, and it already fails
quantitatively for a separable diagonal algebra.  Put `d_n=b_n m_n`, let
`B_n subset D_(d_n)` be the algebra of diagonal matrices constant on each of
`b_n` consecutive blocks of size `m_n`, and let

`U_n = directSum_(j=1)^(b_n) F_(m_n)`,

where `F_m` is the normalized Fourier matrix.  Then `U_n` centralizes `B_n`
pointwise.  But for every monomial unitary `W_n`,

`|tr(U_n* W_n)| <= 1/sqrt(m_n)`

because a monomial selects one entry in each row and every nonzero Fourier
entry has modulus `1/sqrt(m_n)`.  Consequently

`||U_n-W_n||_2^2 >= 2-2/sqrt(m_n)`.

Thus, as `m_n -> infinity`, the normalizing unitary is asymptotically
`sqrt(2)` away from every monomial (hence every permutation) even though the
abelian algebra is exactly diagonal.  The same example may be made diffuse
in the ultraproduct by taking `b_n -> infinity`.

Accordingly the precise missing theorem is:

> **Invariant Cartan completion for the KT pair (open).**  Given an abstract
> embedding `Theta:M_KT -> product_omega M_(d_n)`, after diagonalizing
> `Theta(A_KT)`, there is a diagonal Cartan ultraproduct `D` containing
> `Theta(A_KT)` which is normalized by all `Theta(u_g)`, `g in G`.

If this held, the normalizers of `D` could be represented by monomials; the
diagonal phases can be removed by the standard trace-amplification device,
producing a Păunescu-sofic embedding and contradicting Kun--Thom Corollary D.
Hence it would prove `M_KT` non-Connes-embeddable.  No cited result proves this
completion.  Kun--Thom starts with permutation normalizers and proves a
normalization theorem *inside that permutation ultraproduct*; it does not
upgrade arbitrary unitary normalizers.  The Fourier-block calculation shows
why the upgrade cannot follow from abelianness or finite-dimensional
simultaneous diagonalization alone: all possible exoticity is stored in the
growing multiplicity fibers.

### MF Mautner decomposition for an infranormal free lamp

There is an operator-norm analogue of the localization above which is exact
and does not require choosing traces.  Let `Gamma < G` be a Kazhdan
infranormal pair, let

`H_K = G *_Gamma (Gamma x K)`,

and let `rho:H_K -> U(A)` be a homomorphism into a unital finite C*-algebra
`A`.  Here *finite* means that every isometry in every matrix algebra over
`A` is unitary.  This applies in particular to a norm matrix ultraproduct
`product M_(d_n) / directSum M_(d_n)`: if bounded lifts `X_n,Y_n` satisfy
`X_n Y_n -> 1` in operator norm, then `X_n` is eventually invertible with
uniformly bounded inverse, and hence `Y_n X_n -> 1`; the same argument works
in every matrix amplification.

Let `p_Gamma in C*_max(Gamma)` be the Kazhdan projection and write
`p=rho(p_Gamma)`, `q=1-p`.  (The inclusion of a subgroup induces an injective
map on full group C*-algebras, for example by induced representations.)

**Theorem (MF Mautner decomposition).**  The projection `q` commutes with
`rho(H_K)`.  Moreover, for every free-lamp witness

`w=[t k t^-1,gamma]`

with `t^-1 gamma t` outside `Gamma`, one has `p(rho(w)-1)=0`.  Consequently,
if `rho` is injective, then

`q(rho(w)-1) != 0`.

**Proof.**  Fix a compressor `t`, so `t Gamma t^-1 <= Gamma`, and put
`U=rho(t)`.  In every unitary representation, `U^-1` maps the
`Gamma`-fixed subspace into itself: if `xi` is fixed and `gamma in Gamma`,
then

`rho(gamma) U^-1 xi = U^-1 rho(t gamma t^-1) xi = U^-1 xi`.

By the defining universal property of the Kazhdan projection this gives
`U q U* <= q`.  The two projections `U q U*` and `q` are Murray--von Neumann
equivalent.  Finiteness of `A` therefore upgrades the inclusion to equality,
so `UqU*=q`.  The compressors generate `G`; hence `q` commutes with `rho(G)`.
Every `k in K` centralizes `Gamma`, so `rho(k)` commutes with the spectral
projection `p`, and therefore with `q`.  These elements generate `H_K`,
proving centrality.

On the `p`-corner every element of `Gamma` acts as the identity.  Since `p`
is now also `G`-invariant, the displayed commutator `w` acts trivially on
that corner.  Thus `p(rho(w)-1)=0`.  If `rho` is injective, Bass--Serre normal
form gives `rho(w) != 1`, so its entire nonzero operator-norm deviation lies
in the `q`-corner.  End proof.

Applying this to Shulman's weak-MF embedding of `H_K` produces a canonical
operator-norm exotic corner with all three properties forced by the prior
heuristics: it has no `Gamma`-fixed vectors, it is invariant under the whole
ambient group, and it detects the nonsofic witness in operator norm.  Thus
the exotic sector is not merely a possible shape of Shulman's construction;
it must actually occur.

This does **not** finish hyperlinearity.  If `q_n` are finite-stage lifts and
`r_n=rank(q_n)`, the nonzero norm of
`q_n(rho_n(w)-1)q_n` may be supported on `o(r_n)` dimensions.  Normalizing the
corner traces can therefore kill `w`.  Property `(T)` guarantees positive
normalized-HS mass for at least one fixed generator of `Gamma`, but it does
not transfer that mass to the free-lamp witness.  The remaining quantitative
statement is exactly one of the following equivalent construction targets:

* make the witness occupy positive rank inside this forced exotic corner;
* give the corner maps Agent Two's pointwise square-root operator-norm
  profile;
* prove a character/normal-subgroup theorem forcing any tracial kernel that
  is nontrivial on `Gamma` to retain a Kun--Thom witness.

The first two are model-production questions.  The third is the only visible
rigidity route around rank blindness; it is not supplied merely by the known
classification of characters of elementary groups, because finite-congruence
representations with their trivial summand removed have no invariant vectors
and can still absorb the compression.

### Invariant ideals in the Laurent ambient are finite-codimensional

The ideal side of the preceding character fork can nevertheless be made
exact.  Put

`R = F_q[x_1^(+-1),...,x_d^(+-1)]`, `d>=2`,

with the monomial action of `SL_d(Z)`.

**Theorem.**  Every nonzero `SL_d(Z)`-invariant ideal `I` of `R` has finite
codimension over `F_q`.

**Proof.**  Base-change to the algebraic closure `k` of `F_q`, and let `P` be
a minimal prime over `I R_k`.  The group permutes the finitely many minimal
primes, so a finite-index subgroup `Lambda<SL_d(Z)` stabilizes `P`.  There is
an integer `N>=1` such that every elementary shear `E_ij(N)` belongs to
`Lambda`.  Write `z_i` for the image of `x_i` in the fraction field of the
domain `R_k/P`.

Suppose some `z_j` has infinite multiplicative order.  For `i!=j`, write any
`f in P` as

`f=sum_m a_m x_i^m`

with the coefficients independent of `x_i`.  Applying the powers
`E_ij(Nn)`, `n=0,...,M-1`, and reducing modulo `P` gives

`sum_m (a_m z_i^m) (z_j^(Nm))^n = 0`.

The numbers `z_j^(Nm)` are pairwise distinct.  The Vandermonde matrix is
therefore invertible over the fraction field, so every coefficient `a_m`
already lies in `P`.  Doing this for every `i!=j` shows that `P` is the
extension of `P intersect k[x_j^(+-1)]`: after successively taking homogeneous
components in the other variables, each remaining Laurent monomial is a
unit times a coefficient in the one-variable ring.  If this intersection is
nonzero, primeness makes it `(x_j-a)` for some `a in k*`; but every element of
the algebraic closure of a finite field has finite multiplicative order,
contrary to the choice of `z_j`.  Hence the intersection is zero and `P=0`.
This is impossible because `P` contains the nonzero ideal `I R_k`.

Thus every `z_j` has finite order.  Some relations
`x_j^(m_j)-1 in P` hold for all `j`, so `R_k/P` is finite-dimensional.
Therefore every minimal prime over `I R_k` is maximal and the radical of
`I R_k` has finite codimension.  Noetherianity gives
`rad(I R_k)^a <= I R_k` for some `a`, hence `I R_k`, and then `I`, has finite
codimension.  End proof.

**Consequence for KT tracial kernels.**  Let
`N=EL_r(R) normal G` be the Laurent elementary subgroup.  By the standard
normal-subgroup/sandwich theorem, the level ideal of `ker(eta) intersect N`
for any homomorphism `eta:G->U(M)` is `SL_d(Z)`-invariant.  Apart from the
possible level-zero central kernel, there are only two cases:

1. level zero, so the representation is faithful on every Laurent root
   subgroup;
2. nonzero level, so it factors on all root subgroups through a finite ring
   quotient of `R`.

This removes the possibility of an infinite-codimensional intermediate
congruence kernel.  It still does not force the free-lamp witness to be
trace-visible: a tracial model may be faithful on the ambient Laurent roots
while killing the lamp commutator, or may use a finite-congruence component
with its invariant summand removed.  The exact remaining issue is therefore
not ideal classification but whether positive trace on the MF exotic corner
can be forced onto the lamp ideal.

### A single trace-visible lamp witness is enough

The preceding target can be weakened substantially.  It is unnecessary to
make the whole Shulman free-lamp group hyperlinear.

Let `K` be any nontrivial hyperlinear group (one may take `C_2`), let

`H_K = G *_Gamma (Gamma x K)`,

and choose a Kun--Thom witness `w=[t k t^-1,gamma] != 1`.  Suppose there is
**one** homomorphism `eta_1:H_K -> U(M)` into a Connes-embeddable finite
tracial von Neumann algebra such that `eta_1(w) != 1`.  No faithfulness
assumption on `eta_1` is needed.

**Theorem (single-trace criterion).**  Under the Kun--Thom hypotheses on
`Gamma<G`, the existence of `eta_1` implies that a hyperlinear nonsofic group
exists.

**Proof.**  The two factor maps

`G -> G x K,       g |-> (g,1)`,

`Gamma x K -> G x K,  (gamma,k) |-> (gamma,k)`

agree on `Gamma`, and hence induce a homomorphism
`eta_0:H_K -> G x K`.  Its restrictions to both `G` and the distinguished
copy of `K` are injective.  Since `G` is residually finite and `K` is
hyperlinear, `G x K` is hyperlinear.

Let `Q` be the image of the diagonal homomorphism

`eta_0 x eta_1 : H_K -> (G x K) x U(M)`.

Then `Q` is hyperlinear, the visible copy of `G` embeds in `Q`, and the image
of `w` is nontrivial because its second coordinate is `eta_1(w) != 1`.
Assume that `Q` were sofic and take a sofic representation of it.  Its
restriction to the embedded `G` is a sofic representation.  The image of `k`
centralizes the image of `Gamma`; Kun--Thom Theorem 4.1 says that this
centralizer is normalized by the image of `G`.  Hence the image of
`t k t^-1` commutes with the image of `gamma`, forcing the nontrivial element
`w in Q` to map to the identity.  This contradicts injectivity of the sofic
representation.  Thus `Q` is hyperlinear and nonsofic.  End proof.

Apply this to the MF Mautner decomposition.  Write `A_q=qAq` and
`a=q(rho(w)-1)`, which is nonzero in operator norm.  The full open certificate
is now exactly

> find a Connes-embeddable (hyperlinear) tracial state `tau` on `A_q` with
> `tau(a* a)>0`.

Indeed its GNS representation is the required `eta_1`.  Equivalently, `a`
must lie outside the **hyperlinear tracial radical**
`intersection_(tau in T_hyp(A_q)) ker(pi_tau)`.  The restriction to
hyperlinear traces is essential: an MF C*-algebra need not have every trace
Connes-embeddable.  This formulation precisely
identifies rank blindness: a matrix-norm ultraproduct may contain a nonzero
compact-like ideal annihilated by every normalized matrix trace (the
unitization of the compact operators is the calibration), so MF and
stably-finite alone do not supply the desired trace.  But no canonical-trace
or full-faithfulness construction is required; positive trace on this single
lamp ideal already ends the main problem.

### Correct corner visibility criterion: one witness and Cesaro tensors

The first proposed tensor argument for the exotic corner needs two repairs.
If a fraction `delta` of the spectrum of a unitary is `c`-far from `1`, the
near-`1` subspace of its tensor power need not have fraction
`(1-delta)^M`: eigenphases from different tensor factors can cancel.  Also,
the absence of `Gamma`-fixed vectors does not prevent the witness from being
nontrivial in operator norm on `o(r_n)` dimensions and invisible in normalized
HS.  The absorption-one basin therefore remains available in trace even on
the MF Mautner corner.

There is, however, a cancellation-proof replacement which also weakens the
hypothesis to a single witness.  Let

`phi_n:H_K -> U(r_n)`

be unital maps on exhausting windows, with maximum operator-norm
multiplicative defect `epsilon_n` on the `n`th window.  Fix the one Kun--Thom
witness `w`, put `U_n=phi_n(w)`, fix `c>0`, and let

`delta_n = tr_(r_n)(1_[c,infinity)(|U_n-1|))`.

**Theorem (one-witness rank/defect criterion).**  If

`epsilon_n/delta_n -> 0`

and `delta_n>0` eventually, then there is a homomorphism from `H_K` into a
tracial matrix ultraproduct whose value on `w` is nontrivial.  Consequently,
by the single-trace criterion, a hyperlinear nonsofic group exists.

**Proof.**  Choose integers `L_n -> infinity` so slowly that

`L_n epsilon_n -> 0`, `L_n delta_n -> infinity`.

For `1<=j<=L_n`, use the tensor-power map

`phi_n(h)^(tensor j) tensor 1_(r_n^(L_n-j))`

on a block of dimension `r_n^L_n`, and take the direct sum of these `L_n`
equal-sized blocks.  The `j`th block has operator-norm multiplicative defect
at most `j epsilon_n`; hence the normalized-HS defect of the direct sum is at
most `L_n epsilon_n -> 0`.

Write `a_n=tr_(r_n)(U_n)`.  Since

`1-Re(lambda)=|lambda-1|^2/2`

on the unit circle,

`Re(a_n) <= 1-(c^2/2)delta_n`,

and therefore `|1-a_n| >= (c^2/2)delta_n`.  The normalized trace of the new
model at `w` is the Cesaro geometric sum

`(1/L_n) sum_(j=1)^L_n a_n^j`.

For `|a_n|<=1` its modulus is at most

`2/(L_n |1-a_n|) <= 4/(c^2 L_n delta_n) -> 0`.

Thus the maps define a homomorphism into a tracial matrix ultraproduct and
send `w` to a unitary of trace zero, in particular not to `1`.  The
single-trace criterion finishes.  End proof.

This is the exact quantitative summit on the Shulman/Mautner lane:

`deviation rank fraction of one witness >> operator-norm defect`.

No minimum over all nontrivial window elements is needed, no faithfulness of
the corner representation is needed, and no assertion about tensor spectral
supports is used.  Conversely, Theorem C's operator-norm separation alone
only says `delta_n>=1/r_n`; it gives no comparison with `epsilon_n`.

The proposed normal-subgroup escape can also be closed more simply and more
rigorously than by claiming full connectivity of the lamp-identification
graph.  The retraction `H_K -> G` kills every lamp and hence kills `w`, while
the left regular representation of the residually finite group `G` is
Connes-embeddable, faithful on `Gamma`, and has no nonzero `Gamma`-fixed
vectors.  Therefore no theorem whose only input is "the tracial
representation is nontrivial/fixed-vector-free on Gamma" can force `w` to
survive.  Stronger claims about the entire normal closure of `w` require the
orbit-graph connectivity calculation and are not needed for this no-go.

Shulman's published double construction still does not provide the new
one-witness modulus automatically.  At outer stage `k` its asymptotic lift
has a uniform operator-norm defect tending to zero and converges strongly to
a chosen faithful representation, but strong convergence controls each fixed
finite-dimensional subspace rather than its density in the selected matrix
coordinate.  Adding arbitrarily large exact-trivial blocks (or delaying the
active block to an arbitrarily late coordinate) preserves the strong limit
and every qualitative norm estimate while replacing `delta_n(w)` by an
arbitrarily small rank fraction.  Thus the paper proves that the exotic
corner and an operator-norm-visible witness exist, but not
`epsilon_n=o(delta_n(w))`.  Unlike the older square-root profile, this is now
a one-element quantitative extraction problem; it is nonetheless genuinely
new input rather than a reindexing of Theorem 10.

### Ergodic-centralizer audit: the Thom-K shortcut remains conjectural

Hayes--Kunnawalkam Elayavalli, *On sofic approximations of non amenable
groups* (Math. Z. 307 (2024), Article 38), states the exact missing assertion
as Conjecture 1: every sofic group admits a sofic embedding whose centralizer
acts ergodically on the Loeb space.  Their Lemma 5, citing Paunescu Theorem
2.13, proves the assertion for initially subamenable (LEA) groups.  It does
not prove it for arbitrary sofic groups.

Alekseev--Thom, arXiv:2608.05362, proves that a Kazhdan group admitting such
an ergodic-centralizer embedding is LEF, and hence that a finitely presented
Kazhdan group admitting one is residually finite.  Consequently Thom's
finitely presented Kazhdan hyperlinear non-RF group `K` cannot simply be put
in the known LEA case: if it were LEA, the preceding theorem would force it
to be RF.  Thus

`HKE Conjecture 1 + K sofic  =>  K RF`,

and HKE would indeed prove that `K` is nonsofic, but this is a conditional
route rather than a completed existence theorem.

Munteanu--Paunescu, *On the Krein--Milman theorem for the space of sofic
representations* (Groups Geom. Dyn. 20 (2026), 381--401), does not remove the
condition.  It proves that minimal faces are extreme and constructs extreme
points for free groups, but it also constructs a decreasing chain of closed
faces with empty intersection and explicitly presents a free-group sofic
representation believed to lie outside the closed convex hull of the extreme
points.  Therefore neither a Zorn argument nor an ordinary Krein--Milman
argument supplies an extreme/ergodic-centralizer embedding for an arbitrary
sofic group, in particular not for `K`.

### Fullness forces trace visibility, but the symmetric double has a fold

The one-witness rank/defect condition has a purely ideal-theoretic sufficient
condition that needs no dimension estimate.

Let `phi_n:H->U(d_n)` be operator-norm almost-representations on exhausting
windows, let `U_n=phi_n(w)`, and suppose there are a fixed integer `N` and
uniformly bounded matrix words `X_(i,n),Y_(i,n)` such that

`||1-sum_(i=1)^N X_(i,n)(U_n-1)Y_(i,n)||_op -> 0`.

**Lemma (uniform algebraic visibility).**  The normalized Hilbert--Schmidt
norms `||U_n-1||_2` are bounded away from zero.  Hence the normalized matrix
traces give a hyperlinear trace detecting `w`, and in the Kun--Thom setting a
hyperlinear nonsofic group exists.

**Proof.**  Put

`C=sum_i sup_n ||X_(i,n)|| ||Y_(i,n)|| < infinity`.

The normalized Hilbert--Schmidt norm is an operator ideal norm, so

`1-o(1) <= ||sum_i X_(i,n)(U_n-1)Y_(i,n)||_2`
`         <= C ||U_n-1||_2`.

Thus `liminf ||U_n-1||_2 >= 1/C`.  Operator-norm multiplicativity implies
normalized-HS multiplicativity, so the tracial ultraproduct homomorphism
sends `w` to something other than `1`.  The single-trace criterion then
finishes.  End proof.

In C*-language, if `A_q` is the unital MF Mautner corner and
`a=q(rho(w)-1)`, the hypothesis holds whenever `a` is **full** in `A_q`:
approximate the unit in norm by a finite sum `sum x_i a y_i` and lift the
finitely many coefficients.  Therefore

> fullness of the lamp deviation in one MF Mautner corner implies that a
> hyperlinear nonsofic group exists.

This does not follow from Shulman's theorem.  The primary statement is that
for every separable MF C*-algebra `A` and every subalgebra `C`, the symmetric
amalgam `A *_C A` is MF (Theorem 10 of arXiv:2603.13564).  It does not say
that the reduced C*-algebra of the Kun--Thom free-lamp group is MF.  Moreover
every symmetric amalgam has the fold homomorphism

`A *_C A -> A`

identifying the two copies.  In the free-lamp realization that fold kills the
copy-difference/lamp witness.  Whenever the fold representation has a
nonzero `q`-part, it gives a proper quotient of the Mautner corner killing
`a`, so `a` is not full there.  This is the ideal-theoretic form of rank
blindness: the nonsofic mechanism lies in the fold kernel, and Shulman's MF
theorem supplies no tracial mass to that kernel.

The exact new fork is consequently:

1. find an MF model/quotient of the double in which the image of `a` is full;
2. or construct a hyperlinear trace on the fold kernel which is nonzero on
   `a`;
3. or establish the weaker coordinate inequality
   `epsilon_n=o(delta_n(w))` directly.

The first alternative is stronger than necessary but dimension-free.  The
canonical symmetric-double model does not satisfy it automatically.

### The fold-kernel trace is exactly the nonamenable-amalgam problem

The group-theoretic symmetric double used around the free-lamp subgroup can
be written

`D=(G x K) *_Gamma (G x K)`,

where `Gamma` is embedded as `Gamma x {1}` in both factors.  The subgroup
generated by `G x {1}` in the first factor and `Gamma x K` in the second is

`H_K=G *_Gamma (Gamma x K)`.

The fold `D->G x K` restricts to the earlier retraction-type map `eta_0` and
kills the Kun--Thom commutator.  On the other hand, the canonical reduced
amalgamated-free-product trace on

`L(G x K) *_(L Gamma) L(G x K)`

detects every nontrivial reduced group word, hence detects the witness `w`.
Its restriction to `H_K` is just the canonical group trace.  Consequently,
if this one reduced amalgamated free product is Connes-embeddable, then
`H_K` is hyperlinear; Kun--Thom nonsoficity would solve the main problem.

This observation does not follow from Shulman's norm-MF theorem.  It asks
for trace-preserving microstates for the reduced amalgamated product, whereas
Theorem 10 constructs an embedding of the **full** symmetric C*-amalgam into
a norm matrix ultraproduct.  The normalized coordinate traces of that
embedding may factor through the fold and annihilate its kernel.

Equivalently, using the free-lamp normal form,

`H_K=(ast_(G/Gamma) K) semidirect G`,

the desired canonical trace is the trace of the free generalized wreath
product, or of the associated free-Bogoljubov crossed product for the
quasi-regular orthogonal representation on `ell^2(G/Gamma)`.  Theorem 3.9 of
Duncan--Kazachkov--Kunnawalkam Elayavalli, *Soficity for group actions on
sets and applications* (Research in the Mathematical Sciences, 2025), gives
Connes embeddability for such free generalized wreath products when the
action `G on G/Gamma` is sofic.  That hypothesis is not available here: the
Kun--Thom centralizer obstruction (and the reverse-transfer theorem already
audited in this ledger) rules out exactly the relevant action-model route.

Thus the fold-kernel branch terminates at the following precise relative
embedding statement:

> Is `L(G x K) *_(L Gamma) L(G x K)` Connes-embeddable for the Kun--Thom
> compression pair `Gamma<G`?

This is equivalent in strength, for the present construction, to producing
the trace-visible lamp witness.  Neither full-C*-MF permanence nor ordinary
hyperlinearity of `G`, `Gamma`, and `K` proves it.  A proof must manufacture
relative microstates which distinguish the profinitely invisible cosets.

### Gaussian one-lamp criterion

There is an abelian version of the relative target which needs neither the
whole free-lamp algebra nor amalgamated freeness.  Let

`pi:G -> O(ell^2(G/Gamma,R))`

be the quasi-regular orthogonal representation and let
`G on (X_pi,mu_pi)` be its Gaussian p.m.p. action.  Write `A_pi` for the
Gaussian abelian von Neumann algebra, with Gaussian Weyl unitaries `v(xi)`.
The vector `delta_Gamma` is fixed by `Gamma`, so

`v=sign(X_(delta_Gamma)) in A_pi^Gamma`.

Then `v^2=1`, `v` is nonconstant, and `v` commutes with the canonical copy
of `Gamma` in the crossed product `A_pi crossed G`.

**Theorem (Gaussian one-lamp criterion).**  If the tracial crossed product

`A_pi crossed G`

is Connes-embeddable, then there exists a hyperlinear nonsofic group.

**Proof.**  The Gaussian coordinates belonging to the orthonormal basis
`{delta_(g Gamma)}` are independent real Gaussians.  Their signs are
independent Rademacher variables.  Consequently the conjugates

`v_(g Gamma)=u_g v u_g^*`

generate a faithful copy of `direct-sum_(G/Gamma) C_2`, and `G` permutes
these generators by its coset action.  The subgroup `Q` generated by `G` and
`v` is therefore exactly

`(direct-sum_(G/Gamma) C_2) semidirect G`,

the group in Kun--Thom Theorem A.  It is nonsofic.  If the ambient crossed
product is Connes-embeddable, its countable subgroup `Q` is hyperlinear.
Thus `Q` itself is a hyperlinear nonsofic group.  End proof.

This criterion is strictly cheaper in algebraic structure than embedding the
free generalized wreath product: its lamp orbit is abelian and Gaussian.
Indeed the Gaussian action here is the generalized Bernoulli action with
Gaussian base over `G/Gamma`, and its sign factor is the two-point
generalized Bernoulli action whose group-measure-space algebra contains
`L(Q)`.  Analytically the criterion asks whether this nonsofic p.m.p. action
nevertheless has an **abstractly** Connes-embeddable crossed product.  A
diagonal-preserving embedding is impossible by Kun--Thom Corollary D, but
abstract Connes embeddability does not require the Cartan algebra to become
diagonal.

Ben Hayes, *Sofic Entropy of Gaussian Actions* (arXiv:1509.07835), does not
settle this.  His Theorem 1.1 decomposes an orthogonal representation into a
part absolutely continuous with respect to the regular representation and a
singular part, and explicitly leaves open the possibility that the Gaussian
action of the singular part has sofic entropy `-infinity` (no microstates).
For `pi=ell^2(G/Gamma)`, the standard implication

`pi weakly contained in lambda_G  iff  Gamma amenable`

does not apply favorably because the Kun--Thom `Gamma` is nonamenable.
Finite-quotient covariance models also converge to the indicator of the
relative profinite closure `Gamma*`, not to the desired coefficient
`1_Gamma`.  Thus the same invisible-coset obstruction reappears as positivity
of finite covariance kernels.

The new terminal question is explicit:

> Does the Gaussian action associated with `ell^2(G/Gamma)` admit sofic, or
> at least Connes-embeddable crossed-product, microstates for the Kun--Thom
> compression pair?

A positive answer alone disproves the universal hyperlinear-to-sofic claim.

### Audit of the proposed CIII hexagon: one vector is not enough

The Bogoljubov reformulation

`L(H_free)=Gamma(ell^2_R(G/Gamma))'' crossed_Bog G`

is correct.  The proposed six-way equivalence is not.  Three failures are
load-bearing.

1. `W'` and `Ad(u_h)(W')` both contain the scalar identity, so they can never
   be Hilbert--Schmidt orthogonal as stated.  One must first center them:
   `W'_0=W' minus C1`, and one must specify normalization by their dimensions.
2. A single rank-one `Gamma`-fixed projection in `W'` whose translate has
   small overlap controls one vector in `W'_0`; it does not imply that an
   orthonormal basis of the whole commutant has small translated overlaps.
   Thus the claimed `(5)=>(6)` propagation is invalid.
3. Most importantly, one vector in dimension `d_n` has normalized rank
   `1/d_n`.  The reflection `1-2p_xi` is then `2/sqrt(d_n)`-close to the
   identity in normalized HS norm.  Padding or taking more identical copies
   does not change this fraction, and tensoring makes it smaller.  Hence the
   vector lamp can disappear in the tracial ultraproduct unless its rank is
   compared quantitatively with the multiplicativity defect.  This is exactly
   the rank-blindness obstruction, not an escape from it.

There is a clean corrected version.  First strengthen the earlier
one-witness lemma to its natural trace-gap form.

**Lemma (trace-gap/defect criterion).**  Let `phi_n:H->U(d_n)` be
normalized-HS almost-representations on exhausting windows with defect
`epsilon_n` (operator-norm control is more than enough), fix `w in H`, and put

`kappa_n=1-Re tr(phi_n(w))`.

If `kappa_n>0` and `epsilon_n/kappa_n->0`, then there is a homomorphism from
`H` to a tracial matrix ultraproduct in which `w` is nontrivial.

**Proof.**  Choose `L_n->infinity` with
`L_n epsilon_n->0` and `L_n kappa_n->infinity`.  As in the earlier proof,
take the equal-sized direct sum of the tensor powers `phi_n^(tensor j)`,
`1<=j<=L_n`.  Its defect is at most `L_n epsilon_n`.  If
`a_n=tr(phi_n(w))`, then `|1-a_n|>=1-Re(a_n)=kappa_n`, and its new trace at
`w` has modulus

`|(1/L_n) sum_(j=1)^L_n a_n^j| <= 2/(L_n kappa_n) -> 0`.

End proof.  The spectral rank criterion implies this one by
`kappa_n>=(c^2/2)delta_n`, but the trace-gap version is strictly more direct.

**Correct projection-profile face.**  Suppose a hyperlinear/MF model `u_n`
of `G` contains projections `p_n` of normalized ranks `rho_n`, satisfying on
the relevant window

`||[p_n,u_n(gamma)]||_2=o(rho_n)` for `gamma in Gamma`,

and for the two distinct cosets in the Kun--Thom witness,

`tr(p_(t,n) p_(gamma t,n))=o(rho_n)`,

where `p_(g,n)=u_n(g)p_nu_n(g)^*`.  If the total relation defect
`epsilon_n` also satisfies `epsilon_n=o(rho_n)`, then the main problem has a
negative answer.

Indeed put `v_n=1-2p_n`.  It is an exact involution and almost commutes with
the `Gamma`-window.  The witness image is, up to the stated relation error,
`v_(t,n)v_(gamma t,n)`.  Since

`Re tr(v_p v_q)=1-2tr(p)-2tr(q)+4tr(pq)`,

its trace gap is

`kappa_n=4(rho_n-tr(p_(t,n)p_(gamma t,n)))+o(rho_n)`
`       =(4+o(1))rho_n`.

The trace-gap/defect criterion and the single-trace Kun--Thom construction
finish.  A single vector is the special case `rho_n=1/d_n`; it is useful only
if the much stronger rate `epsilon_n=o(1/d_n)` is also proved.  The corrected
minimal face is therefore a **positive-profile almost-invariant subspace**,
not one vector.

For the commutant-Gaussian construction, the corresponding valid hypothesis
must likewise concern the centered commutant covariance operator (or a
positive-dimensional subspace of it), not one basis vector.  Wick expansion
can then prove freeness once all centered translated overlaps vanish with a
dimension-uniform normalization; it does not supply that hypothesis.

### Exact Bogoljubov implementers versus the free trace

Known permanence does not cover the Kun--Thom coset action.  Gao--Kunnawalkam
Elayavalli--Patchell prove Connes embeddability of generalized and free
generalized wreath products when the underlying action on the index set is
sofic.  Kun--Thom Theorem A and Corollary D prove that the relevant action
`G on G/Gamma` and its nontrivial generalized Bernoulli actions are not
sofic.  Capraro--Paunescu cover profinite actions, which again identify the
invisible cosets.  Results on unrestricted wreath products cover the opposite
extension direction: the acting/quotient group must be amenable.  Here the
lamp kernel is amenable but the quotient `G` is Kazhdan and nonamenable.

The most natural direct free-Gaussian construction has a rigorous trace
obstruction.  Let `H_R` have dimension `m>=3`, let

`F_N=direct-sum_(k=0)^N H_C^(tensor k)`,

and let `l_i^(N)` be the compressed left creation operators.  Orthogonal
transformations of `H_R` are implemented **exactly** on every `F_N` by
second quantization.  Put

`S_N=sum_(i=1)^m (l_i^(N)+l_i^(N)*)`.

**Lemma (truncated-Fock trace obstruction).**  No scalar rescaling of `S_N`
can make both its second and fourth normalized matrix moments converge to
the vacuum moments of the free Gaussian sum of `m` standard semicirculars.

**Proof.**  In the word basis, `S_N` is the adjacency matrix of the rooted
`m`-ary tree of depth `N`.  Its number of vertices is

`D_N=1+m+...+m^N`.

The number of edges is `D_N-1`, hence

`tr_N(S_N^2)=2(D_N-1)/D_N -> 2`.

For any finite tree with adjacency matrix `A`,

`Tr(A^4)=2|E|+4 sum_v binom(deg(v),2)`:

a closed walk of length four either traverses one edge twice or uses two
distinct edges incident at its middle vertex.  In the rooted `m`-ary tree,
the leaves have asymptotic vertex proportion `(m-1)/m` and degree `1`, while
the non-leaf, non-root vertices have asymptotic proportion `1/m` and degree
`m+1`; the root is negligible.  Therefore

`tr_N(S_N^4) -> 2+4*(1/m)*binom(m+1,2)=2m+4`.

The free Gaussian sum has second moment `m` and fourth moment `2m^2`.
Matching the second moment forces a rescaling with square `m/2`; the resulting
fourth moment is

`(m^2/4)(2m+4)=m^2(m+2)/2`,

which equals `2m^2` only for `m=2`, contrary to `m>=3`.  End proof.

Thus finite Fock truncation gives exact covariance implementers but the wrong
tracial state: uniform dimension is concentrated near the boundary of the
tree, while the free trace is the vacuum state.  GUE/random-matrix models
give the correct free trace, but a generic tuple has no coherent samplewise
implementers for the quasi-regular action.  Projecting one GUE onto the
finite-level `Gamma`-commutant is therefore not merely one ansatz among many;
it is the direct way to combine the two requirements.  Its unresolved input
is precisely a positive-profile centered-commutant overlap estimate, as in
the corrected criterion above.

### One-number Haar criterion: full freeness is unnecessary

The single-trace criterion removes nearly all of the free-probability burden.
Fix a strict compressor `t` and `gamma in Gamma minus t Gamma t^-1`, and put

`h=t^-1 gamma t`, so `h notin Gamma`.

Let `u_n` be normalized-HS almost-representations of `G` on exhausting
windows, with window defect `epsilon_n`.  Let `W_n` be the finite-dimensional
unital C*-algebra generated by the images of the required `Gamma`-window,
put `C_n=W_n'`, and define the exact word matrix

`x_n=u_n(t)^* u_n(gamma) u_n(t)`.

Set

`Delta_n=1-||E_(W_n)(x_n)||_2^2`
`       =||x_n-E_(W_n)(x_n)||_2^2`.

The second equality is the Pythagorean identity for the trace-preserving
conditional expectation and uses that `x_n` is unitary.

**Theorem (one-number Haar criterion).**  If `Delta_n>0` eventually and

`epsilon_n/Delta_n -> 0`,

then a hyperlinear nonsofic group exists.

**Proof.**  Haar-average over the compact unitary group `U(C_n)`.  Its
twirling map is the trace-preserving conditional expectation onto the
bicommutant:

`integral_(v in U(C_n)) v x v^* dv = E_(C_n')(x)=E_(W_n)(x)`.

Therefore

`integral Re tr(v x_n v^* x_n^*) dv`
` =tr(E_(W_n)(x_n)x_n^*)`
` =||E_(W_n)(x_n)||_2^2=1-Delta_n`.

Choose `v_n in U(C_n)` whose real correlation is at most this average.  Map
the distinguished free lamp generator `k` of

`H_Z=G *_Gamma (Gamma x Z)`

to `v_n`.  It commutes **exactly** with the selected `Gamma` matrices.  The
Kun--Thom witness word evaluates, with no approximation in this calculation,
as

`tr([u_n(t)v_nu_n(t)^*,u_n(gamma)])`
` =tr(v_n x_n v_n^* x_n^*)`.

Hence its trace gap `kappa_n=1-Re tr(w_n)` satisfies
`kappa_n>=Delta_n`.  All defining-relation errors on a fixed window are at
most a window-dependent constant times `epsilon_n`; the lamp--`Gamma`
relations have zero error.  After the usual diagonal choice of windows, the
trace-gap/defect criterion applies because `epsilon_n/Delta_n->0`.  It gives
a tracial ultraproduct homomorphism detecting the witness, and the
single-trace Kun--Thom theorem produces a hyperlinear nonsofic quotient.
End proof.

This is weaker than XCV/XCVI and than the proposed commutant-Wick face:

* only the single element `h=t^-1 gamma t` is tested;
* `E_W(x_n)` need not tend to zero--any gap beating the relation defect is
  enough;
* no minimum block multiplicity is needed;
* no higher alternating moments, asymptotic freeness, or concentration is
  needed;
* the chosen lamp may depend on `n` and on the window.

The entire free-lamp route is therefore reduced to one scalar inequality:

`distance_2(x_n,W_n)^2 >> epsilon_n`.

Liftable/finite-quotient models have `Delta_n=0` at the profinitely invisible
element.  Shulman's norm-MF theorem forces `x_n` to escape `W_n` in operator
norm somewhere, but permits that escape on trace fraction `o(epsilon_n)`.
Thus the new theorem isolates the exact remaining rank-blindness without any
extraneous free-probability conditions.

### Quantifier audit of Shulman Theorem 10: no profile follows

The primary proof has two independent asymptotic parameters.  The outer
parameter `k` indexes asymptotic homomorphisms

`Phi_k:A *_C A -> M_4(D)`,

and controls operator-norm multiplicativity in the `D`-norm, hence uniformly
over all inner matrix coordinates.  For each fixed `k`, the value
`Phi_k(a)` is a sequence of matrices indexed by an inner coordinate `n`, and
the quotient map `q:D->B(H)` records only its strong operator limit as
`n->infinity`.  Faithfulness/separation is recovered only after taking this
inner limit.

Nothing in Lemmas 7--9 or Theorem 10 bounds the inner coordinate at which a
fixed witness becomes separated in terms of the outer multiplicativity
error.  The proof invokes an arbitrary continuous section of a quotient and
an arbitrary quasicentral approximate unit.  Both are qualitative.  In
particular, strong convergence permits an operator-norm-visible defect to
have rank one at every finite coordinate.

The logical insufficiency can be stated as an exact counterarray.  The
estimates proved in the paper have the abstract form

`epsilon_k -> 0`,

uniformly in `n`, and, for every fixed `k`, eventual operator-norm separation
of the witness as `n->infinity`.  They are compatible with

`epsilon_k=1/k`,

`d_(k,n)=n`,

and a witness which is `c`-separated from the identity on only `r(n)`
dimensions whenever `n>=exp(k^2)`, and is unseparated before that threshold,
where `r(n)->infinity` arbitrarily slowly (for example
`r(n)=floor(log log(n+e^e))`).  The increasing support is compatible with
strong convergence even to an infinite-rank operator, while its normalized
trace gap is only of order `r(n)/n`.  Consequently, already at the smallest
separating coordinate,

`epsilon_k / Delta_(k,n) >= exp(k^2)/(k r(exp(k^2)))`,

and also `epsilon_k sqrt(d_(k,n))>=exp(k^2/2)/k`.  Thus neither the
one-number Haar profile nor Agent Two's square-root profile is a logical
consequence of the two qualitative limits.

This counterarray is not a proof that no favorable choice of Shulman lifts
exists.  It proves the exact scoped conclusion:

> the published construction supplies no dimension/error dependency from
> which either known MF-to-hyperlinear bridge can be deduced.

Any successful extraction must add a new quantitative theorem about the
continuous section, the quasicentral approximate unit, or the normalized
rank of the fold-kernel witness.  Reindexing or choosing the inner coordinate
after the outer parameter does not provide it.

### Kazhdan extreme-point audit: component selection does not create an ergodic centralizer

There is a tempting shortcut for Thom's finitely presented, Kazhdan,
hyperlinear, non-residually-finite group `K`: start from a hypothetical sofic
approximation, use property (T) to decompose it into expander components, keep
one component, and hope that the resulting sofic representation is extreme.
If this worked, the Hayes--Kunnawalkam Elayavalli centralizer condition and
Alekseev--Thom would force `K` to be residually finite, a contradiction.

The shortcut fails at a precise and already-open step.

Păunescu's Theorem 4.8 in *Convex Structures Revisited* identifies an extreme
point of the amplified diffuse sofic-representation space with ergodicity of
the associated commutant full-group action.  The same paper explicitly says
that existence of extreme points for an arbitrary sofic group remains open.
This has not become automatic for Kazhdan groups.  Alekseev--Thom,
arXiv:2608.05362, Theorem A, prove instead that a Kazhdan group admitting a
sofic embedding whose permutation-ultraproduct centralizer acts ergodically
is LEF, and is residually finite if finitely presented.  Their Theorem 3.1
shows that after an essentially equivalent modification the centralizer is a
metric ultraproduct of finite permutation groups; it does not assert
ergodicity.  Their paper retains the Hayes--Kunnawalkam Elayavalli assertion
as Conjecture 1.1.

The finite obstruction behind this distinction is elementary.

**Lemma (centralizer orbits of a transitive component).**  Let a finite group
`H` act transitively on `X=H/L` by left translations.  Then

`C_Sym(X)(H) = N_H(L)/L`,

acting by right translations, and every centralizer orbit has cardinality
`[N_H(L):L]`.  Consequently the centralizer is transitive on `X` if and only
if `N_H(L)=H`, equivalently `L` is normal in `H`.  If the action of `H` on
`H/L` is faithful, transitivity of the centralizer is equivalent to `L=1`,
so the action is regular.

**Proof.**  A centralizing permutation is determined by the image `aL` of the
base point `L`.  Well-definedness of `gL -> gaL` is exactly
`a in N_H(L)`, with two choices defining the same permutation exactly modulo
`L`.  The orbit of `L` is therefore `N_H(L)/L`; conjugating by a left
translation gives the same orbit size at every point.  It is all of `H/L`
exactly when `N_H(L)=H`.  The kernel of the left action is the core of `L`;
if `L` is normal and the action faithful, this core is `L=1`.  End proof.

Thus Kun's expander decomposition only supplies connected expanding
components.  Connectedness/transitivity of the generated finite action does
not make its centralizer transitive; that would require the much stronger
regular/finite-quotient geometry.  Amplifying a component creates
permutations of identical copies but does not remove the internal
centralizer-orbit partition.  Alekseev--Thom Lemma 2.8 expresses the
ultraproduct version: ergodicity of a rigid centralizer forces a conull
finite-level centralizer orbit, and Proposition 2.9 turns this into LEF.

In particular, if Thom's `K` is sofic, then no sofic embedding of `K` can
have an ergodic permutation centralizer, by Alekseev--Thom and finite
presentability/non-residual-finiteness.  Subject to Păunescu's amplified
full-group identification being used with its exact notion of equivalence,
`Sof(K)` would therefore be nonempty but have no extreme point.  This is not
a contradiction: the recent Munteanu--Păunescu work proves that minimal
faces are extreme but also exhibits decreasing closed faces with empty
intersection, so no Krein--Milman compactness argument supplies an extreme
point.

The rigorous consequence is negative but useful: property (T) plus expander
component selection does not prove the HKE conjecture for `K`.  The route

`K sofic -> extreme/ergodic-centralizer model -> LEF -> RF`

still has its entire first implication open.  Any proof of it for this `K`
would already prove `K` nonsofic; it cannot be treated as a routine selection
lemma.

### Exact commutant-compression dichotomy: the minimal free-lamp face

The one-number finite-level criterion has an exact ultraproduct form with no
rate, block-multiplicity, or freeness hypothesis.  Let `Gamma<G` be the
Kun--Thom pair, let `t` be a strict compressor,

`t Gamma t^-1 < Gamma`,

and let `rho:G->U(M)` be an injective homomorphism into a Connes-embeddable
finite tracial von Neumann algebra.  Put

`N=W*(rho(Gamma))` and `P=N' intersect M`.

Since `rho(t)N rho(t)^*` is contained in `N`, commutants reverse the
inclusion:

`P subset rho(t) P rho(t)^*`.

**Theorem (strict commutant compression criterion).**  If this inclusion is
strict for one compressor `t`, then a hyperlinear nonsofic group exists.

**Proof.**  A proper inclusion of unital von Neumann algebras contains a
unitary in the larger algebra but not the smaller one (unitaries linearly
span a von Neumann algebra).  Choose

`y in U(rho(t)P rho(t)^*) minus P`

and put `v=rho(t)^* y rho(t) in U(P)`.  Because `y` is not in
`P=N' intersect M`, it fails to commute with some group unitary
`rho(gamma)`, `gamma in Gamma`.  Since `y` commutes with
`rho(t Gamma t^-1)`, this `gamma` automatically lies outside
`t Gamma t^-1`.

By the amalgam universal property there is a homomorphism

`eta:H_Z=G *_Gamma (Gamma x Z) -> U(M)`

which restricts to `rho` on `G` and maps the free lamp generator `k` to
`v`.  The Kun--Thom witness has image

`eta([t k t^-1,gamma])=[y,rho(gamma)] != 1`.

Let `Q=eta(H_Z)`.  It is hyperlinear because it is a countable subgroup of
the unitary group of the Connes-embeddable finite algebra `M`.  It is
nonsofic: a sofic embedding of `Q`, composed with `eta`, is faithful on the
copy of `G`; Kun--Thom centralizer normalization then kills the displayed
witness, contradicting its nontriviality in `Q`.  End proof.

Thus the exact unitary analogue of Kun--Thom's permutation theorem is a
dichotomy.  In every tracial embedding one automatically has the one-sided
inclusion above.  Either it is strict somewhere, and the main question has a
negative answer, or every compressor normalizes the relative commutant.  If
the compressors generate `G`, the latter says that `rho(G)` normalizes
`rho(Gamma)' intersect M`, exactly the rigidity statement that kills the
free lamp in permutations.

The finite-level number

`Delta_n=dist_2(u_n(t)^*u_n(gamma)u_n(t),W_n)^2`

is a coordinate form of strictness: a nonzero ultraproduct commutator gives
a fixed positive trace gap while the relation defect tends to zero, so the
earlier `epsilon_n/Delta_n` condition is automatic after passing to the
ultraproduct witness.  Conversely liftable models have equality and
`Delta_n=0` at the invisible letters.

This criterion also scopes a tempting Popa route.  A factorial relative
commutant is not enough: a factor can contain a proper unital copy of itself,
and factoriality does not imply

`(rho(L Gamma)' intersect R^omega)' intersect R^omega = rho(L Gamma)`.

The Popa factorial-commutant embedding problem remains open for general
property-(T) factors, and even a positive solution would not by itself give
the bicommutant identity needed to force strictness here.

### Two-extension criterion: relative non-uniqueness already suffices

There is a second exact formulation which can be easier to attack than a
relative commutant directly.

**Theorem (two extensions of one Gamma-model).**  Let `M` be a
Connes-embeddable finite tracial von Neumann algebra.  Suppose

`rho_1,rho_2:G->U(M)`

are injective trace-preserving group homomorphisms satisfying

`rho_1(gamma)=rho_2(gamma)` for every `gamma in Gamma`,

and for some compressor `t` and `gamma in Gamma` one has

`rho_1(t^-1 gamma t) != rho_2(t^-1 gamma t)`.

Then a hyperlinear nonsofic group exists.

**Proof.**  In `M_2(M)` form

`rho(g)=diag(rho_1(g),rho_2(g))`

and let `v=[[0,1],[1,0]]`.  The equality of the restrictions says that `v`
commutes with `rho(Gamma)`, so it defines the free lamp.  Put

`y=rho(t)v rho(t)^*`.

The upper-right corner of `[y,rho(gamma)]` vanishes exactly when

`rho_1(t)^* rho_1(gamma) rho_1(t)`
` =rho_2(t)^* rho_2(gamma) rho_2(t)`,

which is precisely equality of the two images of `t^-1 gamma t` (the
restrictions agree on `gamma`).  Hence the stated disagreement makes the
Kun--Thom witness nontrivial.  Apply the preceding image-quotient argument.
End proof.

Equivalently, it is enough to find an automorphism of a Connes-embeddable
ambient algebra which fixes `rho(Gamma)` pointwise but moves one invisible
conjugate `rho(t^-1 gamma t)`.  In model-theoretic language, it is enough for
that conjugate not to belong to the definable closure of `rho(Gamma)` in a
sufficiently homogeneous ambient model.  This observation does not prove
the needed non-uniqueness: definable closure in tracial von Neumann algebras
can be strictly larger than the generated von Neumann algebra.  It identifies
the exact remaining relative rigidity question.

Finally, this corrects one statement in the supplied consolidated research
state.  A leak at one invisible letter is not enough for the older XCV
*full-amalgamated-freeness* hypothesis, but it **is** enough for the later
one-number/image-quotient argument.  No propagation to all reduced words is
needed once the aim is a hyperlinear nonsofic quotient rather than
faithfulness of the whole free-lamp group.

### Exact finite-dimensional relative uniqueness

The two-extension criterion cannot be met by coordinatewise genuine
finite-dimensional representations.

**Lemma.**  Let `t Gamma t^-1 <= Gamma`, and let

`pi_1,pi_2:G->U(d)`

be genuine finite-dimensional representations satisfying
`pi_1|Gamma=pi_2|Gamma`.  Then for every `gamma in Gamma`,

`pi_1(t^-1 gamma t)=pi_2(t^-1 gamma t)`.

**Proof.**  Let `W=C*(pi_1(Gamma))=C*(pi_2(Gamma))`.  Conjugation by either
`pi_i(t)` sends `W` into itself, because `t Gamma t^-1<=Gamma`.  The image is
unitarily conjugate to `W`, hence has the same finite vector-space dimension;
therefore the inclusion is equality.  Thus

`alpha_i=Ad(pi_i(t))|W`

is an automorphism of `W`.  For every `delta in Gamma`,

`alpha_i(pi_1(delta))=pi_i(t delta t^-1)`.

Both the source matrices and the right-hand sides agree for `i=1,2`, since
all involved group elements lie in `Gamma`.  The group matrices generate
`W`, so `alpha_1=alpha_2`.  Applying the common inverse to the common matrix
`pi_1(gamma)=pi_2(gamma)` proves the assertion.  End proof.

Equivalently, the block-flip witness from the two-extension theorem is killed
in every exact finite coordinate.  Any successful pair of extensions in a
tracial matrix ultraproduct must therefore exploit normalized-HS defects on
coordinate sets whose trace profile dominates those defects.  This is the
same defect/rank interface as the one-number Haar criterion, now derived
from exact relative uniqueness rather than from the free-lamp presentation.

Alekseev--Thom Open Problem 6.2 is the closest published formulation of the
remaining lifting issue.  For a Kazhdan group homomorphism into a tracial
matrix ultraproduct it asks whether, after asymptotically negligible dimension
changes, the relative commutant is an ultraproduct of finite-dimensional
algebras, and more strongly whether these algebras can be taken as exact
centralizers of lifts of a fixed generating set.  A sufficiently uniform
positive answer, applied to the `Gamma`-restriction and combined with the
finite-dimensional equality above, would force unitary centralizer
normalization and close this free-lamp counterexample route.  A strict
commutant-compression model would refute precisely that normalization
phenomenon.  The published problem is open; it must not be used as an input.

The two exact criteria above are in fact the same obstruction in different
coordinates.  For a fixed tracial embedding `rho`, the following are
equivalent:

1. `P` is properly contained in `rho(t)P rho(t)^*`;
2. for some `gamma in Gamma` and `v in U(P)`,
   `[v,rho(t^-1 gamma t)] != 1`;
3. the two embeddings `rho` and `Ad(v) o rho` agree pointwise on `Gamma` but
   disagree on `t^-1 gamma t`.

For `(1)=>(2)`, choose `y=rho(t)v rho(t)^*` in the larger commutant but not
the smaller one, as in the strict-compression proof.  `(2)=>(3)` is
immediate because `v` commutes with `rho(Gamma)`.  Conversely, `(2)` implies
that `rho(t)v rho(t)^*` belongs to `rho(t)P rho(t)^*` but not to `P`, giving
strictness.  The block-flip construction shows that an arbitrary pair of
extensions as in the two-extension theorem can always be converted into
this fixed-embedding form after passing to `M_2(M)`.

So the terminal free-lamp question is exactly non-uniqueness of extension of
a `Gamma`-model to `G`, measured at one inverse-compressed element.  Exact
finite-dimensional extensions are unique there by the lemma; a counterexample
requires this uniqueness to fail only after passage to a tracial
ultraproduct.

### Faithfulness is free; an action-theoretic corollary

The representation exhibiting strict commutant compression need not itself
be faithful or have the regular group trace.

**Lemma (faithful tensor completion).**  Suppose `G` is hyperlinear and
`sigma:G->U(S)` is any homomorphism into a Connes-embeddable finite tracial
von Neumann algebra.  If there are `v in U(sigma(Gamma)' intersect S)` and
`gamma in Gamma` such that

`[v,sigma(t^-1 gamma t)] != 1`,

then a hyperlinear nonsofic group exists.

**Proof.**  Let `rho_0:G->U(R^omega)` be a faithful hyperlinear embedding and
put `rho(g)=rho_0(g) tensor sigma(g)`.  This is faithful.  The unitary
`1 tensor v` commutes with `rho(Gamma)`, while

`[1 tensor v,rho(t^-1 gamma t)]`
` =1 tensor [v,sigma(t^-1 gamma t)]`

is nontrivial.  Apply the strict-commutant/free-lamp image theorem in the
Connes-embeddable tensor product.  End proof.

Consequently one can search among arbitrary finite characters/representations
of `G`; trace separation of `G` is supplied afterward by tensoring.

There is an exact p.m.p.-action version.  Let `G` act trace-preservingly on an
abelian finite algebra `A=L-infinity(X)`, and suppose the crossed product
`A crossed G` is Connes-embeddable.  If

`A^Gamma` is not contained in `A^(t^-1 Gamma t)`,

then the main problem has a negative answer.  Indeed choose a unitary
`v in A^Gamma` moved by some `t^-1 gamma t`; the canonical group unitaries and
`v` satisfy the preceding lemma.  The quasi-regular Gaussian/generalized
Bernoulli criterion recorded earlier is the special case in which the
coordinate at `Gamma` is fixed by `Gamma` and moved by an element outside
`Gamma`.

This also states the exact obstruction to a cheap sofic-action proof.  A
sofic model of such an action would make the crossed product Connes-embeddable
and immediately yield the counterexample.  Kun--Thom's action rigidity rules
out the coordinate/generalized-Bernoulli realization for their pair; an
abstractly Connes-embeddable but nonsofic action remains sufficient and open.

### Centralizer lifting does not finish Thom's K

For a hypothetical sofic embedding of Thom's finitely presented Kazhdan
group `K`, Alekseev--Thom Theorem 3.1 does allow, after an essentially
equivalent modification, the permutation centralizer to be written as a
metric ultraproduct of finite groups `A_n`.  Since the central Prüfer group
of `K` lies in that centralizer, finite-order surgery can represent every
fixed initial segment

`C_p < C_(p^2) < ... < C_(p^m)`

by coherent finite permutations at asymptotically zero cost, followed by a
diagonal choice with `m->infinity`.

This is not a contradiction.  The approximating permutations of the rest of
`K` still form only an almost action on the quotient of the central orbits.
Neither Theorem 3.1 nor its finite-groupoid correction turns that quotient
model into a genuine finite group representation of `K/C_(p^m)`.  Doing so
would require exactly the flexible P-stability/phase-factorization statement
already isolated in the Thom lane.  The divisible central tower itself is
perfectly compatible with a metric ultraproduct of finite groups (use cyclic
groups of orders tending through powers of `p`).

Thus the new centralizer theorem supplies finite-stage coordinates for the
Prüfer tower but does not upgrade approximate multiplication of `K`.  It
cannot be combined with finite-quotient collapse to prove `K` nonsofic
without a genuinely new stability theorem.

### Lavi--Levit character rigidity cannot see strict commutant compression

Lavi--Levit, Corollary 1.3 of arXiv:2007.15547, says that for a commutative
Noetherian ring `R` and `d > max{sr(R),2}`, every extreme character of
`EL_d(R)` is induced from a finite-dimensional representation of a particular
normal subgroup.  Here "induced" means that the character is zero outside
that subgroup.  It does **not** say that the character's GNS representation
is finite-dimensional: inducing from an infinite-index normal subgroup is
normally infinite-dimensional.  Dogon--Vigdorovich's 2025 implication from
flexible Hilbert--Schmidt stability to character rigidity does not reverse
this loss; its stability hypothesis is itself open in the relevant cases.

More decisively, scalar character data are formally blind to the exact
strict-commutant certificate.

**Lemma (regular-character camouflage).**  Let `G` be hyperlinear and let

`sigma:G -> U(S)`

be any homomorphism into a Connes-embeddable finite tracial von Neumann
algebra.  Let `lambda:G -> U(LG)` be the left regular representation and put

`rho(g)=lambda(g) tensor sigma(g)`.

Then the scalar character of `rho|Gamma` is the regular character

`tau(rho(gamma)) = 1_(gamma=e)`

independently of `sigma`.  Nevertheless, if

`v in sigma(Gamma)' intersect S`

fails to commute with `sigma(t^-1 gamma t)`, then `1 tensor v` belongs to
`rho(Gamma)'` and fails to commute with `rho(t^-1 gamma t)`.  Hence `rho`
has strict relative-commutant compression and produces a hyperlinear
nonsofic image by the strict-compression theorem.

**Proof.**  The trace factorizes, and `tau_LG(lambda(gamma))` is zero for
`gamma != e`; this proves the character assertion.  The commutator identity

`[1 tensor v, rho(h)]_group = 1 tensor [v,sigma(h)]_group`

proves the relative assertion.  End proof.

Thus even the strongest possible classification of the scalar trace on
`Gamma` cannot decide the terminal free-lamp question: every auxiliary model,
including a successful one, becomes the *same regular character* after the
faithful tensor completion already required downstream.  What varies is the
`Gamma`-bimodule multiplicity/relative commutant, not the character.

There is a useful sterile subcase.  If the von Neumann algebra
`W*(sigma(Gamma))` is finite-dimensional, then

`Ad(sigma(t))(W*(sigma(Gamma))) <= W*(sigma(Gamma))`

is equality by finite dimension, so the commutant is normalized and no
strictness occurs.  Lavi--Levit's induced finite-dimensional source does not
put a general GNS representation in this subcase.  In particular, the
regular character is allowed and is exactly the sector in which the tensor
camouflage lemma places every auxiliary construction.

Conclusion: the character-only lane is closed.  It can become relevant only
when paired with a genuinely stronger theorem controlling the relative
commutant or decomposing the whole `Gamma`-bimodule (for example the open
Alekseev--Thom centralizer-lifting problem).  Level-ideal or scalar-character
classification alone supplies no arrow toward either equality or strictness
of

`rho(Gamma)' intersect M <= rho(t)(rho(Gamma)' intersect M)rho(t)^*`.

### The exact relative-cocycle formulation

The two-extension criterion is precisely a relative first-cohomology problem.

Fix a homomorphism `pi:G -> U(S)` into a Connes-embeddable finite tracial
von Neumann algebra, and let `alpha_g=Ad(pi(g))`.  A unitary `alpha`-cocycle
is a map `c:G -> U(S)` satisfying

`c(gh)=c(g) alpha_g(c(h))`.

It defines a second representation

`pi_c(g)=c(g)pi(g)`.

**Theorem (relative cocycle certificate).**  A hyperlinear nonsofic group
exists if there are `pi` and `c` as above such that

`c(gamma)=1` for every `gamma in Gamma`,

but

`c(t^-1 gamma t) != 1`

for some compressor `t` and `gamma in Gamma`.  Conversely, every pair of
extensions in the two-extension theorem gives such a cocycle, after replacing
the common ambient algebra by `M_2(S)` if necessary.

**Proof.**  The cocycle equation is exactly the assertion that `pi_c` is a
homomorphism.  Triviality on `Gamma` says that `pi_c` and `pi` agree there,
while the displayed inequality says that they disagree on the required
inverse-compressed element.  Apply the two-extension theorem and faithful
tensor completion.  Conversely, for two representations `pi_1,pi_2` put

`c(g)=pi_2(g)pi_1(g)^*`.

This is a cocycle for `Ad(pi_1)` and has the stated relative properties.
End proof.

The universal algebraic model of this cocycle is completely concrete.  Let

`A=directSum_(G/Gamma) Z`

with the permutation action, and define

`b(g)=delta_(g Gamma)-delta_Gamma`.

Then

`b(gh)=b(g)+g b(h)`,  and  `b|Gamma=0`.

Moreover `b(h) != 0` exactly when `h notin Gamma`.  Exponentiating the lamp
coordinate places this cocycle in the generalized wreath/free-lamp models.
Thus the relative cocycle certainly exists algebraically; the whole problem
is to realize a nonzero image of it in a Connes-embeddable finite tracial
target.

The finite-dimensional uniqueness lemma says that every unitary cocycle in
a genuine finite-dimensional representation which is trivial on `Gamma` is
also trivial on every `t^-1 Gamma t`.  Equivalently, the universal coset
cocycle dies in every finite `G`-module image.  This recovers the profinite
invisibility obstruction in first-cohomology language and proves that any
successful cocycle must be genuinely nonliftable/order-one.

The quasi-regular Gaussian and free-Bogoliubov proposals are functorial
realisations of this same cocycle.  Their crossed products are known to be
Connes-embeddable in the regular/amenable representation cone.  For
`ell^2(G/Gamma)`, weak containment in the regular representation is
equivalent to amenability of `Gamma`, which fails for the Kun--Thom pair.
No general Connes-embeddability theorem for an arbitrary free-Bogoliubov
crossed product was located; asserting one here would already prove the
desired counterexample.  Hence free Gaussian functoriality is a precise
restatement of the certificate, not a completed permanence argument.

### Amenable Gamma-algebras cannot compress strictly

The finite-dimensional sterile subcase extends to every amenable von Neumann
algebra generated by the `Gamma`-image.

**Theorem (amenable-sector normalization).**  Let `Gamma` have property
`(T)`, let `alpha:Gamma -> Gamma` be an injective endomorphism, and suppose
`sigma` is a unitary representation in a finite tracial von Neumann algebra
`S`.  Put

`N=W*(sigma(Gamma))`.

Assume that a unitary `U in S` satisfies

`U sigma(gamma) U* = sigma(alpha(gamma))`

for every `gamma`, so that `beta=Ad(U)|N` is a trace-preserving embedding of
`N` into itself.  If `N` is amenable, then

`beta(N)=N`.

In particular, for a Kun--Thom compressor `t`, strict relative-commutant
compression cannot occur in any auxiliary representation for which
`W*(sigma(Gamma))` is amenable.

**Proof.**  Centrally decompose the tracial representation of `Gamma`
generating `N`.  Almost every fiber is an amenable finite factor
representation.  An amenable unitary representation of a Kazhdan group
contains a nonzero finite-dimensional subrepresentation: amenability gives
almost invariant vectors in `pi tensor conjugate(pi)`, and property `(T)`
turns one into an invariant vector.  In a factor representation a nonzero
finite-dimensional subrepresentation forces the whole generated factor to
be finite-dimensional (a nonzero finite-rank projection in the factor
commutant has central support one).  Hence the central decomposition is
supported on normalized characters of finite-dimensional irreducible
representations.

A Kazhdan group has only finitely many inequivalent irreducible unitary
representations of each fixed finite dimension (the finite-representation-
type theorem used by Rapinchuk).  Thus these factor characters form a
countable state space, finite in each dimension.

Precomposition with `alpha` sends the character of a `D`-dimensional
irreducible representation `pi` to the convex combination obtained by
decomposing `pi o alpha` into irreducibles.  Regard the normalized
dimension-multiplicity coefficients as transition probabilities.  Every
target constituent has dimension at most `D`.  The equality

`tau(sigma(gamma)) = tau(sigma(alpha(gamma)))`

and uniqueness of central decomposition say exactly that the central measure
is stationary for this Markov kernel.

For every integer `m`, the set of states of dimension at most `m` is
absorbing.  Stationarity therefore forbids positive mass from entering it
from larger dimensions.  Taking all `m` shows that the dimension cannot drop
on a transition of positive stationary mass.  But a `D`-dimensional
representation whose irreducible constituents all have dimension `D` has
exactly one constituent, with multiplicity one.  Therefore `pi o alpha` is
irreducible of the same dimension almost everywhere.

The transition is now a deterministic map on the finite set of irreducibles
of each dimension.  A stationary probability measure for such a map is
supported on its cycles.  Consequently the induced map on the center is
invertible modulo null sets, and on each factor it is a unital embedding
`M_D -> M_D`, hence an automorphism.  Therefore `beta(N)=N`.  End proof.

Since commutants reverse inclusions, this gives

`sigma(Gamma)' intersect S = U(sigma(Gamma)' intersect S)U*`.

So the auxiliary representation sought by the strict-compression theorem
must have a **nonamenable** `Gamma`-algebra.  This rules out a direct
hyperfinite realization of the relative cocycle and explains why CAR/Gaussian
base algebras help only if the full implementing representation already
creates a nonamenable crossed-product component.  It does not rule out a
Connes-embeddable nonamenable `N`, such as a copy of `L(Gamma)`; that is now
the exact surviving sector.

### The nonamenable part reduces to the regular Laurent sector

For the explicit Kun--Thom pair, character rigidity and the invariant-ideal
theorem reduce the surviving nonamenable sector further.  Put

`R=F_q[x_1^(+-1),...,x_d^(+-1)]`,

`Lambda=EL_r(R) normal G`.

Assume the Lavi--Levit stable-range hypothesis
`r > max{sr(R),2}`.

**Theorem (regular-sector reduction).**  Let `sigma:G -> U(S)` be a
homomorphism into a finite tracial von Neumann algebra, and centrally
decompose the trace of `sigma|Lambda` into extreme characters.  Almost every
factor character occurring in this decomposition is of exactly one of the
following two kinds:

1. it factors through a finite quotient of `Lambda`;
2. its level ideal is zero, and it is induced from the finite center of
   `Lambda`, hence is a central twist of the regular character of `Lambda`.

Consequently every amenable factor summand is finite-dimensional, while every
possible diffuse nonamenable summand is a regular Laurent group-factor
summand (up to the finite central twist).  Strict commutant compression, if it
occurs at all, must occur on the restriction of one of these regular summands
to the polynomial subgroup `Gamma`.

**Proof.**  The trace of `sigma|Lambda` is invariant under conjugation by the
`SL_d(Z)` factor of `G`.  Uniqueness of the Choquet/central decomposition
therefore makes its representing probability measure on extreme characters
`SL_d(Z)`-invariant.  Lavi--Levit attach equivariantly to every extreme
character its level ideal.  Push the representing measure to the countable
set of ideals of `R`.  Every invariant probability measure on a countable set
is supported on finite orbits.

Let `I` lie in such a finite orbit.  If `I != 0`, the intersection of its
finite orbit is nonzero: `R` is a domain, and the product of the orbit ideals
is a nonzero ideal contained in that intersection.  The intersection is
`SL_d(Z)`-invariant.  By the invariant-ideal theorem proved above it has finite
codimension over `F_q`; hence so does `I`.

For a Lavi--Levit character with level ideal `I` and kernel ideal `K`, one has
`K*=I`, so `I/K` is finite.  If `I` has finite codimension, then `R/K` is a
finite ring.  Corollary 1.3 therefore makes the whole character factor through
a finite group, giving case 1.

The only alternative is `I=0`.  Here the normal subgroup from which the
character is induced is the preimage of the center modulo the zero ideal,
namely the finite scalar center of `Lambda`.  The character vanishes off that
center and is a central twist there.  Its GNS factor is the corresponding
twisted regular group factor of the central quotient, giving case 2.  End
proof.

On a regular/centrally twisted Laurent summand, restriction to `Gamma` is a
multiple of the corresponding regular/centrally twisted representation of
`Gamma` (decompose `ell^2(Lambda)` into left `Gamma`-cosets).  Thus the
terminal exact problem can be stated without unknown level-ideal parameters:

> Construct a Connes-embeddable finite extension of one of the finitely many
> centrally twisted regular inclusions associated with
> `Gamma <= Lambda`, in which a compressor implementation makes the
> `Gamma`-commutant grow strictly.

The canonical group factor `L(G)` does not do this: the relevant group
centralizers are trivial, so both commutants are scalar.  The missing object
is therefore a nontrivial Connes-embeddable multiplicity/correspondence over
the regular `Gamma`-factor, not a new scalar trace.

### Thom's central free lamp: hyperlinearity is banked, nonsoficity is not

Let

`Ktilde=K_0(Z[1/p])`,  `C=Z <= Z(Ktilde)`,  `Q=Ktilde/C`.

Here `Ktilde` is residually finite and `Q` is Thom's finitely presented
hyperlinear Kazhdan group whose soficity is open.  Define the central
free-lamp amalgam

`H_c=Ktilde *_C (C x Z)`.

**Lemma (central free-lamp normal form).**

`H_c = (ast_(Q) Z) semidirect Ktilde`,

where `Ktilde` permutes the free factors through its left action on
`Ktilde/C=Q`.

**Proof.**  Retract `H_c` to `Ktilde` by killing the second `Z`-factor.  The
conjugate of that factor by `g in Ktilde` depends only on `gC`, because the
lamp commutes with `C`.  Bass--Serre normal form says that conjugates indexed
by distinct cosets freely generate the kernel.  End proof.

Hyperlinearity of `H_c` is unconditional.  At the von Neumann algebra level,

`L(H_c)=L(Ktilde) *_(L(C)) (L(C) tensorBar L(Z))`.

Both factors are Connes-embeddable and `L(C)` is amenable, so the standard
amenable-amalgam permanence theorem makes this free product Connes-embeddable.
Thus proving `H_c` nonsofic would solve the main problem immediately.

The nonsofic half is **not** supplied by the existing action results.  The
forward permanence theorem of Gao--Kunnawalkam Elayavalli--Patchell says that
a sofic action produces a sofic free generalized wreath product.  Its
converse is their Question 4.4.  A sofic approximation of the abstract group
`H_c` does not presently give a sofic model of the conjugation action on its
free factors.  The coordinate reverse-transfer theorem recorded above starts
only after such an automorphic/action model has been supplied; it does not
construct one from group soficity.  This is exactly the quantifier gap noted
by the authors in their discussion of Question 4.4.

Consequently the central free lamp is a valid banked-hyperlinearity target,
but its remaining nonsoficity problem is a special action-extraction/phase-
factorization problem, not an already proved consequence of Thom's quotient.
For the current record the three statements must remain separate:

1. `H_c` is hyperlinear -- proved by amenable amalgamation;
2. `Q` is non-LEF/non-initially-subamenable -- proved by Thom/de Cornulier;
3. `H_c` is nonsofic -- open, and would require a new bridge from an arbitrary
   sofic approximation of `H_c` to quotient/free-factor orbit data.

### Shulman doubles cannot manufacture weak MF for the Leavitt witness

The degree-zero/local-finite core and the Leavitt self-similarity suggest
trying to embed

`J=EL_4(L_(F_2)(1,2))`

across the two factors of a symmetric amalgam or an HNN extension and then
apply Shulman's weak-MF permanence theorem.  Property `(T)` rules out exactly
that strategy.

**Lemma (Bass--Serre confinement).**  Let `J` have property `(T)`.  Every
homomorphism

`J -> A *_C B`

whose image is isomorphic to `J` has image conjugate into `A` or `B`.
Likewise every embedding of `J` into an HNN extension is conjugate into the
base group.

**Proof.**  Property `(T)` implies Serre's property FA.  Let `J` act through
the embedding on the Bass--Serre tree of the amalgam or HNN extension.  It
fixes a vertex.  Vertex stabilizers are precisely conjugates of the vertex
groups (the base group in the HNN case).  End proof.

Consequently an embedding of the Leavitt witness into a Shulman symmetric
double cannot use its two-factor geometry: one factor already contains the
whole witness.  If that factor were locally finite or residually finite this
would be impossible, since subgroups inherit residual finiteness and `J` is
an infinite simple nonsofic group.  More generally, applying weak-MF
permanence to the double would add nothing unless weak MF of a group already
containing `J` had independently been established.

Thus the Leavitt self-similarity may still help construct operator-norm
microstates directly, but it cannot be converted into a nontrivial
Bass--Serre decomposition and fed to the symmetric-double theorem.  This
closes the proposed degree-zero-double/HNN shortcut without making any claim
about the still-open direct weak-MF certificate for `J`.

### The compressor has infinite index; regular tensor sectors are rigid

There are two tempting ways to turn the regular-sector reduction into a
finite correspondence: use the Jones basic construction for the compressed
subgroup, or tensor several regular/projectively regular sectors until a
relative commutant appears.  Neither works.

Fix the explicit compressor `t=t_(u_12)` from Kun--Thom Theorem E.  Its ring
image is

`S=F_q[x_1,x_1 x_2,x_3,...,x_d] < R_+=F_q[x_1,...,x_d]`,

and put `H=t Gamma t^-1=EL_r(S)`.

**Lemma (the compressed subgroup has infinite index).**

`[Gamma:H]=infinity`.

**Proof.**  The cosets

`e_12(x_2^n) H`,  `n>=1`,

are pairwise distinct.  Indeed, equality of the `m`th and `n`th cosets would
put

`e_12(x_2^m+x_2^n)`

in `EL_r(S)`.  Every entry of a matrix in `EL_r(S)` belongs to `S`, whereas
`x_2^m+x_2^n` does not: every monomial `x_1^a x_2^b` occurring in `S` has
`a>=b`, while the displayed polynomial has positive `x_2`-degree and zero
`x_1`-degree.  End proof.

Consequently

`[L(Gamma):L(H)]=infinity`.

The Jones basic construction for `L(H)<L(Gamma)` is therefore semifinite,
not a finite Connes-embeddable extension supplying the desired unitary.  This
does not rule out a more elaborate finite correspondence, but closes the
finite-index shortcut.

The tensor shortcut admits a general Fourier no-go.  Let

`Lambda=EL_r(F_q[x_1^(+-1),...,x_d^(+-1)])`.

Use the standard normal-subgroup/sandwich theorem for elementary groups over
the commutative domain `R_+`: every noncentral normal subgroup of `Gamma` in
rank at least three contains `E_r(R_+,I)` for a nonzero ideal `I`.

**Lemma (relative FC-centre).**  For every `m>=1`, an element of `Lambda^m`
with finite conjugacy orbit under the diagonal copy of `Gamma` belongs to
`Z(Lambda)^m`.

**Proof.**  If `a=(a_1,...,a_m)` has finite orbit, its stabilizer in `Gamma`
has finite index.  Its normal core `K` still has finite index and centralizes
every `a_j`.  The group `K` is noncentral (otherwise the infinite group
`Gamma` would be finite-by-centre), so the sandwich theorem supplies a
nonzero ideal `I` with `E_r(R_+,I)<=K`.

Regard `a_j` as a matrix over the Laurent domain.  For every `i!=k` and every
`s in I`, it commutes with `e_ik(s)=1+sE_ik`.  Choose one nonzero `s in I`.
The domain property cancels `s` from

`s(a_j E_ik-E_ik a_j)=0`,

so `a_j` commutes with every off-diagonal matrix unit.  The simultaneous
centralizer of these matrix units consists of scalar matrices.  Hence
`a_j in Z(Lambda)` for every `j`.  End proof.

**Theorem (regular tensor-sector rigidity).**  Embed `Gamma` diagonally in
`L(Lambda) tensorBar ... tensorBar L(Lambda)` (`m` factors).  Then

`L(diag Gamma)' intersect L(Lambda^m) = L(Z(Lambda)^m)`.

The same conclusion, with possibly a smaller finite-dimensional right-hand
side, holds for finite tensor products of centrally twisted regular Laurent
factors.  In particular every monomial substitution normalizes this relative
commutant, so no compressor gives strict commutant growth in any such finite
tensor sector.

**Proof.**  Write an element of `L(Lambda^m)` in its Fourier expansion.  If it
commutes with diagonal `Gamma`, conjugation permutes its Fourier coefficients.
The absolute values of the coefficients are constant on every diagonal
conjugacy orbit.  Square summability forces the coefficient to vanish on
every infinite orbit.  The relative FC-centre lemma confines the support to
`Z(Lambda)^m`, and the reverse inclusion is immediate.  In a cocycle-twisted
group factor conjugation also multiplies coefficients by phases; their
absolute values are still constant on orbits, so the identical support
argument applies.  The scalar centre is preserved by every ring
substitution.  End proof.

Thus the regular-sector reduction cannot be completed by taking tensor
powers, contragredient pairs, projective twists, or their finite direct sums.
The missing object really is an **external Connes-embeddable
`L(Gamma)`-correspondence** with nontrivial multiplicity.  Its strictness
cannot be visible in the Fourier support of any finite product of the regular
Laurent sector.  This is a rigorous restriction on the terminal certificate,
not a construction of it.

### Strict compression is an infinite Kazhdan projection in the left--right envelope

The word "external" in the preceding conclusion has a precise C*-algebraic
meaning.  Let

`sigma:G -> U(S)`

be a homomorphism into a finite tracial von Neumann algebra, and let `H=L2(S)`.
The adjoint representation is

`Ad_sigma(g)=L(sigma(g)) R(sigma(g)^*)`.

Let `p_Gamma in C*_max(Gamma)` be the Kazhdan projection and denote its image
under `Ad_sigma` by `p in B(H)`.  Thus

`pH=L2(sigma(Gamma)' intersect S)`.

Put `V=Ad_sigma(t)` for a compressor `t Gamma t^-1<=Gamma`.

**Theorem (left--right infiniteness criterion).**

`sigma(Gamma)' intersect S < sigma(t)(sigma(Gamma)' intersect S)sigma(t)^*`

if and only if

`V^* p V < p`.

In that event `p` is an infinite projection in the unital C*-algebra

`A_lr=C*(Ad_sigma(G),p) <= C*(L(sigma(G)),R(sigma(G))) <= B(L2(S))`:

the proper subprojection `V^*pV` is Murray--von Neumann equivalent to `p`.
Consequently `A_lr` is not finite, not stably finite, and not MF.

**Proof.**  If `xi` is fixed by `Gamma`, then for every `gamma in Gamma`,

`Ad_sigma(gamma)V^*xi`
` =V^* Ad_sigma(t gamma t^-1)xi=V^*xi`.

Hence `V^*(pH)<=pH`, which is equivalent to `V^*pV<=p`.  The range of
`VpV^*` is the space fixed by `t Gamma t^-1`; on bounded vectors this is

`L2(sigma(t)(sigma(Gamma)' intersect S)sigma(t)^*)`.

Thus equality of the two projections is exactly equality of the two relative
commutants, and properness is equivalent on both sides.  Finally
`V^*p=(V^*pV)V^*` is a partial isometry implementing Murray--von Neumann
equivalence of `p` and `V^*pV`.  End proof.

This theorem recovers several earlier no-go results at once.  In a genuine
finite-dimensional representation the left--right envelope is finite, so
the inclusion cannot be strict.  If the left--right representation factors
through a spatial tensor product of finite von Neumann algebras, its image is
finite and again strictness is impossible.  In particular this is the real
mechanism behind the amenable-sector theorem: for an amenable generated
factor the multiplication representation is spatial/min-continuous, whereas
for a nonamenable factor the left and right actions can generate an infinite
algebra (indeed all of `B(L2(S))` in the factorial standard form).

The criterion also identifies the exact relation with Kirchberg
factorization phenomena.  A strict Connes-embeddable model must have a
finite ambient algebra `S` but a **non-stably-finite left--right C*-envelope**.
Therefore no proof which first embeds both left and right copies into a finite
spatial tensor product can succeed.  Hyperlinearity of `S` alone does not
prevent this: Thom's examples show that hyperlinear Kazhdan groups can fail
the factorization property.  What is still missing is a representation of
the specific compressed pair for which this failure is carried by the
displayed Kazhdan projection and the compressor makes it properly infinite.

Equivalently, the remaining counterexample certificate may be stated in a
single C*-sentence:

> Find a Connes-embeddable tracial representation of the Kun--Thom ambient
> group such that the adjoint Kazhdan projection of `Gamma` is infinite in
> its left--right envelope, with `V^*pV<p` for one compressor.

This is stronger structural information than merely saying that a relative
commutant should grow.  It does not yet produce the required representation.

### Ordinary and local HS-instability cannot supply the infinite projection

The failure of Hilbert--Schmidt stability for infinite hyperlinear Kazhdan
groups is not, by itself, evidence for the strict-compression certificate.
The standard Becker--Lubotzky/Fournier--Facio--Gerasimova--Spaas sequence is
obtained by deleting one dimension from a genuine irreducible
representation.  It becomes genuine again after a negligible-dimensional
flexible enlargement.  Such models have normalized relative commutant.

**Theorem (flexibly liftable models are compression-sterile).**  Let

`phi_n:G -> U(d_n)`

be asymptotic homomorphisms.  Suppose there are `D_n>=d_n` with

`(D_n-d_n)/d_n -> 0`

and genuine representations `pi_n:G->U(D_n)` such that, after the standard
corner inclusions, `phi_n(g)` is asymptotically equal in normalized
Hilbert--Schmidt norm to `pi_n(g)` on the original corner for every fixed
`g`.  Then the induced tracial-ultraproduct representation `rho` satisfies

`rho(Gamma)' = rho(t)(rho(Gamma)')rho(t)^*`

inside the corresponding matrix tracial ultraproduct for every compressor
`t`.  In particular it cannot satisfy the strict-commutant criterion.

**Proof.**  Adding or deleting `o(d_n)` dimensions changes the normalized
Hilbert--Schmidt class by zero, so the ultraproduct representation is
unitarily equivalent to that represented by the genuine `pi_n`.  Put

`C_n=pi_n(Gamma)'`.

Exact finite-dimensional co-Hopfianity gives

`pi_n(t) C_n pi_n(t)^*=C_n`:

one inclusion follows from `t Gamma t^-1<=Gamma`, and equality follows because
unitarily conjugate finite-dimensional algebras have the same dimension.

Now let `v=(v_n)` commute with `rho(Gamma)`.  Apply the Kazhdan spectral gap
to the adjoint representations on `M_(D_n)` with their normalized
Hilbert--Schmidt norms.  The distance from `v_n` to the exact invariant space
`C_n` tends to zero.  Choose `c_n in C_n` with

`||v_n-c_n||_2 -> 0`.

Since every `pi_n(t)` normalizes `C_n`, both conjugations by `rho(t)` and
`rho(t)^*` preserve the ultraproduct relative commutant.  This proves
equality.  End proof.

Lemma 6.3 and Theorem 6.1 of *Local Hilbert--Schmidt stability* delete exactly
one dimension, with relation defect `O(|w|/sqrt(d_n))`; hence their witness
lies inside the theorem.  The same is true of the original
Becker--Lubotzky instability construction.  They prove failure of
(same-dimension) local stability, but they do **not** produce the
non-stably-finite left--right envelope required here.

Thus the terminal model must fail a substantially stronger property:

> it must remain nonliftable after every asymptotically negligible change of
> dimension.

This is the flexible relative-lifting quadrant represented by
Alekseev--Thom Open Problem 6.2, not the already-established failure of local
HS-stability.

### A strict witness has a quantitative flexible-lifting gap

The preceding qualitative obstruction has a fixed-window version with an
explicit constant.  It is useful because it distinguishes the required
exotic model from an arbitrary failure of stability.

Fix a finite Kazhdan set `S` for `Gamma` and a constant `kappa>0` such that,
for every unitary representation of `Gamma`,

`dist(x,H^Gamma) <= kappa^-1 max_(s in S) ||s x-x||`

for every vector `x`.  Let `t Gamma t^-1<=Gamma`, and fix `gamma in Gamma`.
For a map `phi:G->U(d)` and `v in U(d)` put

`a=max_(s in S)||[v,phi(s)]||_2`,

`b=||[phi(t)v phi(t)^*,phi(gamma)]||_2`.

**Theorem (quantitative flexible-lifting gap).**  If
`pi:G->U(d)` is a genuine representation and

`eta=max_(x in S union {t,gamma})||phi(x)-pi(x)||_2`,

then

`b <= 6 eta + 2(a+2 eta)/kappa`.

Consequently, if `b>=beta` and `a` tends to zero, then every genuine
representation stays at distance at least

`(beta-o(1))/(6+4/kappa)`

from `phi` on the fixed window `S union {t,gamma}`.  The same conclusion
holds after adding `o(d)` dimensions to `phi`: pad both `phi` and `v` by
identities and note that all displayed normalized Hilbert--Schmidt norms are
multiplied by `sqrt(d/D)=1-o(1)`.

**Proof.**  Put `C=pi(Gamma)'`.  In the adjoint representation of `Gamma`,
the Kazhdan estimate gives a contraction `c in C` with

`||v-c||_2 <= (a+2 eta)/kappa`.

The term `2 eta` appears because replacing the two entries in a commutator
with `phi(s)` by `pi(s)` costs at most `2 eta`.  Exact finite-dimensional
co-Hopfianity gives

`pi(t) C pi(t)^*=C`,

so `y_0=pi(t)c pi(t)^*` commutes with `pi(gamma)`.  With
`y=phi(t)v phi(t)^*`,

`||y-y_0||_2 <= 2 eta+(a+2 eta)/kappa`.

Comparing the commutator `[y,phi(gamma)]` with the zero commutator
`[y_0,pi(gamma)]` costs twice this distance and another `2 eta` for the
`gamma`-matrix.  This is exactly the asserted inequality.  End proof.

In particular, a strict ultraproduct witness produces a **uniformly local,
flexible-instability sequence** for the ambient group: one fixed
Kazhdan/compressor/witness window remains a positive distance from every
genuine model even after negligible-dimensional enlargement.  Known local
HS-instability only asserts failure before such enlargement, and therefore
does not meet this quantitative requirement.

### What Alekseev--Thom Open Problem 6.2(a) would still leave open

The exact wording of Alekseev--Thom Open Problem 6.2 is weaker than one
sentence used earlier in this ledger.  Part (a) asks whether, after a
negligible change of dimensions, the relative commutant can be written as

`P=product_U A_n`

for finite-dimensional subalgebras `A_n`.  Part (b) asks whether the `A_n`
can be chosen as exact centralizers of arbitrary lifts of a fixed generating
set.  It does **not** ask that those lifts form genuine representations.

Consequently, a positive answer to (a) does not formally imply normalization
under a compressor.  The missing step would be a tracial co-Hopfian statement
for coordinate ultraproducts of finite-dimensional algebras.  The following
principal-angle calculation identifies the only possible failure of that
step.

Represent the compressor by unitaries `u_n` and let `p_n` be the orthogonal
projection

`L2(M_(d_n)) -> L2(A_n)`.

On `L2(M_(d_n))` put

`V_n(x)=u_n x u_n^*`,  and  `q_n=V_n^* p_n V_n`.

The projections `p_n` and `q_n` have the same finite rank.  In the bounded
tracial ultraproduct, the automatic one-sided commutant inclusion is

`q<=p`.

**Theorem (rank-spiky compensation).**  Assume `P=product_U A_n` and that
`q<p` on `L2` of the bounded tracial ultraproduct.  Then there are a constant
`delta>0` and unit `L2`-vectors

`xi_n in q_n L2(M_(d_n))`

such that

`||(1-p_n)xi_n||_2>=delta`,

but every such choice of vectors has

`||xi_n||_infinity ->_U infinity`.

**Proof.**  Properness supplies a unitary `v=(v_n) in P` whose component in
`p-q` is nonzero.  After passing to an ultrafilter-large set, there is
`delta>0` with

`||(1-q_n)v_n||_2>=delta`,

where `v_n in U(A_n)` and hence `||v_n||_infinity=1`.  Thus the largest
singular value of

`(1-q_n)p_n:p_nH_n -> (1-q_n)H_n`

is at least `delta`.

For two projections of equal finite rank, the nonzero singular values of
`(1-q_n)p_n` and `(1-p_n)q_n` agree: they are the sines of the same principal
angles between `p_nH_n` and `q_nH_n`.  Hence there is a unit vector
`xi_n in q_nH_n` satisfying the displayed lower bound.

If such `xi_n` could be chosen with uniformly bounded operator norm, it would
define an element of the bounded tracial ultraproduct lying in `qH` but not
in `pH`, contradicting `q<=p`.  Therefore its operator norm must diverge
along the ultrafilter.  The same argument applies to every choice with a
fixed positive lower bound.  End proof.

So even coordinatewise liftability of the commutant leaves exactly one
loophole: finite-dimensional rank balance can be paid for by `L2`-unit
vectors concentrated on smaller and smaller matrix support.  Those vectors
are absent from the bounded tracial ultraproduct.  This is the precise
operator-algebraic form of normalized-HS rank blindness at the terminal
certificate.

A useful strengthened target is therefore:

> prove uniform integrability of the principal-angle vectors for the
> compressor and the lifted Kazhdan centralizers.

That statement, together with Open Problem 6.2(a), would force `q=p` and
close the strict-compression route.  Conversely any successful
counterexample must manufacture the displayed operator-norm blow-up while
retaining a bounded unitary witness on the opposite principal-angle side.

### Rank-spiky compensation already occurs for diagonal algebras

There is no dimension-free theorem saying that a one-sided normalized-`L2`
near inclusion between unitarily conjugate finite-dimensional algebras is
automatically symmetric.  The obstruction above is real even for
commutative algebras.

**Theorem (binary-tree asymmetric near inclusion).**  For every `L>=1`
there are two unitarily conjugate diagonal subalgebras `A_L,B_L` of a matrix
algebra with normalized trace such that

`sup_(b in (B_L)_1) dist_2(b,A_L) <= 2/sqrt(L+1)`,

but there is a self-adjoint unitary `a_L in A_L` satisfying

`dist_2(a_L,B_L)=sqrt(L/(L+1))`.

Moreover there is an `L2`-unit vector `xi_L in B_L` with

`E_(A_L)(xi_L)=0`  and  `||xi_L||_infinity=sqrt(L+1)`.

**Proof.**  Let `T_L` be the rooted binary tree with levels `0,...,L`, and
give a vertex `v` at depth `k` the probability

`mu(v)=1/((L+1)2^k)`.

Every level has total mass `1/(L+1)`, so this is a probability measure.  We
construct identically distributed random variables `X,Y` with values in
`T_L`.  If `X` is a non-root vertex, set `Y=parent(X)`.  If `X` is the root,
choose `Y` uniformly among the `2^L` leaves.  The law of `Y` is again `mu`:
the two children of every non-leaf vertex have total mass equal to the mass
of that vertex, while the root mass is redistributed uniformly over the
leaves.

All probabilities are integer multiples of

`1/N_L`,  where  `N_L=(L+1)2^L`.

Thus `X,Y` may be realized on a uniform set of `N_L` points.  Put

`A_L=L_infinity(X)`  and  `B_L=L_infinity(Y)`

inside the diagonal algebra of `M_(N_L)`.  The `X`- and `Y`-atoms have the
same multiset of cardinalities, so a permutation unitary conjugates `A_L`
onto `B_L`.

Let `f` send every non-root vertex to its parent and fix the root.  Then
`Y=f(X)` except on the event `X=root`, of probability `1/(L+1)`.  For every
`b in (B_L)_1`, the element `b(f(X))` lies in `A_L`, and the two functions
differ by at most `2` only on that event.  Hence

`dist_2(b,A_L) <= 2/sqrt(L+1)`.

Choose signs `s(v) in {+1,-1}` so that the two children of every non-leaf
vertex have opposite signs, and set `a_L=s(X)`.  Conditional on every
non-leaf value of `Y`, the variable `X` is uniformly distributed over two
children with opposite signs.  Conditional on a leaf value of `Y`, one has
`X=root`.  Therefore `E_(B_L)(a_L)` vanishes on all non-leaf `Y`-atoms and
has modulus one on the leaves.  Since the non-leaf levels have total mass
`L/(L+1)`,

`||a_L-E_(B_L)(a_L)||_2^2=L/(L+1)`.

Finally choose mean-zero signs on the leaves and define `xi_L(Y)` to be
`sqrt(L+1)` times those signs on the leaf atoms and zero elsewhere.  Its
`L2`-norm is one.  Given `X=root`, its conditional mean is zero, and for
every other value of `X` it vanishes; hence `E_(A_L)(xi_L)=0`.  Its operator
norm is `sqrt(L+1)`.  End proof.

This example exactly realizes the principal-angle pathology.  In the
tracial ultraproduct, the bounded part of `B_L` is contained in the bounded
part of `A_L`, and the inclusion is proper, witnessed by the bounded
unitaries `a_L`.  Equal finite-dimensional ranks are restored in the reverse
direction only by the vectors `xi_L`, whose operator norms diverge.  Thus a
positive answer to Alekseev--Thom Open Problem 6.2(a) would not, on its own,
normalize a compressor.  Any rigidity theorem closing the strict-commutant
route must use the Kazhdan/representation structure of the lifted algebras,
not merely finite dimensionality, conjugacy, or commutativity.

The construction also supplies a useful positive blueprint.  A strict
model should have a long branching tower of `Gamma`-types under pullback by
the compressor.  Only one boundary level should violate the transport
relations, while ambiguity in the inverse pullback accumulates over all
levels.  Exact finite-quotient representations cannot exhibit this tower:
the compressed image equals the original image and the type dynamics is a
permutation.  The missing object is therefore a flexibly nonliftable
approximate representation whose `Gamma`-type Bratteli diagram contains
binary-tree regions of diverging depth.

**Corollary (tree-overlap strictness certificate).**  Let

`phi_n:G -> U(d_n)`

be an asymptotic representation, let `u_n=phi_n(t)`, and suppose that
finite-dimensional algebras `C_n` lift the `Gamma`-relative commutant.  Put

`D_n=u_n^* C_n u_n`.

Assume that, after cutting by central projections whose total trace tends to
one, the overlap of `C_n` and `D_n` contains the binary-tree coupling in the
theorem with depths `L_n -> infinity`; equivalently, there are
self-adjoint unitaries `a_n in C_n` with

`dist_2(a_n,D_n) -> 1`,

while every bounded element of `D_n` has distance `o(1)` from `C_n`.  Then in
the tracial ultraproduct

`P=phi(Gamma)'`

satisfies

`u^* P u < P`,  equivalently  `P < u P u^*`.

Indeed `a=(a_n)` lies in `P` but not in `u^*Pu`; the one-sided near inclusion
puts the bounded ultraproduct of `D_n` inside `P`.  Consequently
`u a u^*` belongs to `uPu^*` but not to `P`.  By the strict-commutant theorem,
after tensoring with a faithful hyperlinear representation if necessary,
this single tree overlap produces a hyperlinear nonsofic image of the
associated free-lamp group.

This does not construct the required `phi_n`.  It reduces model production
to a concrete spectral-combinatorial task: realize a long branching overlap
in the multiplicity/type decomposition of the `Gamma`-centralizer while the
fixed group-relation defect stays on the vanishing boundary level.  A mere
long chain is insufficient: its inverse ambiguity is confined to one level
and has vanishing trace.  Branching is what accumulates order-one reverse
ambiguity from an `o(1)` forward boundary.

### Exact polynomial-elementary restrictions are compression-sterile

The tree certificate cannot be realized by keeping the restriction to the
polynomial elementary subgroup exact.  This follows from representation
rigidity, not merely from residual finiteness.

**Theorem (finite image of finite-dimensional unitary representations).**
Let

`Gamma=EL_r(F_q[x_1,...,x_d])`,  with `r>=3`.

Every finite-dimensional unitary representation of `Gamma` has finite image.

**Proof.**  Choose a finite presentation of `F_q` over its prime field and
write `F_q[x_1,...,x_d]` as a quotient of a polynomial ring

`Z[X_1,...,X_m]`.

Elementary generators lift, so `Gamma` is a quotient of the corresponding
universal lattice `SL_r(Z[X_1,...,X_m])` (equivalently its elementary
subgroup in this range).  Pull a finite-dimensional unitary representation
of `Gamma` back along this quotient.  It is semisimple.  Shenfeld's theorem
on semisimple representations of universal lattices says that, on a
finite-index subgroup, it is a direct sum of tensor products of rational
representations obtained from complex specializations of the variables.

The pulled-back representation kills every elementary matrix `e_ij(pf)`,
where `p=char(F_q)`.  Intersect the finite-index subgroup with the cyclic
constant root subgroup `e_ij(Z)`.  For some `N>=1`, all matrices

`e_ij(k p N)`,  `k in Z`,

belong to that finite-index subgroup and are killed.  Under every complex
specialization these are the points `kpN` of the algebraic root subgroup
`G_a(C)`.  That infinite set is Zariski dense.  Hence the resulting rational
representation is trivial on the entire root subgroup.  This holds for
every root, and the root subgroups generate `SL_r(C)`, so every standard
factor in Shenfeld's description is trivial.  The original representation
is therefore trivial on a finite-index subgroup and has finite image.  End
proof.

The only external input is Daniel K. Shenfeld, *On semisimple
representations of universal lattices*, Groups Geom. Dyn. 4 (2010),
179--193: every semisimple complex representation of
`SL_r(Z[X_1,...,X_m])`, `r>=3`, has the stated standard description on a
finite-index subgroup.

**Theorem (exact-on-`Gamma` microstates are sterile).**  Let

`alpha(gamma)=t gamma t^-1`

be a Kun--Thom compressor.  Suppose maps `phi_n:G->U(d_n)` are asymptotically
multiplicative on the compressor relations and their restrictions

`pi_n=phi_n|_Gamma`

are genuine representations.  Then, in the tracial ultraproduct,

`phi(Gamma)'=phi(t) phi(Gamma)' phi(t)^*`.

In particular these maps cannot satisfy the strict-commutant certificate.

**Proof.**  Put `A_n=pi_n(Gamma)'`.  By the preceding theorem the image of
`pi_n` is finite.  Kun--Thom's finite-quotient argument says that the image
of `alpha(Gamma)` equals the image of `Gamma`: compression inclusion becomes
equality in every finite group.  Consequently

`pi_n(alpha(Gamma))'=A_n`.

Fix a Kazhdan set `S` for `Gamma`.  The compressor relations give

`max_(s in S) ||phi_n(t)pi_n(s)phi_n(t)^*-pi_n(alpha(s))||_2 -> 0`.

The two maps in this display are genuine representations of `Gamma` up to
the displayed unitary conjugacy.  If `a_n` is in the unit ball of `A_n`, its
commutators with the conjugated representation tend uniformly to zero.
The Kazhdan spectral-gap estimate for the adjoint representation therefore
puts `a_n` at `o(1)` distance from

`phi_n(t)A_n phi_n(t)^*`.

Conversely, a unit-ball element of the conjugated algebra has commutators
`o(1)` with `pi_n(alpha(S))`; the same Kazhdan estimate, together with
`pi_n(alpha(Gamma))'=A_n`, puts it at `o(1)` distance from `A_n`.  Thus the
two bounded ultraproduct algebras coincide.  End proof.

The statement persists if `phi_n|_Gamma` is flexibly close to genuine
representations after an `o(d_n)` enlargement, by the same padding and
Kazhdan-pinning argument used above.  Hence a successful tree-overlap model
must already lie in the flexibly nonliftable normalized-Hilbert--Schmidt
quadrant for `Gamma` itself.  Approximation error confined only to the
compressor or the ambient `SL_d(Z)` sector cannot work.

**Corollary (the free-lamp cost is flexible instability of `Gamma`).**  Let
`H_free=G *_Gamma (Gamma x Z)` for the Kun--Thom polynomial/Laurent pair.  If
`H_free` is hyperlinear, then `Gamma` is not flexibly Hilbert--Schmidt stable.
More precisely, a hyperlinear model of `H_free` restricts to an asymptotic
representation of `Gamma` which stays a fixed positive distance, on one
finite window, from every genuine representation after every `o(d_n)`
dimensional enlargement.

**Proof.**  The free generator `z` commutes with `Gamma`.  The nontrivial
free-lamp commutator supplies `tzt^-1` whose commutator with a fixed
`gamma in Gamma minus tGamma t^-1` has positive normalized `L2`-norm.  Thus the
restricted `G`-model satisfies the quantitative strict-witness inequalities
`a_n->0` and `b_n>=beta>0` recorded in the flexible-lifting-gap theorem.
If its restriction to `Gamma` were flexibly close to genuine
representations, the exact-on-`Gamma` sterility theorem (or directly the
same Kazhdan estimate after padding) would force `b_n->0`, a contradiction.
End proof.

Consequently this candidate now has a precise independent price:

`H_free hyperlinear  =>  Gamma flexibly HS-unstable`.

The known failure of local Hilbert--Schmidt stability for infinite
hyperlinear property-`(T)` groups does not pay that price: its standard
delete-one-dimension witnesses become genuine after a negligible enlargement.
The remaining model-production question is exactly whether the polynomial
elementary group admits a **flexibly nonliftable** asymptotic representation
whose centralizer type graph contains the binary-tree overlap above.

### The polynomial subgroup is hyperfinitely Hilbert--Schmidt stable

Let

`R = F_q[x_1,...,x_d]` and `Gamma = EL_r(R)`, with
`r > max{sr(R),2}` (in particular, `r > d+2` is sufficient).  Then `Gamma`
is **hyperfinitely Hilbert--Schmidt stable** in the sense of
Dogon--Vigdorovich, Definition 6.1.

This is a genuine stability theorem for the exact Kun--Thom polynomial
subgroup, although it is strictly weaker than the flexible normalized-HS
stability whose status remains decisive for the free-lamp route.

**Proof.**  We use the general character criterion of Dogon--Vigdorovich,
Theorem 6.2: a finitely generated group is hyperfinitely HS-stable if and
only if each of its von Neumann amenable characters is a pointwise limit of
normalized traces of finite-dimensional representations.

It is enough first to treat an extremal von Neumann amenable character
`chi`.  By Lavi--Levit, Corollary 1.3, there is a normal subgroup
`N normal Gamma` and a finite-dimensional unitary representation `pi` of
`N` such that `chi` is induced from `pi`; in particular `chi(g)=0` for
`g notin N`.  We claim that `Gamma/N` is amenable.

Indeed, form the product character `chi * conjugate(chi)`.  Its GNS algebra
is represented inside the tensor product of the GNS algebra of `chi` with
its opposite, and is therefore amenable.  On `N`, the finite-dimensional
character `tr(pi) * conjugate(tr(pi))` is the character of
`pi tensor conjugate(pi)`.  This representation contains the trivial
representation with positive multiplicity (the identity intertwiner; after
splitting `pi` into irreducibles, use any irreducible summand).  Extending
the resulting invariant character decomposition by zero off `N` shows, as
an identity of positive functionals on `C^*(Gamma)`, that
`chi * conjugate(chi)` dominates a positive multiple of the quotient character

`1_N(g) = 1 if g in N, and 0 otherwise`.

By the noncommutative Radon--Nikodym theorem, the GNS representation
of a positive functional dominated by an amenable tracial functional is a
corner of an amplification of the latter GNS representation.  Consequently
the GNS algebra of `1_N`, namely `L(Gamma/N)`, is amenable.  Thus `Gamma/N`
is amenable.  Since `Gamma` has
property `(T)`, so does its quotient; an amenable discrete property-`(T)`
group is finite.  Hence `[Gamma:N] < infinity`, and the induced
representation `Ind_N^Gamma(pi)` is finite-dimensional; its normalized trace
is `chi` (the conjugation invariance already encoded by `chi` makes the usual
finite-index induced-character average equal to the displayed trace on `N`).
Thus every von Neumann amenable character is itself finite-dimensional.
Dogon--Vigdorovich Theorem 6.2 now proves hyperfinite HS-stability.  End proof.

**Source pins.**

* O. Lavi and A. Levit, *Characters of the group EL_d(R) for a commutative
  Noetherian ring R*, Corollary 1.3: every character in the stable range is
  induced from a finite-dimensional representation of a specified normal
  subgroup.
* A. Dogon and I. Vigdorovich, *Hyperlinearity, stability and asymptotic
  spectral gap of higher rank lattices*, Theorem 6.2 (the theorem itself is
  stated for every finitely generated group, not only lattices).

**Exact consequence for the main route.**  If the Kun--Thom free-lamp group
is hyperlinear, the restriction of a strict model to `Gamma` cannot be both
flexibly liftable (by the preceding finite-image/commutant theorem) and
hyperfinite (by the theorem above, which corrects every hyperfinite
asymptotic representation in the original dimension).  Thus the remaining
certificate is narrower than mere flexible instability:

`a non-hyperfinite, flexibly nonliftable normalized-HS model of Gamma`

whose relative-centralizer overlap is strict.  The ordinary local-HS
instability theorem for infinite hyperlinear property-`(T)` groups does not
provide this: its Theorem 6.1 is non-flexible, and the standard deleted-small-
rank witnesses are flexibly repairable.  Likewise, the unnormalized
Frobenius `[T_2]` calculation above does not decide it because normalized-HS
defect may be `sqrt(dimension)` times smaller.
