# Formal left-inverse identities force bijectivity once the linearization is directly finite

Lane `gk-free-neg`, 2026-09-12. Supports `formal-polynomial-strict-pairs-need-unstable-linearization`
and its proof route, and the corollaries recorded beside it.

## 0. Approach declared by this lane

**The arithmetic of the alphabet.** Every counterexample design family on main is either
combinatorial or linear:
- combinatorial: product tables, routing, invariant outputs, defect windows, network coding;
- linear: one-sided inverses in group algebras and their lifts.

None of them asks how the arithmetic of a finite alphabet enters the left-inverse identity. Over an
alphabet `F_q^n` every local rule is a polynomial map, and `sigma o tau = id` is an identity of
functions on `F_q`-points. Such an identity either already holds as a polynomial identity
(*formally*), or it needs the collapse `x^q = x`.

Theorem 1 shows the formal case adds nothing beyond Kaplansky: a formally left-invertible strict pair
has a linearization with a one-sided inverse that is not two-sided. So on any group whose prime-field
group algebras are stably finite, a nonlinear counterexample must use the collapse essentially. This
is a screen for every nonlinear design, and it names what a counterexample has to exploit.

## 1. Setting

Let `k` be a field, `n >= 1`, `A = k^n`. For finite `k` this is a finite alphabet. For infinite `k`
it is the algebraic setting.
- **Automata.** A polynomial automaton `tau` has a finite memory `M` containing `1` and a vector
  `mu` of polynomials in the variables `X_(m,i)`, `m in M`, `i <= n`. It acts by
  `tau(x)(g) = mu((x(gm))_m)`. Over a finite field every rule has such a representative, and the
  representative is part of the data.
- **Formal composite.** Given `sigma = (S, nu)`, the formal composite `sigma o tau` is obtained by
  substituting `mu((X_(gsm))_m)` into `nu`. Its variables are `X_(h,i)`, `h in G`, and products are
  computed in `G`, so two variables coincide exactly when the products coincide.
- **Formal identity.** `sigma o tau = id` formally means each coordinate of the composite at `g`
  equals `X_(g,i)` in the polynomial ring `k[X_(h,i)]`. A formal identity implies the functional
  one; the converse fails over finite fields.
- **Linear automata.** A linear automaton is `L_a(x)(g) = sum_m a_m x(gm)` with
  `a = sum_m a_m delta_m in M_n(k[G])`. Then `L_b o L_a = L_(ba)`, and `L_a = id` iff `a = 1`.
- **Linearization.** At a constant configuration `c` with constant value `c in A`, the linearization
  is `J_tau(c) = sum_m (d mu / d X_m)(c) delta_m in M_n(k[G])`. The chain rule for formal
  composites reads `J_(sigma o tau)(c) = J_sigma(tau(c)) J_tau(c)`.

## 2. Theorem 1 and proof

**Theorem 1.** Let `tau`, `sigma` be polynomial automata on `(k^n)^G` with
`sigma o tau = id` formally. If `M_n(k[G])` is directly finite, then `tau o sigma = id` formally. In
particular `tau` and `sigma` are mutually inverse bijections of `(k^n)^G`.

*Proof.*

**Step 0: translation.** Put `d = tau(0)`, a constant configuration. Constant translations
`T_v(x) = x + v` are formally invertible automata. Replace `tau` by `T_(-d) o tau` and `sigma` by
`sigma o T_d`. The formal identity is preserved, and `tau o sigma = id` formally is equivalent for the
two pairs. Now `tau(0) = 0`, and `sigma(0) = sigma(tau(0)) = 0`.

**Step 1: linear parts compose.** Let `I` be the ideal of all variables. Write `tau = L_tau + N_tau`
coordinatewise, with `L_tau` linear and `N_tau in I^2`, and the same for `sigma`. Then
`sigma o tau == L_sigma o L_tau mod I^2`. So the formal identity gives `J_sigma(0) J_tau(0) = 1` in
`M_n(k[G])`.

**Step 2: direct finiteness.** Hence `J_tau(0) J_sigma(0) = 1`, and `a = J_tau(0)` is invertible in
`M_n(k[G])` with finitely supported inverse.

**Step 3: finite-memory formal maps.**
- **The class.** Let `P` be the set of equivariant families `phi(X)(g)` of `n`-tuples of formal
  power series without constant term. For each degree `j` the homogeneous degree-`j` part must read
  only the variables `X_(gu)`, `u` in a finite set `U_j` independent of `g`. Every polynomial
  automaton fixing `0` lies in `P`.
- **Composition.** The degree-`j` part of `phi o psi` uses only the parts of degree at most `j` of
  `phi` and `psi`, and only finitely many terms. So composition is well defined and associative, and
  `P` is a monoid.
- **Lemma.** If `phi in P` has invertible linear part `L_phi = L_a`, `a in M_n(k[G])^x`, then `phi`
  is a unit of `P`.
  - *Tangent-to-identity form.* `phi = L_a o (id + Q)` with `Q = L_(a^-1) o N_phi`, which has order
    at least 2.
  - *Right inverse.* Define `psi` degree by degree through `psi = id - Q o psi`. Because `Q` has order
    at least 2, the degree-`j` part of `Q o psi` involves only parts of `psi` of degree below `j`. So
    the recursion determines `psi` uniquely, with finite memory in each degree, and
    `(id + Q) o psi = id`.
  - *Two-sided.* The same construction gives `psi` a right inverse `chi`. Then
    `id + Q = (id + Q) o psi o chi = chi`, so `psi` is a two-sided inverse.
  - *Conclusion.* `phi^(-1) = psi o L_(a^-1)` lies in `P`.

**Step 4: uniqueness.** By Step 2 and the Lemma, `tau` has a two-sided inverse `psi in P`. So
`sigma = sigma o (tau o psi) = (sigma o tau) o psi = psi`, and `tau o sigma = tau o psi = id` in `P`.
Both sides are polynomial, so the identity holds in the polynomial ring. Evaluating on
configurations gives `tau o sigma = id`. With `sigma o tau = id`, `tau` is bijective. QED

**Scope.** The hypothesis is a formal identity for *some* polynomial representatives of the two rules.
Over a finite field a functional identity need not be formal for any choice of representatives. The
theorem says nothing about such pairs. Section 4 is about them.

## 3. Corollaries

**Corollary 2: infinite fields.** Let `k` be infinite, with `sigma o tau = id` on all configurations of
`(k^n)^G`. Each coordinate of the composite is a polynomial in finitely many variables that vanishes
on all `k`-points, so it is zero. The identity is therefore formal, and Theorem 1 applies:
- if `M_n(k[G])` is directly finite, `tau` is bijective;
- in characteristic `p > 0`, a strict polynomial pair over an infinite field gives a one-sided inverse
  pair in `M_n(k[G])`, which by the prime-field reduction of stable finiteness means `F_p[G]` is not
  stably finite;
- in characteristic 0, `k[G]` is stably finite for every group (Kaplansky), so a polynomial automaton
  over a field of characteristic 0 that admits a polynomial left-inverse automaton is bijective, for
  every group.

**Corollary 3: specialization.** A design whose rules and formal identity have coefficients in `F_p[t]`
or another finitely generated ring specializes to each finite residue field with the identity still
formal. The specializations are bijective over every group whose matrix group algebras over that
residue field are directly finite. So designs built over infinite fields and then specialized produce
no counterexample on such groups.

**Screen.** On a group whose `F_p[G]` is stably finite for the alphabet's characteristic, the
following are bijective:
- shears `x -> x + f(other tracks)`;
- triangular circuits and Nagata-type designs;
- every design whose left-inverse identity is formal for some representatives.

A strict pair on such a group must use `x^q = x` in `sigma o tau = id`. This complements:
- `triangular-forward-tables-force-surjectivity`, a condition on product coincidences;
- `invariant-output-automata-have-only-nonlinear-decoders`, a linear-decoder exclusion;
- the certificate-linear decoders, automata linear in the data.

## 4. Collapse-essential pairs (open, where this lane goes next)

Take `q = 2` and multilinear representatives. Then `sigma o tau - id = sum_h (X_h^2 - X_h) P_h`
coordinatewise, for polynomials `P_h`.
- **Where squares arise.** A square `X_h^2` appears only where the composite reads one cell `h` along
  two different paths, `g s m = g s' m'` with `(s, m) != (s', m')`, that is, at a forward
  coincidence. So the collapse terms sit on the forward table.
- **Defect at a constant configuration.** Linearizing at a constant configuration `c in F_2^n`, and
  using `d(X^2 - X)/dX = 1` in characteristic 2 with `c^2 = c`, gives
  `J_sigma(tau(c)) J_tau(c) = 1 + D(c)` with `D(c) = sum_h P_h(c) delta_h in M_n(F_2[G])`.
  A strict pair on a group with directly finite `M_n(F_2[G])` therefore needs a nonzero collapse
  polynomial.
- **Where it stops.** No invariant is known that forces the collapse defect to vanish, and no
  collapse-essential strict pair has been constructed on any group. Recorded as the open claim
  `non-surjunctive-group-with-stably-finite-group-algebras`.
