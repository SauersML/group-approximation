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
  `non-surjunctive-group-with-stably-finite-group-algebras`. Section 6 shows why no such invariant
  exists: the defect depends on representatives.

## 5. Decoders with disjoint encoder footprints

Use reduced representatives over `F_q`: every exponent below `q`, which makes them unique.
- **Encoder.** Rules `mu_j` with essential footprints `F_j ⊆ M`, the variables occurring in `mu_j`.
- **Decoder.** Rules `nu_i` in the variables `Y_(s,j)`.

**Theorem 5.** Suppose `sigma o tau = id` and condition (DF) holds: every monomial of every `nu_i` is
multilinear in the `Y`-variables, and distinct variables `Y_(s,j)`, `Y_(s',j')` in a common monomial
satisfy `s F_j ∩ s' F_(j') = ∅`. Then the identity is formal for these representatives. So if
`M_n(F_q[G])` is directly finite, `tau` is bijective.

*Proof.*
- At `g` a monomial `c prod_((s,j) in T) Y_(s,j)` becomes `c prod mu_j((X_(gsm))_(m in F_j))`.
- The sets `g s F_j` are pairwise disjoint, so the product of these reduced factors is reduced, and
  so is the sum over monomials.
- Each coordinate of the composite is therefore a reduced polynomial equal to `X_(g,i)` on
  `F_q`-points, hence equal to `X_(g,i)`.
- Theorem 1 finishes. QED

**Corollaries.**
- **Affine decoders.** They satisfy (DF). A strict automaton with an affine left-inverse automaton
  is a matrix Kaplansky pair.
- **Stably finite hosts.** On a host with stably finite `F_p[G]`, a strict pair over `F_q^n` needs a
  decoder monomial multiplying two encoder outputs that read a common essential cell (or a power,
  when `q > 2`). Over `F_2` this is a nonlinear decoder term at a forward coincidence read by both
  encoder copies. This sharpens the table-level coincidence filters.

**Relation to gk-n-highalpha** (`low-degree-strict-pairs-have-one-sided-linear-parts`, landed 12:55;
`unipotent-automata-over-finite-fields-are-surjective` and
`low-degree-strict-automata-force-matrix-kaplansky-failure`, established 13:05):
- `deg sigma * deg tau < q` is another sufficient condition for formality, since no exponent reaches `q`.
- Theorem 1 at that bound gives both of those conclusions (formal identity plus directly finite
  matrix algebra gives bijectivity), with a different injectivity argument.
- Over `F_2` the degree bound forces both rules linear, while Theorem 5 covers decoders of every degree.

## 6. The multilinear defect is not an invariant; formalizability is

### 6.1 Calibration: a sitewise reversible pair with nonzero canonical defect

Over `F_2^3` with coordinates `(a,b,c)`, take the Toffoli gates `T_1(a,b,c) = (a, b, c + ab)` and
`T_2(a,b,c) = (a + bc, b, c)`, and put `tau = T_2 T_1`, `sigma = T_1 T_2`. These are inverse
bijections, acting sitewise on `(F_2^3)^G` for any `G`.

**Multilinear representatives.** `tau = (a + ab + bc, b, c + ab)` and
`sigma = (a + bc, b, c + ab + bc)`.

**Formal composite.** Substituting into `sigma = (y_1 + y_2 y_3, y_2, y_3 + y_1 y_2 + y_2 y_3)` gives
`(a + ab + ab^2, b, c + bc + b^2 c)`. This is the identity on `{0,1}`-points but not formally.

**At `c = (1,0,0)`.**
- `tau(c) = c`.
- `J_tau(c) = [[1,1,0],[0,1,0],[0,1,1]]`.
- `J_sigma(c) = [[1,0,0],[0,1,0],[0,1,1]]`.
- `J_sigma(tau(c)) J_tau(c) = I + e_12`, so `D(c) = e_12 ≠ 0`. Both Jacobians are invertible, and the
  pair is bijective on every group, including groups with stably finite group algebras.

**Unreduced representatives.** `(a + bc + ab^2, b, c + ab)` and `(a + bc, b, c + ab + b^2 c)` compose
formally to the identity, so the pair is formalizable.

### 6.2 What is intrinsic

- **Linear parts are not invariants.** Replacing a rule `mu_j` by `mu_j + (X_h^2 - X_h) P` changes
  `J_tau(c)` at a Boolean constant configuration by `P(c)` at `h` (characteristic 2), arbitrarily.
  So `J_tau(c)`, `J_sigma(c)` and `D(c)` are invariants of the representatives, not of the automata.
  The underlying reason is in `boolean-secants-do-not-supply-operator-left-inverses`: the Boolean
  function algebra has no Kähler differentials.
- **Formalizability is.** A pair is *formalizable* if some representatives satisfy `sigma o tau = id`
  formally, possibly after enlarging the memories.
- **Sitewise pairs over `F_2^n` are formalizable, on every group.**
  - A shear `x_i -> x_i + f(other coordinates)` is a formal involution in characteristic 2.
  - Shears with `f` the indicator of one point realize the transpositions along hypercube edges.
  - These generate `Sym(F_2^n)`, because the hypercube is connected.
  - So a permutation `tau` is a composite of shears. The reverse composite is `sigma`, and the
    identity is formal.
- **Theorem 1 restated.** Formalizable strict pairs are matrix Kaplansky pairs.

### 6.3 The Bennett form of a strict pair

Let `A = F_2^n`, and put:
- `T(x,y) = (x, y + tau(x))`;
- `S(x,y) = (x + sigma(y), y)`;
- `P` the track swap;
- `V = P o S o T` on `(A^2)^G`.

**Properties of `V`.**
- **Formally invertible, whatever the representatives.** `T o T = id` and `S o S = id` formally.
- **Formula on `X_0`.** `V(x,0) = (tau(x), x + sigma(tau(x)))`. Functionally this is `(tau(x), 0)`.
  So `V` maps the linear subspace `X_0 = A^G x 0` into itself, it restricts to `tau` there, and
  `tau` is strict iff `V(X_0) ⊊ X_0`.
- **Where the collapse enters.** Only in this invariance of `X_0`.

**Linearization.** Normalize `tau(0) = 0` and put `a = J_tau(0)`, `b = J_sigma(0)`, `ba = 1 + D`.
Then `J_(S o T)(0) = [[1,b],[0,1]] [[1,0],[a,1]] = [[D, b],[a, 1]]`, and
`J_V(0) = [[a, 1],[D, b]]`, which lies in `GL_(2n)(F_2[G])`. The defect `D` is exactly how far the
invertible linearization is from preserving `X_0`.

### 6.4 Open: are strict pairs formalizable?

Recorded as `binary-left-inverse-pairs-are-formalizable`. If every pair of automata on
`(F_2^n)^G` with `sigma o tau = id` is formalizable for every `G`, then Theorem 1 makes every group
with stably finite `F_2[G]` surjunctive over alphabets of size `2^n`. Injective automata over finite
alphabets have left-inverse automata, by compactness.
- **Sitewise pairs:** formalizable (6.2).
- **Canonical representatives:** the wrong ones (6.1).
- **Where it stops.** In the Bennett form, formalizability asks for representatives in which `V`
  preserves `X_0` formally. Changing representatives feeds the defect through `J_sigma(tau)`
  applied to ideal elements, an equivariant finite-memory solvability problem inside the ideal
  `(X_h^2 - X_h)`. No argument is known on any group with nontrivial memory.

**Update (13:55).** Over bi-orderable groups a formalizable one-track binary pair is a shift plus a
constant (`binary-left-inverse-pairs-need-not-be-formalizable`, gk-fz-bennett). So the claim above
is false, and the live target is `injective-binary-automata-are-stably-formalizable` (identity
ancilla tracks).

### 6.5 The marker involution: regrouping, ancillas, specializations

Let `tau(x)_i = x_i + m_i(x)` with `m_i(x) = [x_(i-3..i+3) = 001*100]`. It is an involution:
markers within distance 3 exclude each other, so flipping any subset of the marker set changes no
marker.

**Regrouping along `4Z` formalizes it.**
- Let `S_r` flip the cells `4k+r` at markers.
- `m_i` reads offsets `±1, ±2, ±3`, none congruent to 0 mod 4, so each `S_r` reads only other tracks
  of the regrouped configuration. It is a track shear and a formal involution.
- Since subset flips preserve markers, `S_3 S_2 S_1 S_0 = tau`, and the reversed word is a formal
  inverse (`marker-involution-is-formalizable-after-regrouping`).
- Consequences:
  - Formalizability is not invariant under regrouping.
  - Regrouping along a finite-index subgroup is a stabilization that keeps the Kaplansky payoff,
    because stable finiteness passes to finite-index subgroups.
  - The target hosts are finitely generated simple groups, which have no proper finite-index
    subgroups, so there only ancillas are available.

**One ancilla with `Z`-equivariance: where the obvious word stops.**
- Let `A : y -> y + m(x)` and `B : x -> x + y`, both track shears. Applying `A`, `B`, `A`, `B` in
  that order gives `(x + m(x + y + m(x)), y + m(x) + m(x + y + m(x)))`.
- This is `tau x id` exactly when `m(x + y + m(x)) = m(x)`, for instance at `y = 0`, but not for
  every `y`. The dirty-ancilla trick needs the controls unchanged while the targets change.
- In one track with translation symmetry, controls and targets are the same cells. Regrouping
  separates them by residue, and no `Z`-equivariant separation is known.

**Specializations give no invariant.**
- Substituting `Y = 0` turns a formal automorphism realizing `tau x id` into a two-output formal
  identity `nu_1(mu_1(X,0), mu_2(X,0)) = X`, where the extreme variable can cancel.
- Diagonal (constant) specialization gives the identity on `F_2^2`.
- Periodic specialization gives finite-group equivariant automorphisms. Those are flexible: over
  `Z/2` with two tracks, the controlled affine map `a -> (I + cM) a + c v` with `c = b_0 b_1`,
  `M = [[1,1],[1,1]]`, `v = (1,1)` is a formal involution inducing an odd permutation.
- A negative answer needs an invariant that sees translation symmetry with simultaneous updates.
  It cannot live in the graded `I`-adic layers: with an encoder representative whose reduced
  Jacobian is `I` at every Boolean point, the corrections always exist Boolean-adically
  (`binary-left-inverse-pairs-are-boolean-adically-formalizable`). So it must measure the growth in
  degree or memory of the corrections, and a positive theorem must bound that growth.
