# Formalizability by decomposition: structurally reversible words, clean dilations, finite fields

Lane `gk-fz-decompose`, 2026-09-12, family F (formalizability). Supports the Cairn claims
`structurally-reversible-automata-are-formalizable`,
`formalizable-left-inverse-iff-clean-shear-dilation`,
`binary-left-inverse-pairs-extend-over-every-finite-field` and the open claim
`injective-binary-automata-have-formalizable-left-inverses`. It builds on
`research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md`, Section 6.

The question is whether `binary-left-inverse-pairs-are-formalizable` can be proved by decomposing
an automaton into gates that are formal involutions. What follows proves exactly which automata
decomposition reaches, gives an equivalence showing any decomposition with ancillas meets the
same defect as the Bennett form, and shows finite-field points never obstruct.

## 0. Conventions

- `A = F_2^n`. An automaton `tau` on `A^G` has finite memory `M` and local rule `mu: A^M -> A`, with
  `tau(x)(g) = mu((x(gm))_(m in M))`.
- A *representative* of `tau` is a tuple of polynomials over `F_2` in variables `X_(m,i)`
  (`m in M'` for some finite `M'` containing `M`, `i in [n]`) that agrees with `mu` on `{0,1}`-points.
  Composites are computed by substitution, with products of addresses computed in `G`.
- A pair `(tau, sigma)` with `sigma o tau = id` is *formalizable* if some representatives satisfy
  `sigma o tau = id` as a polynomial identity in the variables `X_(h,i)`, `h in G`.
- **Normalization.** Let `c = tau(0)`, a constant configuration. The translation `x -> x + c` is a
  formal involution, and `(tau, sigma)` is formalizable iff `(tau + c, sigma(· + c))` is. So we may
  assume `tau(0) = 0`, and then `sigma(0) = 0`.

## 1. Structurally reversible words are formalizable

**Gates.** On `A^G`:
1. *Track shear.* Fix a coordinate `i`, a finite `M` and a polynomial `f` in the variables
   `X_(m,j)`, `m in M`, `j != i`. Put `E(x)(g)_i = x(g)_i + f((x(gm)_j)_(m, j != i))` and leave the
   other coordinates unchanged.
2. *Sitewise linear map* `L in GL_n(F_2)`.
3. *Constant translation* `x -> x + c`.

**Proposition 1.1.** Each gate is formally invertible: shears and translations are formal
involutions, and `L` has the formal inverse `L^-1`.

*Proof.* A shear changes only coordinate `i`, at every site, and `f` reads no coordinate `i`. So
the second application reads the same inputs, and coordinate `i` becomes
`X_(1,i) + f + f = X_(1,i)` in characteristic 2. The other two cases are linear. QED

**Proposition 1.2 (composition).** If `(tau_1, sigma_1)` and `(tau_2, sigma_2)` are formal pairs,
so is `(tau_2 o tau_1, sigma_1 o sigma_2)`. Substitution is associative.

**Corollary 1.3.** Call `W` *structurally reversible* if it is a finite word in gates. Its reversed
word `W'` satisfies `W' o W = W o W' = id` formally. So every structurally reversible automaton is
bijective and forms a formalizable pair with its inverse, on every group. The sitewise case of
`formal-polynomial-strict-pairs-2026-09-12.md` §6.2 is the special case `M = {1}`: indicator
shears generate `Sym(F_2^n)`.

**Proposition 1.4 (regrouping).** Let `H <= G` have finite index, with right transversal `T`. A
`G`-automaton on `A^G` is an `H`-automaton on `(A^T)^H`, with the same polynomial variables. Suppose
`tau` is structurally reversible over `H`, for gates over `H`. Then the reversed word is a formal
two-sided inverse in the same variables. For the Kaplansky payoff this suffices:
`M_N(F_2[H])` is a unital subring of `M_N(F_2[G])`, so stable finiteness of `F_2[G]` gives direct
finiteness of every `M_N(F_2[H])`, and the linearization theorem applies over `H`.

**Remark 1.5.** A strict automaton is never structurally reversible, since words of bijections are
bijective. Decomposition without ancillas reaches only bijective automata.

## 2. Dilations with ancillas

**Theorem 2.1.** Let `tau` be an automaton on `A^G`. The following are equivalent.
- (a) `tau` has a left-inverse automaton `sigma` such that `(tau, sigma)` is formalizable.
- (b) There are `m >= 0`, a structurally reversible `W` on `(F_2^(n+m))^G` and a representative
  `tau~` of `tau` with `W~(X, 0) = (tau~(X), 0)` as polynomials, where `W~` is the formal word.

*Proof.*
- (a) ⇒ (b). Let `tau~`, `sigma~` be formal representatives. Take `m = n` and `W = P o S o T` with
  `T(x,y) = (x, y + tau~(x))`, `S(x,y) = (x + sigma~(y), y)` and `P` the track swap. Here `T` and
  `S` are products of commuting track shears, and `P` is linear. Then
  `W~(X,0) = (tau~(X), X + sigma~(tau~(X))) = (tau~(X), 0)` formally.
- (b) ⇒ (a). Put `sigma = pi_1 o W^-1 o iota_0`, with representative `sigma~ = pi_1 o W~' o iota_0`,
  where `W~'` is the reversed word.
  - *Functionally.* `W(x,0) = (tau(x),0)` gives `W^-1(tau(x),0) = (x,0)`, so `sigma o tau = id`.
  - *Formally.* `sigma~(tau~(X)) = pi_1 W~'(tau~(X), 0) = pi_1 W~'(W~(X,0)) = pi_1(X,0) = X`.

QED

**Proposition 2.2 (functional dilations always exist).** For every injective `tau` on `A^G` and every
left inverse `sigma`, the word `W = P o S o T` above satisfies `W(x,0) = (tau(x),0)` as functions,
over every group. Its formal ancilla output is `X + sigma~(tau~(X))`, the defect of the pair.

**Consequence 2.3.** Decomposition is never the obstruction.
- Every injective binary automaton is the restriction to the zero-ancilla subshift of a word of
  two track shears and a swap.
- A decomposition yields a formalizable left inverse exactly when its ancillas vanish formally.
- In any such circuit, the step that erases the input from the output track is where the defect
  `X + sigma~(tau~(X))` appears. By Theorem 2.1, a circuit with formally clean ancillas *is* a
  formal pair.
- Changing the circuit only changes which representatives are used.

**Remark 2.4 (Kari-type decompositions).** Decompositions of reversible automata into block
permutations are ancilla-free words of gates over a finite-index sublattice. So by Proposition 1.4
they would make `(tau, tau^-1)` formalizable for every bijective `tau` they cover. We did not verify
the literature statement (Kari 1996, one and two dimensions) from source, so no node relies on it.
It says nothing about strict `tau` (Remark 1.5). Over groups without proper finite-index
subgroups, regrouping is unavailable, and gates must be track shears over `G` itself.

## 3. Finite fields never obstruct

**Theorem 3.1.** Let `(tau, sigma)` be automata on `(F_2^n)^G` with `sigma o tau = id`. For every
`k >= 1` there are automata `tau_k`, `sigma_k` on `(F_(2^k)^n)^G` with the following properties:
- they restrict to `tau` and `sigma` on the Boolean subshift;
- they commute with the sitewise Frobenius `x -> x^2`;
- `sigma_k o tau_k = id`;
- they have the memories of `tau` and `sigma`.

If `tau` is strict, `tau_k` is strict.

*Proof.*
- **Normalize.** Assume `tau(0) = 0` and `sigma(0) = 0` (Section 0). Choose a normal basis
  `beta_j = beta^(2^j)`, `j in Z/k`, of `F_(2^k)` over `F_2`. Its trace-dual basis `gamma_j` is again
  normal, with `gamma_j^2 = gamma_(j+1)`.
- **Slices.** For a configuration `x`, put `x^(j) = Tr(gamma_j x)`, sitewise and coordinatewise, a
  Boolean configuration. Then `x = Sum_j x^(j) beta_j`.
- **Define.** `tau_k(x) = Sum_j tau(x^(j)) beta_j`, and similarly `sigma_k`. These are automata,
  since slicing and recombination are sitewise linear and `tau` has memory `M`.
- **Extension.** For Boolean `x`, `x^(j) = x·Tr(gamma_j)`. So
  `tau_k(x) = tau(x)·Sum_j Tr(gamma_j) beta_j + tau(0)·(...) = tau(x)`.
- **Left inverse.** The slices of `tau_k(x)` are `tau(x^(j))`, because `Tr(gamma_j beta_i) = delta_ij`
  and the values `tau(x^(i))` are Boolean. Hence
  `sigma_k(tau_k(x)) = Sum_j sigma(tau(x^(j))) beta_j = Sum_j x^(j) beta_j = x`.
- **Frobenius.** `(x^2)^(j) = Tr(gamma_(j-1)^2 x^2) = x^(j-1)`, so
  `tau_k(x^2) = Sum_i tau(x^(i)) beta_(i+1) = (Sum_i tau(x^(i)) beta_i)^2`.
- **Strictness.** The image of `tau_k` consists of the configurations whose slices all lie in
  `tau(A^G)`.

QED

**Corollary 3.2.** `(tau, sigma)` is formalizable iff there are `F_2`-polynomial representatives `p`,
`q` of the local rules with `q o p = id` on `F_(2^k)`-points for infinitely many `k`.
- (⇐) A polynomial of degree `d` that vanishes on all `F_(2^k)`-points with `2^k > d` is zero.
- (⇒) is immediate.

By Theorem 3.1, left-inverse extensions over each finite field always exist. So what formality adds
is exactly one polynomial pair, of `k`-independent degree, working for infinitely many `k`. The
slicewise rules read the traces `Tr(gamma_j x)`, of degree `2^(k-1)`. Their degree grows with `k`,
which puts them in the regime where `low-degree-strict-pairs-have-one-sided-linear-parts` gives
nothing. That is an observation about this construction, not a lower bound.

## 4. The open statement, and where it stops

**Open (`injective-binary-automata-have-formalizable-left-inverses`).** Every injective automaton on
`(F_2^n)^G` has *some* left inverse forming a formalizable pair. It is implied by
`binary-left-inverse-pairs-are-formalizable`, which asks this for every left inverse. It already
suffices for `stable-finiteness-forces-binary-surjunctivity`, via
`formal-polynomial-strict-pairs-need-unstable-linearization`. By Theorem 2.1 it is equivalent to:
every injective binary automaton has a structurally reversible dilation with formally clean
ancillas.

**Where decomposition stops.**
- **Bijective words.** Structurally reversible words, over `G` or over a finite-index subgroup,
  give formalizable pairs, but they are bijective.
- **Strict automata.** Strict automata need ancillas. Clean ancillas are formalizability itself.
- **Finite fields.** Finite-field extensions always exist, so the obstruction is uniformity of
  degree over infinite fields.
- **Stably finite hosts.** A strict automaton has no clean dilation on any host with stably finite
  `F_2[G]`, by `formal-polynomial-strict-pairs-need-unstable-linearization`. So a clean dilation of
  a strict automaton would itself be a Kaplansky failure.
- **What remains.** A mechanism must choose representatives, equivalently a circuit, whose formal
  ancilla output vanishes, using more than functional data. No such mechanism is known for any
  automaton that reads more than one cell and is not structurally reversible.
