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

**Status (added later the same day).** This statement and `binary-left-inverse-pairs-are-formalizable`
are both refuted over `Z` with one track, by `binary-left-inverse-pairs-need-not-be-formalizable`.
Section 5 records what survives.

**Formerly open (`injective-binary-automata-have-formalizable-left-inverses`).** Every injective automaton on
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

## 5. After the refutation: formalizability depends on the regrouping

**Status.** `binary-left-inverse-pairs-need-not-be-formalizable` (gk-fz-bennett) refutes both open
statements of Section 4 over `Z` with one track: formalizable one-track pairs over bi-orderable
groups are affine translations, and the six-cell marker involution is not affine. I re-derived both
steps of that argument: the two-sided formal inverse, then the degree count in the variable at the
product of the largest window elements. Regrouping gives several tracks, where the degree argument
does not apply, and this section shows regrouping genuinely changes the answer.

### 5.1 Subset-stable marker flips

**Proposition 5.1.** Let `N ⊴ G` have finite index, with right transversal `T`. Let `W ⊂ G \ N` be
finite and `mu: {0,1}^W -> {0,1}`. Put `F(x) = {g : mu((x(gw))_(w in W)) = 1}` and
`tau(x) = x + 1_(F(x))`, and suppose `F(x + 1_S) = F(x)` for every `x` and every `S ⊆ F(x)`. For
`t in T` let `tau_t(x) = x + 1_(F(x) ∩ Nt)`. Then:
- (i) each `tau_t` is a track shear over `N`, on the regrouped alphabet `{0,1}^T` with `y(h)_t = x(ht)`;
- (ii) `tau = tau_(t_k) o ... o tau_(t_1)` for any enumeration of `T`;
- (iii) `tau` is an involution, and `(tau, tau)` is formalizable as `N`-automata.

*Proof.*
- (i) A cell `g = nt` of track `t` reads the cells `gw = ntw`. By normality, `ntw in Nt` iff
  `t w t^-1 in N` iff `w in N`, and `w notin N`. So `tau_t` writes track `t` from other tracks only.
  For `h in N`, `h^-1 g in Nt` iff `g in Nt`, so `tau_t` commutes with left translation by `N`.
  Writing `tw = h'(t,w) t'(t,w)` with `h' in N` and `t' in T`, the rule reads `y(n h')_(t')`, a
  finite memory over `N`.
- (ii) `tau_(t_1)` flips `S_1 = F(x) ∩ Nt_1 ⊆ F(x)`, so the flip set of the new configuration is
  still `F(x)`. Inductively `tau_(t_j)` flips `F(x) ∩ Nt_j`, and the word flips each cell of `F(x)`
  exactly once.
- (iii) With `S = F(x)`, `F(tau x) = F(x)`, so `tau o tau = id`. By (i) and Proposition 1.1, each
  `tau_t` has a representative `X + P_t` that is a formal involution, where `P_t` is a polynomial
  indicator of the marker pattern in variables of other tracks. By Corollary 1.3 and
  Proposition 1.4, `tau~ = tau_(t_k)~ o ... o tau_(t_1)~` and `sigma~ = tau_(t_1)~ o ... o tau_(t_k)~`
  satisfy `sigma~ o tau~ = id` formally. ∎

### 5.2 The marker involution over `4Z`

For the six-cell marker rule over `Z`, the window `W = {±1, ±2, ±3}` avoids `4Z`. Subset stability,
for `S ⊆ F(x)` and a cell `j`:
- **`j in F(x)`.** No cell `i` with `1 <= |i − j| <= 3` lies in `F(x)` (Lemma 2.1 of
  `research/artifacts/binary-formalizability-refutation-2026-09-12.md`). So none lies in `S`, and the
  marker at `j` reads unchanged cells.
- **`j notin F(x)`, no cell of `S` within distance 3.** The marker at `j` reads unchanged cells.
- **`j notin F(x)`, some `i in S` with `1 <= |j − i| <= 3`.** By the table of Lemma 2.1, the marker at
  `j` needs a `0` at `i − 1` or `i + 1`, where `x` has a `1` because `i in F(x)`. Those cells are at
  distance 1 from `i in F(x)`, so they are not in `F(x)` and not in `S`. The marker at `j` stays false.

So the marker involution is the word `tau_3 o tau_2 o tau_1 o tau_0` of four track shears over `4Z`,
and `(tau, tau)` is formalizable as `4Z`-automata. The representative `tau~` assigns different
polynomials to the four tracks, because the shears apply in order. So it is `4Z`-equivariant but
not `Z`-equivariant, as Theorem A of the refutation artifact requires. The hypothesis `W ∩ N = ∅`
fails for `2Z` and `3Z`, and nothing here decides those subgroups.

### 5.3 Over `Q` no regrouping helps

**Proposition 5.3.** Let `tau` be the six-cell marker rule on `{0,1}^Q`, with memory in `Z ⊂ Q`.
Then `tau` is a bijective involution. For every finite-index subgroup `H <= Q`, no representatives
make `(tau, tau)` formal as `H`-automata, and `tau` is its own unique left inverse.

*Proof.*
- **No regrouping.** `Q` is divisible, so a finite quotient `Q/H` of order `n` is divisible, and every
  class is `n` times a class, which is `0`. So `H = Q`, with one track.
- **Involution.** `tau` acts on each coset `q + Z` as the marker involution over `Z`.
- **Not affine.** `Q` is bi-orderable, so by `formalizable-binary-pairs-over-biorderable-groups-are-affine`
  a formal pair would give `tau(x)(g) = x(g + m) + eps`. `tau` fixes the configuration with a single
  `1` at `0`, since every marker needs two `1`s. That forces `m = 0` and `eps = 0`, so `tau = id`.
  But `tau` changes the configuration that is `1` exactly at `−1` and `1`. ∎

So "formalizable after regrouping along some finite-index subgroup" is false in general. The payoff
route therefore localizes first:
- An automaton with memory in the finitely generated subgroup `Γ` acts coset by coset on
  `A^G = ∏_(gΓ) A^(gΓ)`, as a copy of the same rule over `Γ`. So injectivity and surjectivity are
  decided over `Γ`.
- Stable finiteness of `F_2[G]` passes to `F_2[H]` for every `H <= Γ`, since matrix rings over
  `F_2[H]` are unital subrings of those over `F_2[G]`.

### 5.4 The surviving statement

**Open (`injective-automata-over-fg-groups-are-virtually-formalizable`).** Let `Γ` be finitely
generated. Every injective automaton on `(F_2^n)^Γ` has a left inverse `sigma` and a finite-index
`H <= Γ` such that the pair is formalizable as `H`-automata. With
`formal-polynomial-strict-pairs-need-unstable-linearization`, this gives
`stable-finiteness-forces-binary-surjunctivity`, through the route
`virtual-formalizability-reduces-surjunctivity-to-kaplansky`.

- **Block permutations.** A block permutation along the translates of a fundamental domain `B` of
  `bZ^d` is a word of track shears over `bZ^d`.
  - Each block meets every residue class once.
  - A permutation of `{0,1}^B` is a product of hypercube-edge transpositions, and each of those is an
    indicator shear reading the other cells of its block.
  - Translations are formal.
  So a decomposition of the reversible automata over `Z^d` into block permutations and translations
  would give the statement for them. Kari's theorems for `d = 1, 2` are recalled, not read from
  source, so no node depends on them.
- **Groups without finite-index subgroups.** There `H = Γ`, and the automaton keeps its `n` tracks.
  The one-track classification never applies to a nontrivial finitely generated perfect group:
  - A finitely generated bi-orderable group has a maximal proper convex subgroup, because the
    finitely many generators cannot all lie in a union of a chain of proper convex subgroups.
  - That subgroup is normal, since conjugation maps it to a proper convex subgroup.
  - Its quotient is Archimedean, hence embeds in `R` by Hölder's theorem, so the group maps onto `Z`.
  So on `R^x` and on finitely generated simple hosts, no one-track classification constrains the
  statement.
- **Strict automata.** On a host with stably finite `F_2[Γ]`, a strict automaton has no formal pair
  after any regrouping. A proof of the statement must produce Kaplansky failures from strict
  automata.
- **Where it stops.** Every formal pair known after regrouping is a gate word, hence bijective. No
  mechanism produces formal representatives for a strict automaton.
