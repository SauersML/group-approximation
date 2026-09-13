
## 3. Zero margin

**Proposition 3.1.** For every group `G`, surjunctivity is equivalent to the case `j' <= j` of QS. That is, for
all `B`, proper `Y <= B^G`, `D`, `n >= 1` and `j >= j' >= 0`, no injective automaton maps `(B^n x D^j)^G` into
`Y^n x (D^(j'))^G`.

**Proof.**
- **The case gives surjunctivity.** If `tau` on `B^G` is injective and not onto, its image `Y` is a proper
  subshift, and `tau` is a map of the excluded kind with `n = 1` and `j = j' = 0`.
- **Surjunctivity gives the case.** Let `Phi` be such a map. Follow it by an injective symbol map
  `D^(j') -> D^j` on the last track. The composite is an injective automaton on `(B^n x D^j)^G` whose first
  track lies in `Y`, so it is not onto. QED.

**Remarks.**
- **One pattern suffices.** Every proper `Y` lies in the subshift `Y_r` avoiding one pattern `r` that `Y` misses,
  and a constant for `Y_r` is one for `Y`.
- **What QS adds.** For `|D| >= 2`, Proposition 3.1 forces `(j' - j) log|D| >= log 2` for every map of this shape.
  That margin is bounded below independently of `n`. QS asks for a margin growing linearly in `n`.

**Where the margin comes from in Theorem Q.**
- The fibre device over `G x K` stores the input on the `epsilon |V|` bad points of a sofic model `V` of `K`.
  That stored input is the extra full-shift track, against a number of copies of `Y` proportional to `|V|`.
- When `K` has exact finite models there are no bad points and `j' = j`. Proposition 3.1 then closes the
  argument, which is the content of `products-with-lef-permanence-closure-factors-are-surjunctive`.
- So QS is needed exactly to absorb the sofic error rate. Since `epsilon` can be taken as small as wanted, any
  positive `delta_Y` suffices.

## 4. Routes that die

### 4.1 Compactness and ultraproducts

Suppose `G` is surjunctive and `Y` has no QS constant. Then there are injective automata `Phi_i` from
`(B^(n_i) x D_i^(j_i))^G` into `Y^(n_i) x (D_i^(j'_i))^G` with margins `m_i = (j'_i - j_i) log|D_i|` and
`m_i / n_i -> 0`.
- **`n_i -> infinity`.** By Proposition 3.1 each `m_i >= log 2`. If `n_i` stayed bounded along a subsequence,
  `m_i / n_i` would stay bounded below.
- **No limit automaton.** The alphabets grow without bound, so a limit is not an automaton over a finite
  alphabet.
- **The limit statement is true.** A limit with infinitely many tracks has the form of an injective equivariant
  map `(B^N)^G -> Y^N`. Such maps exist over every group.
  - Take `B = {0, 1, 2}` and `Y = {0,1}^G`, a proper subshift.
  - Encode each symbol of `B` as two bits and send track `i` to tracks `2i` and `2i + 1`.
  - The map is injective, equivariant and coordinatewise.
- **Where it stops.** No contradiction can come from the limit, so any proof must keep `n` finite and
  quantitative.

### 4.2 Amplification

- **Products.** The `m`-fold product of `Phi` has parameters `(m n, m j, m j')` and the same ratio.
- **Composition.** A second map of the same shape, from `(B^n x D^(j'))^G` into `Y^n x (D^(j''))^G`, restricts to
  the image of `Phi`. The composite keeps `n` and adds the margins.
- **Where it stops.** Neither operation turns a small positive ratio into a nonpositive margin, which is all that
  surjunctivity forbids.

### 4.3 Recoding the output

A contradiction with surjunctivity needs an injective automaton `Psi` from the image of `Phi` into a full shift
`C^G` with `|C| < |B|^n |D|^j`.
- **A recoding of the whole target fails in the residue.** If `Y` contains all constant configurations,
  `Y^n x (D^(j'))^G` has `|B|^n |D|^(j')` of them, and `Psi` must be injective on them. So `|C| >= |B|^n |D|^(j')`,
  which exceeds `|B|^n |D|^j` when `j' > j`. Over `Z` this is the periodic-point condition of Krieger's
  embedding theorem.
- **A recoding of the image alone is circular.** The image of `Phi` is conjugate to the source full shift. So
  `Psi` exists exactly when an injective automaton maps `(B^n x D^j)^G` into a smaller full shift, which is
  what surjunctivity already forbids.

### 4.4 Logic

- **Certificates.**
  - An injective automaton has a left inverse automaton.
  - The condition "every `Y`-track of the image avoids `r`" is a finite condition on the local rule.
  - So a failure of QS for `Y_r` at ratio below `delta` is certified by a finite piece of the multiplication
    table of `G`, two local rules on a ball, the identity `sigma Phi = id` on that ball, and the avoidance of `r`.
- **Clauses.** Surjunctivity forbids the certificates of ratio `<= 0` (Proposition 3.1), a set of rectangle
  clauses. QS for `Y_r` says that for some `delta` all certificates of ratio below `delta` are forbidden, and the
  set of clauses depends on the unknown `delta`.
- **Where it stops.** A derivation would have to turn a certificate of small positive ratio into one of ratio
  `<= 0` on a larger ball, which is the recoding of Section 4.3. Compactness over the clauses gives
  certificates of vanishing ratio on growing balls, which is Section 4.1.

### 4.5 Counting on amenable Schreier graphs

Section 2 counts configurations invariant under normal subgroups. Theorem A applies to every subgroup `H`.
`Phi` restricts to an injective graph automaton on the Schreier graph `S` of `H`, with a left inverse (Theorem
A(2)).
- **The count.** Let `S` have Følner sets `F_k`.
  - The input on the interior of `F_k` is determined by the output on `F_k`.
  - An output track avoids the image of `r` on every window `vW` at which `W` maps injectively.
  - If those vertices have density at least `c_W > 0` in the `F_k`, the argument of Corollary 2.4 gives the
    constant `-c_W log(1 - |B|^(-|W|)) / |W|^2` for `Y_r`.
- **It reaches only sofic groups.**
  - Take `W = {1, s}` with `s != 1`. Positive density of `W`-injective vertices says that `s` moves a fraction
    at least `c_W` of the vertices of `F_k`.
  - Restricting the action to `F_k` and patching the boundary gives almost-actions of `G` whose fixed-point
    fractions stay below `1 - c_W + o(1)`.
  - Tensor powers push these fractions to `0`. So `G` is sofic, where the constant is already known.
- **Where it stops.** For a nonsofic `G`, every amenable Schreier graph has density `0` for some `W`, and the
  count gives nothing.

## 5. The equivalences asked about

**Proposition 5.1.**
1. For finite `F`, `G x F` is surjunctive iff `G` is.
2. If `G` is surjunctive, so is `G x Z`.

So neither "`G x F` surjunctive for all finite `F`" nor "`G x Z` surjunctive" is equivalent to QS, unless every
surjunctive group is QS, which is the target.

**Proof.**
1. An automaton over `G x F` on `A^(G x F)` is an automaton over `G` on `(A^F)^G`, with memory the projection
   of the old one. Conversely `G` is a subgroup of `G x F`, and surjunctivity passes to subgroups by induction of
   automata.
2. `Z` is LEF, and `products-with-lef-permanence-closure-factors-are-surjunctive` puts every LEF group in
   `{K : G x K surjunctive}`.
3. Both properties are equivalent to surjunctivity, and QS implies surjunctivity. So an equivalence of either
   with QS says that every surjunctive group is QS. QED.

**The candidate "QS iff `G x K` is surjunctive for every sofic `K`".**
- **Forward.** This is Theorem Q.
- **Converse.** It needs a construction from maps over `G` with small positive margin to strict automata over
  `G x K`, the reverse of the fibre device. None is known. Its `K` could not lie in the LEF permanence closure,
  since those products are surjunctive for every surjunctive `G`.
- **Relation to the target.**
  - If the target holds, so does the equivalence: `G x K` surjunctive makes the subgroup `G` surjunctive, hence QS.
  - If the equivalence holds, the target is equivalent to `products-with-a-sofic-factor-are-surjunctive`.

**No refutation.** A counterexample to the target needs a surjunctive nonsofic group and a proper subshift in
its residue with no constant. Section 4 gives no mechanism producing maps of vanishing ratio over any group, so
no candidate is at hand.
