# Torsion-free host constraints for Gottschalk counterexamples, and the Fournier--Facio group

Lane `gk-n-ff`, 2026-09-12. Supports the Cairn claims
`leavitt-tower-does-not-embed-in-torsion-free-hosts`,
`invariant-output-injective-ca-need-torsion` and
`torsion-free-scalar-df-failure-gives-exotic-idempotents`, and the Attempts of
`fournier-facio-outside-surjunctivity-permanence`.

Throughout, `G` is the Fournier--Facio group of
`fournier-facio-torsion-free-skeleton`. It is finitely presented, torsion-free,
Kazhdan, minimally almost periodic and nonsofic. `G = <Gamma, t_1, t_2>` with
`t_i Gamma t_i^-1 <= Gamma`, and a finitely presented simple torsion-free `S`
sits in the compression defect. Automata follow the house convention
`tau(x)(g) = mu((x(g m))_(m in M))`, with the left shift `(g.x)(p) = x(g^-1 p)`.

The surjunctivity of `G` is not decided here. What is proved is that the
counterexample architectures built so far for the Leavitt tower have no
analogue on a torsion-free host, and exactly what a linear counterexample on `G`
would have to refute first.

## 1. The Leavitt tower does not embed in a torsion-free group

Let `R = L_(F_2)(1,2)` and `u = 1 + s_0 t_1`. Since `t_1 s_0 = 0` and the
characteristic is two,

```text
u^2 = 1 + 2 s_0 t_1 + s_0 (t_1 s_0) t_1 = 1,
```

and `u != 1` because `s_0 t_1` is a nonzero basis monomial. So `R^x` has an
element of order two. Thompson's `V` contains every finite symmetric group, and
each d-ary Leavitt unit group `A^x` over `F_2` contains `R^x`
(`leavitt-surjunctivity-tower`). A torsion-free group contains no element of
finite order other than `1`, so no member of the tower `V <= R^x <= A^x` embeds
in any torsion-free group, and in particular none embeds in `G`.

The host census recorded "no known embedding either way" between `R^x` and `G`.
One direction is now settled. `R^x` does not embed in `G`, so a strict automaton
on `R^x` does not ascend to `G`. Whether `G` embeds in `R^x` stays open; if it
did, a strict automaton on `G` would ascend to `R^x`.

## 2. Invariant output forces a finite symmetry

**Proposition 2.1.** Let `A` be finite with `|A| >= 2`, `H <= G` any subgroup of
any group `G`, and `tau` an injective cellular automaton on `A^G` with

```text
tau(x)(gh) = tau(x)(g)       for all x, all g in G, all h in H.
```

Then `H` is finite.

*Proof.* Let `X = G/H` with the left action and base point `o = H`, whose
stabilizer is `H`. Define `F: A^G -> A^X` by `F(x)(gH) = tau(x)(g)`. This is well
defined because the output is constant on left cosets `gH`, and continuous
because `tau` is. It is equivariant:

```text
F(g'.x)(gH) = tau(g'.x)(g) = (g'.tau(x))(g) = tau(x)(g'^-1 g) = F(x)(g'^-1 g H) = (g'.F(x))(gH).
```

If `H` is infinite, `full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`
makes `F` constant. Then `tau(x)(g) = F(x)(gH)` does not depend on `x`, so `tau`
is constant, and it is not injective since `A^G` has at least two points. QED

**Consequences.**

- On a torsion-free host every nontrivial subgroup is infinite. So no injective
  automaton on a torsion-free group has output invariant under a nontrivial
  subgroup. The architecture of `leavitt-units-carry-injective-invariant-output-automaton`
  has no torsion-free analogue.
- The swap and Klein corner automata (`ternary-leavitt-swap-idempotent-is-full`,
  `projective-ternary-klein-idempotent-is-full`) take output in the range of the
  averaging idempotent of a finite subgroup, so they are invariant-output
  automata. They also have no analogue on `G`.
- With `invariant-output-injective-automata-need-invisible-symmetry`, the symmetry
  of any strict invariant-output automaton is a finite subgroup inside the sofic
  radical of its memory group.

## 3. Scalar linear counterexamples on torsion-free hosts refute the idempotent conjecture

**Proposition 3.1.** Let `k` be a field, `G` a group, and `alpha, beta in k[G]`
with `beta alpha = 1 != alpha beta`. Then `e = alpha beta` is an idempotent,
`e != 0, 1`, and `e(1 - e) = 0` gives zero divisors.

*Proof.* `e^2 = alpha (beta alpha) beta = alpha beta = e`. `e != 1` by hypothesis.
`beta e alpha = (beta alpha)(beta alpha) = 1`, so `e != 0`. Finally `e - e^2 = 0`
with both factors nonzero. QED

**Consequence.** If `G` is torsion-free, the idempotent `e` refutes Kaplansky's
idempotent conjecture for `k[G]` and, through
`kaplansky-three-properties-fixed-fp-torsion-free-tester`, for the fixed
torsion-free tester host over `k`. So a scalar one-sided pair on the
Fournier--Facio group, fed to `stable-finiteness-failure-refutes-surjunctivity`,
would refute the idempotent and zero-divisor conjectures for `G` before it refutes
Gottschalk. By Section 2, no averaging idempotent of a finite subgroup can serve
as the corner: any corner has to be an exotic idempotent. Matrix one-sided pairs
at size `n >= 2` are not constrained by Proposition 3.1. An embedding of `k[G]`
into a division ring would exclude them, but none is known for `G`.

## 4. The certification surface of `G`

`G` is produced existentially. The final small-cancellation quotient is controlled
only on a finite set, and whether `G` has solvable word problem is not established
(`kaplansky-zero-divisor-conjecture`, host note corrected at 93d95df1f). By the
Pi^0_2 dichotomy (`surjunctivity-recognition-dichotomy`), a counterexample
certificate lives in one host. On `G` it would need:

- forward coincidences given by explicit derivations from the relations of `G`.
  This is semi-decidable;
- reverse inequalities certified inside `G` itself, never through a surjunctive
  quotient. Clause (W8) of `fournier-facio-nontrivial-quotients-contain-simple-wreath`
  says every nontrivial homomorphic image of `G` is injective on `S wr Z`. So
  inequalities among elements of the embedded `S wr Z` hold in `G` exactly when
  they hold in `S wr Z`, which has a solvable word problem when `S` does, as for
  Burger--Mozes lattices, which are CAT(0). Inequalities that involve `Gamma` or
  `t_2` have no such certificate available yet.

## 5. Status for `G`, and where each direction stops

- **Negative.**
  - Invariant-output designs and finite-corner linear designs are impossible on
    `G` (Section 2).
  - Scalar linear designs need an exotic idempotent in `F_p[G]` (Section 3).
  - What remains: matrix-size linear designs, and nonlinear designs whose output
    carries no subgroup symmetry. By the design filters on main, such a design's
    forward table must force a nonsofic core, a nonamenable decoder subgroup and
    at least two independent cycles.
  - No candidate is known. The natural source of the nonsofic core is the
    compression of `Gamma` by `t_1, t_2`, with the simple wreath shift
    `S wr Z` (W5) and the binary-tree lamp group (TL1-TL7) as the symmetric
    structure the rules would have to read.
- **Positive.**
  - `G` is surjunctive exactly when every finitely generated subgroup is.
  - The structured subgroups of `G`, namely `S wr Z`, `Gamma x (+)_(k<=0) J_k` (W6)
    and the tree lamp group, are covered by no permanence theorem: `S` is simple
    and infinite, hence not residually finite, so
    `rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive` does not apply.
  - Closure of surjunctivity under finite direct products is itself open.
  - Even surjunctivity of `S` is unknown when `S` is not known to be sofic.
  - `sofic-permanence-closure-omits-simple-fa-nonsofic-groups` bears on `G` only
    through a finitely presented simple nonsofic FA subgroup of `G`, and none is
    recorded. So it is not known whether some iteration of permanence operations
    starting from sofic groups reaches `G`. Nonsoficity alone does not exclude it:
    the Kun--Thom wreaths are nonsofic and inside the closure. The existing
    permanence theorems do not reach `G`
    (Attempts of `fournier-facio-outside-surjunctivity-permanence`).
  - A direct argument would have to handle automata whose memory reads the
    compressed Kazhdan `Gamma`.
