# Universal directly finite and MF reflections of zero-dimensional dynamics

2026-09-13. Written proof, not Lean-verified.

Let `X` be a nonempty compact metrizable zero-dimensional space and
`T:X->X` a homeomorphism. For a finite field `F_q`, write

`R_X=LC(X,F_q) semidirect_T Z`.

Let `Y=CR(T)` be the chain-recurrent set, with its restricted dynamics,
and put `I=LC_c(X\Y,F_q) semidirect_T Z`. All ring homomorphisms in the
universal statements below preserve the identity. No finite alphabet
or expansive dynamics is assumed.

## Theorem

Restriction to `Y` is onto and has kernel `I`. The quotient `R_Y` is
LEF, and `I` is locally matricial over `F_q`. Every unital homomorphism
from `R_X` into any directly finite ring factors uniquely through

`R_X -> R_Y`.                                       (1)

Thus (1) is simultaneously the universal directly finite, stably finite
and LEF ring quotient of `R_X`. The same assertion holds after any
finite matrix amplification, with kernel `M_m(I)` and quotient
`M_m(R_Y)`. For the original ring,

`R_X directly finite iff R_X stably finite iff R_X ring-LEF`
`                      iff every point of X is chain recurrent`. (2)

For coefficient field `F_2` and `n>=4`,

`Rad_MF(EL_n(R_X))=ker(EL_n(R_X) -> EL_n(R_Y))`,       (3)

and the kernel is locally finite while the quotient is LEF. The same
radical equality holds for `GL_n`, whose maximal MF quotient is its
restriction image. More generally, if `T^j` has no fixed points for
`1<=j<k` and `nk>=4`, (3) holds for `n>=2` and the general linear
formula holds for every `n>=1`.

In particular the exact rank-two and unit-group conclusions for
aperiodic subshifts now hold for **every aperiodic compact metrizable
zero-dimensional dynamical system**. Finite generation or property (T)
of these general ambient groups is not asserted.

## 1. Exhaust the ring by finite symbolic factors

Choose a sequence of finite clopen partitions `P_m` refining one
another, generating the topology, with maximum atom diameter tending
to zero. Let `Z_m` be the itinerary subshift of `P_m`, and let
`pi_m:X->Z_m` be the itinerary factor map. Refinement gives one-block
factor maps `rho_lm:Z_l->Z_m` for `l>=m`.

Pullback of coefficients, with the formal shift unit retained, gives
injective unital homomorphisms `R_(Z_m) -> R_X`. Injectivity follows
coefficient by coefficient from crossed-product normal forms and
surjectivity of `pi_m`. This remains valid when the action has periodic
points: the formal Laurent degrees are not identified with one another.
Every locally constant function on `X` is constant on a sufficiently
fine `P_m`, by compactness. Therefore

`R_X=union_m R_(Z_m)`                               (4)

as an increasing union of unital subrings.

Direct finiteness of `R_X` implies it for every subring in (4). The
finite-alphabet theorem then makes every such subring LEF. Conversely
any finite ring table in `R_X` lies in one stage, so LEF of all stages
makes `R_X` LEF. Ring-LEF implies stable finiteness by finite inverse-pair
tables, and stable finiteness implies direct finiteness. Thus these
three ring properties are equivalent, and hold exactly when all the
symbolic factors satisfy the finite-word cycle condition.

## 2. Construct and identify the core

Let `Y_m` be the cycle core of `Z_m`, from the
[finite-alphabet core theorem](pestov91-cycle-core-exact-mf-reflection-2026-09-13.md).
One-block factor maps preserve the cycle condition: a cycle in a word
graph maps to a closed walk, each of whose edges is cyclic. In particular
`rho_lm(Y_l) subset Y_m`. Hence the nonempty compact invariant sets
`pi_m^{-1}(Y_m)` are decreasing. Define

`Y*=intersection_m pi_m^{-1}(Y_m)`.                  (5)

For fixed `m`, compactness in the fibers of `pi_m` gives

`pi_m(Y*)=intersection_(l>=m) rho_lm(Y_l)`.           (6)

The sets on the right are decreasing subshifts satisfying the cycle
condition. Their intersection also satisfies it: at any fixed word
length their finite languages eventually stabilize to the intersection
language, so its word graph agrees with a sufficiently late stage.
Thus every symbolic factor `pi_m(Y*)` satisfies the cycle condition,
and (4), applied to `Y*`, shows that `R_(Y*)` is LEF.

Moreover `Y*` contains every closed invariant subset `W` for which
`R_W` is LEF. Each `R_(pi_m(W))` embeds into `R_W`, so the factor
`pi_m(W)` satisfies the cycle condition and is contained in `Y_m`.
Therefore `W subset Y*`.

Finally `Y*=CR(T)`. Chain recurrence passes to every factor by uniform
continuity, so `CR(T) subset Y*`. For the converse, fix `x in Y*` and
`epsilon>0`, and choose `P_m` with all atoms of diameter below epsilon.
The point `pi_m(x)` is chain recurrent in `Z_m`. Choose a closed
approximate orbit there so fine that at each step the zero-coordinate
symbol of the next point equals the one-coordinate symbol of the
current point. Lift its intermediate points arbitrarily to `X`, with
initial and final lifts both equal to `x`. Then each next lift and
the image under `T` of the previous lift lie in the same atom of
`P_m`, so their distance is below epsilon. This is a closed epsilon
chain at `x`. As epsilon was arbitrary, `x` is chain recurrent.

This also proves the last equivalence in (2) and shows that the
restricted dynamics on `Y` is itself chain recurrent.

## 3. The transient ideal is locally matricial

If `x notin Y`, some `pi_m(x)` is outside `Y_m` and therefore exhibits
a noncyclic edge in a finite word graph, at some coordinate. The
associated forward-closed reachable-vertex set gives a compressed
clopen set in `Z_m`. Pull it back to obtain a clopen `P subset X`
with `T(P) subset P` and wandering defect `D=P\T(P)` whose translate
contains `x`.

All such defects and their translates avoid `Y`, since `R_Y` is
directly finite and a nonempty defect would give a one-sided inverse
pair in that restriction ring. These wandering clopen sets therefore
cover `X\Y`. Any compact set in this complement has a finite such
cover, bounding the number of points from any orbit that it can contain.

The local matrix-algebra lemma from the finite-alphabet core proof
now applies unchanged. It uses only compact clopen supports, bounded
orbit visits, and the absence of periodic points in the complement.
Finitely many supported partial shifts generate a compact open finite
equivalence relation, and a finite clopen transversal partition gives
a finite product of full matrix algebras containing the prescribed
elements. Thus `I` is locally matricial over every finite field.

Restriction of locally constant functions onto a closed subset is
surjective by finite clopen extension. Its kernel consists of the
functions supported on a compact clopen subset of `X\Y`. Laurent
normal forms give the exact ring sequence

`0 -> I -> R_X -> R_Y -> 0`.                          (7)

## 4. Universality for directly finite target rings

For each compressed clopen `P`, put `p=1_P`, and define

`s=u p+1-p`, `t=p u^{-1}+1-p`, `d=1_(P\T(P))`.

Then `ts=1` and `st=1-d`. A unital map into a directly finite ring
must kill `d`. The two-sided ideal generated by all such defects
is exactly `I`: their translates cover the complement, and compact
supports can be subdivided using finite subordinate clopen covers.
Thus every map in question kills `I` and factors uniquely through
(7). Since `R_Y` is itself LEF and hence stably finite and directly
finite, this is the common universal quotient for all three classes.
Equivalently, `I` is the intersection of the kernels of all unital
maps to directly finite rings, and likewise for either smaller class.

For matrix amplification, let `f:M_m(R_X)->A` be unital with `A`
directly finite, and put `e=f(E_11)`. The corner `eAe` is directly
finite: extend any one-sided inverse pair by `1-e` inside `A`.
The unital map `r -> f(r E_11)` from `R_X` into that corner kills
`I`. Multiplying by the other matrix units shows that `f` kills
every entry of `M_m(I)`. The quotient `M_m(R_Y)` is LEF, proving
the amplified universal property without assuming stable finiteness
of the target `A`.

## 5. Exact MF radicals without expansiveness

The ring `R_X` is countable: a compact metrizable zero-dimensional
space has a countable clopen basis, each clopen set is a finite union
of basis sets, and the coefficient field is finite. Therefore the
existing countable-ring torsion-defect theorem applies.

Over `F_2`, the local matrix lemma identifies the general linear
restriction kernel as locally finite in all ranks. In ranks at least
two it is elementary and generated by roots with coefficients in
`I`: place matrix deviations and inverse deviations in a finite
matrix-product algebra and use that all finite invertible matrices
over `F_2` have determinant one. This is exactly the kernel argument
of the finite-alphabet core theorem, which needs no symbolic coding.

At rank at least four the printed torsion-defect theorem kills all
roots with coefficient `d` as in section 4. Normal root commutators
propagate this to all of `I`, and hence to the full restriction kernel.
The LEF core quotient proves the opposite inclusion, giving (3) and
its general linear version.

For the short-period-free cases, the clopen return-section construction
works on any compact zero-dimensional system: it uses a finite clopen
cover separated from its first `k-1` translates. Return times lie in
`[k,2k-1]`. Its induced system is again compact metrizable and
zero-dimensional, so the high-rank conclusion just established applies
to its return ring. The
[full-kernel descent proof](pestov91-return-core-full-low-rank-radical-2026-09-13.md)
then applies word for word: ring-LEF passes through the full tower
corners, identifying the induced core; two section coordinates in
each finite transient block give normal generation; the phase-zero
embedding imports the high-rank kernel. No finite-alphabet coding of
the induced system is needed now.

## Scope

The ring reflection holds over every finite field; the exact group
radical statements here use `F_2`. The low-rank short-period hypotheses
remain explicit. The general ambient groups need not be finitely
generated or Kazhdan; the analytic obstruction is still the printed
countable-ring theorem using its finitely generated witness subrings.
These are written deductions, not Lean formalizations or global
priority claims.

## Dependency validation

Cairn 2.13.1 checked the four new nodes on MSI against snapshot
`1ebcaf68d5386b35be8331017635399f5584b82a` in 32.709 seconds.
Both `check --changed` and `preview` returned zero, both new claims
were `ESTABLISHED`, and neither graph had errors. The graph contained
10,425 claims and 10,684 routes. The
[receipt](pestov91-zerodim-cairn-receipt-2026-09-13.json) records the
source-delta and runner hashes. An overlong route ID was shortened
before this successful run. This paragraph and the receipt were added
afterward. These are dependency checks for the written proof, not
finite computational or Lean verification of the general assertions.
