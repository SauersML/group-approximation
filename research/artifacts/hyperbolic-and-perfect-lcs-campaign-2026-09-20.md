# Hyperbolic residual finiteness and perfect-completeness linear games

Date: 2026-09-20. This is the next targeted research wave after the Liu
consequence integration. The two requested existence/hardness targets remain
OPEN unless a complete new proof is supplied. Graph statuses are not Lean
or external human proof certification.

## Exact goals and source gate

The geometric target is the existing
`non-residually-finite-hyperbolic-group`. It asks for a word-hyperbolic
group with a nonidentity element killed in every finite quotient. It does
not require nonsoficity or nonhyperlinearity. Current primary-source
context was rechecked against
[Wilton, with an appendix by Sisto](https://arxiv.org/abs/2410.00556) and the sources
in the preceding hyperbolic campaign; no solution is inferred from a
finite quotient search or an unproved stability hypothesis.

The quantum target is now explicitly named
`lcs-perfect-quantum-completeness-re-hardness`. Its source is
[Taller--Vidick v2](https://arxiv.org/html/2507.22444v2), particularly
Section 5 and the discussion of perfect completeness. Their reduction
has a fixed positive completeness loss; the endpoint sought here has
halting quantum value one and nonhalting value bounded by one fixed s<1.
The source also distinguishes synchronous from unrestricted quantum value.
This wave checks the actual endpoint rather than relabelling the older
weak commuting-completeness compiler as a hardness theorem.

## Three independent lanes

- Hyperbolic: test finite central detectors with elementary-abelian radical,
  beyond the preceding composition-factor exclusions. Existing concurrent
  GHB7 and triangle-matching work is read and reused, not overwritten.
- Linear test: examine the zero-noise Fourier decoding step, including
  globally compatible cheating strategies rather than isolated local cells.
- Halting switch: test whether the fixed Liu-based killed-mark seed can
  be inserted only on nonhalting inputs without violating computability.

Root coordination checks theorem interfaces, quantitative normalizations,
and exact source scopes. Any computation is remote on MSI, bounded and
single-core unless an explicit reason and resource check justify more.

## Completeness, gap, and efficiency are separate obligations

The new root uses the supremum over finite-dimensional entangled strategies.
Its halting value one is not the same as merely having a commuting strategy,
and does not require exact finite-dimensional attainment. The existing
Leavitt sign construction is excellent for a fixed qc/qa separation but
does not give the required positive quantum branch.

There are two additional distinctions:

1. A strictly positive loss depending on the input is not a constant
   soundness gap. Compactness for each individual game does not give one
   constant for a machine-indexed family.
2. A total computable algorithm emitting each finite game is weaker than
   polynomial-time succinct sampling and verification with bounded answer
   length. Exhaustively expanding a succinct verifier is computable, so the
   strong root implies the old weak compiler; the converse is not supplied.

The standard upper inclusion in RE uses only a separated threshold: pick
a rational r with s<r<1, enumerate finite dimensions, and search for a
finite-dimensional strategy with value greater than r. For a rational
finite game this is a semialgebraic existence problem in each fixed
dimension (real and imaginary parts of states and measurement matrices).
The strict inequality and density of computable approximations also give
a direct witness search. On halting inputs such a witness exists because
the supremum is one; on nonhalting inputs none does. No computable bound
on the required dimension is asserted. Thus perfect completeness means
a value statement, not an effective finite-dimensional bound.

## Attribution and certificate boundary

Taller and Vidick own the entangled long-code reduction and its source
analysis; the earlier BCS hardness and repetition inputs retain their
authors. Jihao Liu's internality, Andreas Thom's conditional normalization,
and the repository's credited Leavitt calculations supply the fixed seed
used in the switching experiment. They do not prove perfect-completeness
hardness. The hyperbolic central-extension strategy retains its separate
Dogon--Vigdorovich and cohomological premises.

A failed subclass is a route obstruction, never a proof that either
major open target is false.

## Results of the three lanes

### 1. A finite-quotient obstruction for the hyperbolic construction

[[hrf-next-affine-radicals-preserve-detector-image]] proves that a split
elementary-abelian p-radical adds no detectable edge twists under two
explicit first-cohomology vanishing hypotheses. The proof decomposes
central extensions into inflated base classes and invariant alternating
forms, then shows that the latter have zero edge discrepancy. It does
not classify all finite quotients or prove persistence. The written
proof is [here](hrf-next-attack-2026-09-20.md).

The next useful targets are the omitted mixed H^1 classes, nontrivial
vertex affine cocycles, and nonsplit or nonabelian radicals. A search
restricted to the covered split quotients cannot settle the universal
finite-quotient condition. This theorem is algebraic; it does not use
Liu's internality theorem or assert a new stability theorem.

### 2. The unchanged zero-noise linear test has a global counterexample

[[lcs-pc-zero-noise-coloring-cheat]] uses the three-colouring game of K4.
Its unrestricted quantum value is at most 11/12; the associated repeated
projection game's value tends to zero. Nevertheless the noiseless TV
output has a perfect classical strategy at every repetition count.
The strategy is one globally consistent assignment, not a collection
of incompatible local witnesses. The full proof and exact source
interfaces are [here](lcs-perfect-completeness-attack-2026-09-20.md).

This closes the proposed generic zero-noise decoder attack. It leaves
open a source-specific reduction or a changed test that defeats these
odd-support strategies while preserving perfect quantum completeness.

### 3. Finite bad seeds cannot implement the whole nonhalting branch

[[lcs-switch-marked-seed-transport-is-re]] proves a computability
obstruction. For any recursively enumerable library of finitely
presented killed-mark seeds, membership in the normal closure of their
transported marks is recursively enumerable. If every nonhalting output
sign had such a certificate, and every halting output had a matrix model
preserving its sign, these certificates would enumerate coHALT.
This remains impossible when the maps are chosen noncomputably and
have unbounded word length. The proof is
[here](lcs-halting-switch-audit-2026-09-20.md).

Thus a fixed Liu-based seed supplies the separating example but cannot
by this finite transport mechanism supply all negative instances of the
desired hardness reduction. A successful reduction needs a negative
obstruction not exhausted by that certificate language, as well as a
uniform quantitative gap and the stated efficiency.

## Review and integration record

The root checked all three written arguments. A sibling independently
checked the unrestricted K4 bound and all raw-query identifications
against the TV definitions, and checked the affine-extension
decomposition and its edge-phase identity. The other sibling checked
the seed-switch enumeration and the exact efficient quantum-completeness
endpoint; the weak-interface conversion explicitly discards unsampled
constraints. No flaw was found in these
bounded reviews. These are internal mathematical reviews, not Lean or
external human verification, and no literature-priority claim is made.

Only this wave's owned files are staged. Concurrent hyperbolic and Lean
work is preserved and excluded from this wave's source snapshot. Graph
validation is performed on MSI against the pinned staged tree; its
report records the source revision, statuses, and limitations separately.
Both requested main targets remain OPEN.
