# Archived route: Boone source through the generic Rabin chain

The target is established by the direct variant transform, so this older
decomposition no longer belongs in the active graph.

## Why sufficient

The target is the fourth field of `MarkovMFConsequences.AdianRabinReduction`:
a computable `transform` on codes together with its `correct` equivalence.  Its
two inputs are exactly the two prerequisites, and what remains after them is
item **D6** of the cost table -- 100--200 mechanical lines *for this target*.
Note that D6 as originally scoped also covered discharging `¬ComputablePred
sourceProperty`, which is not part of this target and is not mechanical: see
[[uniform-word-problem-on-presentation-codes-undecidable]], separated out as
D4' once D4 closed and it became clear that the abstract theorem does not hand
the assembly a code.

Take the finitely presented group `H` with undecidable word problem from the
first prerequisite, and apply the construction of the second with forbidden
group `F = E`, this repository's literal non-MF group, which is finitely
presented.  The dichotomy is then the `correct` field verbatim: `w = 1` gives a
trivial, hence MF, presentation, and `w != 1` gives one containing `E`, hence
non-MF by subgroup heredity of MF.  Computability of `transform` is
computability of the chain, which the second prerequisite asserts.

Assembly is D6: package the computable map and the equivalence into the
structure, whose other three fields -- the `Primcodable` code type, the
`FinitePresentationSemantics` and the `MarkovWitness` -- are already inhabited
by [[operator-mf-is-a-markov-property]].

## Neither prerequisite is the target restated

The first is a statement about one group and its word problem, with no map
between presentations in it.  The second is a construction with no
undecidability in it, uniform in the forbidden group and blind to MF.  The
conjunction is what makes the composite reduction, and the fact that this is
the *only* recorded decomposition of the target is itself information: the four
shortcuts listed on the target claim are the arguments that no cheaper route
exists.
