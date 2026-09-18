# Graphical small cancellation inputs as a Boone–Higman hard test case (bh-graphical-sc, 2026-09-18)

This lane landed four nodes:
- `graphical-small-cancellation-inputs-satisfy-boone-higman` (OPEN): the test case.
- `small-cancellation-groups-realize-every-wp-complexity` (ESTABLISHED, lane proof) with its route `classical-small-cancellation-complexity-realization-proof`.
- `fp-simple-nonexact-group-via-graphical-small-cancellation-bh`: a route into the OPEN `fp-simple-nonexact-group`.
- `complex-fp-simple-groups-via-small-cancellation-bh`: a route into the OPEN `fp-simple-groups-with-arbitrarily-complex-word-problem`.

No priority is claimed. The complexity-realization lemma uses only classical small cancellation (Greendlinger, Dehn) and the time hierarchy.

## 1. Subfamilies and their status

| Subfamily | Status | Reason |
|---|---|---|
| Finite `Γ` (finitely many finite components), including every finitely presented `C'(1/6)` group | BH holds | hyperbolic (graphical small cancellation, cited) ⇒ BBMZ arXiv:2309.06224 |
| Infinitely many components, members that are subgroups of a hyperbolic or a linear group | BH holds | subgroups of BH groups are BH |
| Osajda's residually finite non-exact decidable group (`decidable-residually-finite-non-exact-group-exists`) | OPEN | BH for it ⇒ an f.p. simple non-exact group |
| Gromov-type monsters with isometrically or weakly embedded expanders and solvable word problem | OPEN | same as the row above; Haagerup hosts are excluded |
| Arzhantseva–Osajda a-T-menable non-exact graphical groups, if decidable | OPEN | not excluded from Haagerup hosts; see §3 |
| Two-generator classical `C'(1/6)` groups `G_A`, with `A` decidable and hard | OPEN | BH for the whole family ⇒ f.p. simple groups of unbounded word-problem complexity |

## 2. Hosts against the family

| Host class | Excluded for | Node |
|---|---|---|
| Linear over commutative rings | non-exact members | `commutative-ring-linear-groups-have-property-a` |
| Any class with one recursive WP time bound (hyperbolic, rational homeomorphism, contracting RSG, automaton groups, each single group) | some hard `G_A` | `complexity-bounded-host-classes-are-not-universal`, `small-cancellation-groups-realize-every-wp-complexity` |
| Haagerup groups (`F`, `T`, `V`, Higman–Thompson, SFT full groups) | expander-type members | `haagerup-hosts-carry-no-weak-expander` |
| Exact finitely presented simple groups (lattices on products of trees, finite asymptotic dimension, CAT(0) cubical, Kac–Moody) | non-exact members | `exactness-separates-boone-higman-iff-fp-simple-groups-exact` |
| Twisted Brin–Thompson `SV_G` with hard type (A) actors | not excluded | the actor node `type-a-actors-with-arbitrarily-hard-word-problem` is OPEN |
| `L^x = L_(F_2)(1,2)^x` | not excluded | the only finitely presented simple group here known not to be Haagerup |

So a proof of the OPEN claim must produce hosts of unbounded word-problem complexity. For the non-exact members, the hosts must also be non-exact and, for expander-type members, non-Haagerup. No known finitely presented simple family is shown to have all of these.

## 3. The sharpest sub-questions

1. **An Arzhantseva–Osajda group in V.** Take a decidable, a-T-menable, non-exact graphical group, if one exists. Does it embed in Thompson's `V`, or in an SFT topological full group? Haagerup hosts do not exclude it. An embedding would show `V` non-exact, which settles `fp-simple-nonexact-group` unconditionally. The solvable word problem for the AO construction with a recursive graph sequence is not established here, and is the first thing to check.
2. **Hard `G_A` in `SV_G`.** Does `G_A`, for hard `A`, embed in a twisted Brin–Thompson group with a hard type (A) actor? This is the only known host shape of unbounded complexity.
3. **Monster in `L^x`.** Does an expander-type monster embed in `L^x`? That is the only non-Haagerup finitely presented simple host in the graph.

## 4. Sources

- Osajda, arXiv:1703.03791. On main via `decidable-residually-finite-non-exact-group-exists` and its artifact.
- Lyndon–Schupp, Ch. V: textbook, not re-read.
- BBMZ, arXiv:2309.06224: main theorem, not re-read here. The intermediate host is on main.
- Ollivier and Gruber, on the hyperbolicity of finite graphical `C'(1/6)` groups: cited, not read at source.
