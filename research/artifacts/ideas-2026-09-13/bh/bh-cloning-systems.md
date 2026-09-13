# Idea lane bh-cloning-systems (2026-09-13)

Target: `boone-higman-conjecture`. Lens: Witzel–Zaremsky cloning systems and other
Thompson-like groups built from families of groups (forest-skein groups).

This is an ideas artifact. It changes no node status and claims nothing established.
Kill tests were run where indicated. Each source is labelled with how far it was read.

## Sources read

- Zaremsky, *A user's guide to cloning systems*, arXiv:1606.08762. Full text read locally
  with pdftotext:
  - §2: the definitions. The `ι_{m,n}` are injective and the `ρ_n: G_n → S_n` are
    homomorphisms. The cloning maps `κ^n_k` are injective functions satisfying (C1) cloning a
    product, (C2) product of clonings, and (C3) compatibility, but (C3) only "for all
    `i ≠ k, k+1`".
  - §5.2, quoting WZ17 Observations 3.1 and 3.2:
    - "the map `[T−, g, T+] ↦ [T−, ρn(g), T+]` is a homomorphism `T(G∗) → V`", with kernel
      `K(G∗)`;
    - in the pure case `T(G∗) = K(G∗) ⋊ F`;
    - "`g ↦ [T, g, T]` is a monomorphism `Gn ↪ T(G∗)`".
  - §5.3:
    - direct powers `G_n = G^n` give `T = K ⋊ F` with a retract onto `G`;
    - for the twisted systems on `S_n^±` and `B_n^twist`, "there is no 'obvious' way to
      build such a surjection" onto `V`.
- Witzel–Zaremsky, arXiv:1405.5491 (Groups Geom. Dyn. 12 (2018)). Abstract only.
- Skipper–Zaremsky, arXiv:1709.06524. Abstract only:
  - almost-automorphisms of `T_d` arise from a "d-ary cloning system";
  - `V_d(G)` is `F_∞` when `G` is.
  - The d-ary axioms were not re-read.
- Brothier, Forest-skein groups II (arXiv:2212.01993) and III (arXiv:2406.09718);
  Brothier–Seelig arXiv:2512.18943. Abstracts only.
- Repo nodes used as kill tests:
  - `baumslag-gersten-embeds-in-no-rover-nekrashevych-group` (BG embeds in no `V_{d,r}(G)`,
    "in particular `V`, `T` or `F`");
  - `deligne-lattice-embeds-in-no-rover-nekrashevych-group`;
  - `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`;
  - `complexity-bounded-host-classes-are-not-universal`;
  - `bht-trivial-normal-intersection-envelope`.

## Approach 1. Direct-power / wreath cloning host over a Clapham overgroup

**Idea.**
- Take the finitely presented overgroup `P ⊇ G` with solvable word problem that Clapham's
  theorem provides.
- Form the cloning system `G_n = P^n`, or `P ≀ S_n`, with cloning by diagonal duplication
  of the cloned coordinate.
- Finiteness transfers well in this setting (WZ17 §6, Tanushevski).
- So `T(G∗)` is plausibly finitely presented and contains `P`, hence `G`.
- Look for the envelope among its normal subgroups, e.g. a simple derived subgroup.

**Would prove.** BH, if some finitely generated simple normal subgroup of `T(G∗)`
contains `G`.

**Kill test.** Apply the elementary normal-subgroup argument of Approach 2 to the pure
kernel `K(G∗)`.

**Result.** Killed.
- In the pure case `T = K(G∗) ⋊ F` (guide §5.2), and `K(G∗)` is a directed union of copies
  of `P^n`.
- By Approach 2, any finitely generated simple normal `S ⊇ G` embeds in `F`, or already
  sits inside some `P^n`, and then in `P`.
- The finitely presented overgroup step was never the difficulty.
  `bht-trivial-normal-intersection-envelope` already gives a finitely presented `P` missing
  every proper normal subgroup, and root Attempt 1 records why its quotients don't help.

**Verdict.** killed.

## Approach 2. Normal-subgroup dichotomy for compatible cloning systems

**Idea.** Use the structure of `T(G∗)` directly.
- `K = K(G∗)` is normal.
- For `S` simple normal, `S ∩ K` is normal in `S`, so `S ∩ K = 1` or `S ⊆ K`.

**Claim (hand proof).** Assume the forgetful map `[T−, g, T+] ↦ [T−, ρ(g), T+]` is a
homomorphism, and every element of its kernel can be written `[T, g, T]` with `ρ(g) = 1`.
- Then `K` is a directed union over trees `T` of the subgroups `{[T, g, T] : g ∈ ker ρ_n}`.
- Each of these is isomorphic to `ker ρ_n`, by WZ17 Observation 3.1. On `ker ρ_n` the
  cloning maps are homomorphisms by (C1), and trees have common expansions.
- So for every finitely generated simple normal subgroup `S` of `T(G∗)`, either:
  - (a) `S ∩ K = 1`, and `S` embeds in `T/K ≤ V`; or
  - (b) `S ⊆ K`, hence `S` lies in one stage and embeds in `ker ρ_n ≤ G_n`.

**Would prove / kill.**
- Case (b) means the Thompson-like group only rediscovers an envelope the cloning data
  already contained.
- Case (a) forces every subgroup of `S` into `V`. BG embeds in no `V`, and the Deligne
  lattice embeds in no `V_d(H)`, including `H = 1`.
- So no compatible cloning system is a universal BH container via its simple normal
  subgroups, regardless of finiteness properties.

**Kill test run.** The dichotomy needs an actual homomorphism to `V` with that kernel.
- The guide's §5.2 asserts the homomorphism.
- The guide's §5.3 says that for twisted systems, where (C3) fails at `i = k, k+1` (signed
  permutations, twisted braids), no obvious surjection to `V` exists.
- So the argument is safe exactly for systems where (C3) holds at every `i`, or where some
  other homomorphism with kernel a directed union of stage kernels exists.

**Consistency check.**
- Zaremsky's finitely presented simple envelopes `[V_d'(G), V_d'(G)]` for self-similar `G`
  (arXiv:2405.09722) contain inputs such as infinite torsion self-similar groups.
- They sit inside Röver–Nekrashevych groups, whose cloning twists at the cloned positions
  through states.
- That matches the escape above. This was not re-derived from the d-ary axioms.

**Verdict.** killed as a universal method for compatible systems. It survives as a
constraint.

## Approach 3. Twisted cloning systems that realize no tree almost-automorphisms

**Idea.** The only Thompson-like-from-families escape from Approach 2 is twisting: cloning
at position `k` must permute or twist the two children in a way ρ cannot see. Design twisted
cloning systems built from the input's own algebra:
- `G_n = P ≀ S_n^±`-like families, with the children's labels mixed by an action
  `θ: P → Aut(P × P)`;
- or labels drawn from a finitely presented group whose cloning consumes `P`'s presentation.

Three requirements:
- (R1) nontrivial twist at cloned positions, else Approach 2 applies;
- (R2) the resulting group is not realized by almost-automorphisms of a locally finite tree,
  else the BG wall (every map `BG → A_{d,r}` kills `a`) and the Deligne wall apply;
- (R3) finite presentation of `T(G∗)` from Stein–Farley descending-link connectivity.

**Would prove.** BH, if some twisted system meeting (R1)–(R3) has a simple derived
subgroup containing the input for every decidable `G`.

**Kill tests run.**
- (R1)/(R2) are consistent. Signed-permutation twists yield `V^± ≅ V` (guide §5.3, citing
  BDJ17), which is a tree group. A twist valued in `Aut(P × P)` for non-residually-finite
  `P` has no evident tree realization, since the repo walls use tree actions.
- (R3) is untested. The complexity wall doesn't apply, because the host varies with `G`.

**Risk.** For twisted Brin–Thompson groups, the known finite-presentation proof
(arXiv:2405.18354) needs exactly the type (A) conditions: finitely generated stabilizers, and
finitely many orbits on two-element subsets. (R3) may reintroduce type (A), making this the
BFFHZ route in cloning language.

**Next test.** Write the descending link for one twisted wreath system, e.g. `P = BS(1,2)`
with `θ` swapping and twisting by the automorphism `a ↦ a²` where available. Compare its
connectivity conditions with type (A).

**Verdict.** unclear. It is the best survivor of this lens, and its main risk is collapsing
onto type (A).

## Approach 4. Forest-skein hosts from skein presentations encoding the input

**Idea.** Brothier's forest-skein groups come from skein presentations (colours plus pairs
of coloured trees). Per the FS III abstract, Ore forest-skein categories give F/T/V-type
groups with simple derived subgroups under a dynamical or categorical criterion. Per the
Brothier–Seelig abstract, there are finitely presented simple `F_∞` examples acting on the
circle. They are not cloning systems, so Approach 2 doesn't apply directly. Encode a finite
presentation of `P ⊇ G` into a higher-dimensional skein presentation so that `G` appears in
the V-type group.

**Would prove.** BH, for inputs landing in a finitely presented simple derived subgroup.

**Kill tests run.**
- One-dimensional skein presentations: the FS II abstract says the groups decompose as
  wreath products. A normal base subgroup brings back Approach 2's dichotomy, so those die.
- T-type groups act faithfully on the circle (Brothier–Seelig abstract). Finite subgroups of
  `Homeo^+(S^1)` are cyclic (classical, not re-read). So inputs containing `SL_3(Z) ⊇ (Z/2)^2`
  can't enter T-type hosts.
- V-type hosts: no obstruction found. Whether arbitrary groups embed in any forest-skein
  group isn't addressed in the abstracts read.

**Next test.** Read FS III's categorical simplicity criterion. Decide whether a skein
presentation can contain a copy of a given finitely presented group, with that copy
surviving in the derived subgroup, and whether V-type forest-skein groups have a forgetful
quotient onto V (if so, Approach 2 kills them too).

**Verdict.** unclear (V-type only).

## Constraints recorded by this lane

- **(K1)** A group with a nonabelian quotient `Q = T/K` can host a finitely generated simple
  normal `S ⊇ G` only if `G ↪ Q`, or `S` sits inside `K`. Any Thompson-like construction
  with a natural forgetful quotient must twist it away.
- **(K2)** In compatible cloning systems the pure kernel is a directed union of the stage
  kernels. Envelopes found there already live in some `G_n`.
- **(K3)** The surviving shapes are twisted systems (R1)–(R3) and V-type forest-skein
  groups. Both still owe a finite-presentation criterion stated without type (A).
