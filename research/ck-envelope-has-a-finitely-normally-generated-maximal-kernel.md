---
rg: 2
id: ck-envelope-has-a-finitely-normally-generated-maximal-kernel
kind: claim
refuted_by: [poisoned-ck-envelopes-have-no-fng-maximal-kernel]
title: The finitely presented normal-generator envelope has a maximal proper normal subgroup that is finitely normally generated
distinct_from:
  poisoned-ck-envelopes-have-no-fng-maximal-kernel: that is the counterexample to this universal statement -- for every core and normal generator, an envelope supplied by Chatterji--Kassabov (and a marked Steinberg cover over it) all of whose nontrivial quotients have unsolvable word problem; this is the refuted assertion that every such envelope has a finitely normally generated maximal kernel.
  finite-infranormal-subgroup-is-normal: that is the elementary fact that a FINITE infranormal subgroup is normal, about conjugation preserving cardinality; this asks for a finite NORMAL GENERATING SET of a maximal normal subgroup, which is a condition on generating data rather than on the subgroup's size -- the kernel here is expected to be infinite.
  fp-quotient-iff-kernel-finitely-normally-generated: that is the general equivalence between finite presentability of a quotient and finite normal generation of its kernel, true for every finitely presented group; this asserts that one particular class of envelopes actually HAS such a kernel at a maximal element, which is the open existence statement the equivalence turns the conjecture into.
  boone-normal-closure-of-t-finitely-generated: that concerns the Boone HNN tower and finite generation of a normal closure AS A SUBGROUP; this concerns finite NORMAL generation of a maximal normal subgroup of an elementary matrix group, a different group, a different construction and a strictly weaker finiteness condition.
  every-nontrivial-core-element-normally-generates-the-envelope: that records how rigid the envelope is -- perfect, no finite quotients, every core element a normal generator; this asks for a compactness property of its normal lattice, and the audit found no implication from the rigidity clauses to this one.
  miller-amalgam-ck-envelopes-have-no-fng-maximal-kernel: that exhibits, for every core with an element of infinite order, an envelope meeting all hypotheses here whose every nontrivial quotient is undecidable, so it has no such kernel; this asks for such a kernel with existential freedom in the construction, which is tenable only for a clean marking.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Let `S` be a finitely generated computably presented infinite simple group,
`1 != s in S`, and let `Gamma` be a finitely presented group containing `S`
with `Gamma = <<s>>_Gamma`, as supplied by
`chatterji-kassabov-normal-generator-embedding`.  Then `Gamma` has at least
one maximal proper normal subgroup `M` that is finitely normally generated in
`Gamma`.

Open.  This is the entire remaining content of
`boone-higman-via-ck-maximal-kernel`, and by
`fp-quotient-iff-kernel-finitely-normally-generated`
it is equivalent to: **some** maximal proper normal quotient of `Gamma` is
finitely presented.

## Why this and not the conjecture

By `proper-normal-subgroups-miss-the-normally-generating-core` every maximal
proper normal quotient of `Gamma` is simple and contains `S`, hence contains
the original group.  So there is no work left in the *embedding* — only in
the *presentation*.  The quantifier is existential over maximal normal
subgroups and over the freedom in the construction, which is why this is not
a restatement of the conjecture: it is a question about the normal lattice of
a specific, explicitly presented matrix group.

The coefficient ring can be the explicit finitely presented ring

    U = Z[G~]<p,q>/(p(1-g)q - 1).

**September 8 correction:** this does not establish finite presentation
of `EL_4(U)`. The verified finite-presentation theorem applies to
`St_4(U)`. By [[ck-steinberg-marked-cover]], one can use a finitely
presented marked quotient `Gamma` of `St_4(U)` mapping onto `EL_4(U)`.
The covering kernel remains uncontrolled. This open claim concerns the
finitely presented cover; its normal subgroups must not be identified
with the normal subgroups of the elementary image without an additional
argument.

## Attempts

1. **Zorn restricted to the finitely normally generated proper normals.**
   *Dies on chains.*  The union of an ascending chain of finitely normally
   generated normal subgroups need not be finitely normally generated, so the
   restricted poset has no upper bounds and Zorn does not apply.  Finite
   generation of `Gamma` gives properness of the union (that is the argument
   in `proper-normal-subgroups-miss-the-normally-generating-core-proof`) and
   nothing more.  A Max-n condition on the normal lattice would rescue it;
   none is known for these groups.
2. **Derive it from property (T).**  *Dies as a general normal-Noetherianity
   principle.*  `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels` gives
   one torsion-free finitely presented word-hyperbolic property-`(T)` group
   with continuum many maximal normal subgroups that are not finitely normally
   generated.  Thus property `(T)` does not imply `Max-n`, even with those
   additional hypotheses.  This does not refute the existential claim for
   the special elementary-matrix envelope: a successful proof must use that
   envelope's matrix/ring structure or select one special quotient.
3. **Derive it from the rigidity already proved.**  *No implication found.*
   `every-nontrivial-core-element-normally-generates-the-envelope` makes the
   envelope perfect with every proper quotient infinite and no nontrivial
   finite quotient.  All of that is non-existence of *small* quotients; this
   claim is compactness of *some* maximal kernel.  A group with no small
   quotients can still have every maximal normal subgroup infinitely normally
   generated, and nothing found here excludes it.
4. **Weaken to an effective maximal kernel** — ask only that `M` be
   recursively enumerable as a normal subgroup.  *Unsolved and strictly
   easier*; it would give a finitely generated computably presented simple
   quotient with decidable word problem, not a finitely presented one.  The
   effective-Zorn construction needs to decide `<<M, x>> ∩ S = 1`, and the
   clean criterion "proper iff misses `S`" is not effective in the direction
   required.  Recorded here rather than as a node because it is a different
   target, not a route into this one.
5. **Transfer every maximal kernel to the matrix image.** The exact
   alternative is [[ck-cover-quotient-kernel-dichotomy]]. A maximal kernel
   either contains the covering kernel and descends to a proper matrix
   kernel, or maps onto the whole matrix group while the covering kernel
   surjects onto the simple quotient. The second case cannot be excluded
   by assuming stable K_2 properties for the unstable kernel. Neither
   branch currently supplies finite normal generators for the maximal
   kernel upstairs.
6. **Refine the matrix branch by level and congruence layer (swarm-0917).**
   *Established classification, and one regime reduced exactly.*
   [[ck-maximal-kernel-four-regimes]] places every maximal kernel `M` in
   exactly one regime, where `I = lev(rho(M))`:
   - R1: a quotient of the covering kernel;
   - R2: a quotient of the congruence layer `C_I/E_4(U,I)`;
   - R3: a level-zero normal subgroup of `PE_4(U/I)`;
   - R4: `M` is the congruence kernel `rho^{-1}(C_I)`.

   In R4, finite normal generation of `M` is **equivalent** to two
   conditions: `I` is finitely generated, and `PE_4(U/I)` is finitely
   presented and simple. The proof reads finite ideal generators off finite
   normal generators, together with the centre of `E_n`. So the hole follows
   from the open ring statement
   [[ck-sandwich-ring-has-fp-projective-simple-quotient]], via route
   [[ck-maximal-kernel-via-projective-quotient-ring]].

   It is equivalent to that statement once three standard normal-structure
   properties hold for `U`, each killing one regime:
   - the covering kernel has no nonabelian simple quotient (R1);
   - the relative commutator formula `[Q, C_I] <= E_4(U,I)` holds (R2);
   - `PE_4` over quotients of `U` detects roots (R3).

   *Where standard approaches die.* A proof by sandwich or congruence
   methods cannot be cheaper than building a finitely presented simple
   quotient ring of `U`, with `S` in its units and a finitely presented
   simple rank-four projective elementary group. That is the projective
   ring-host wall, and the kernel lane and the ring-host lane merge there. A
   genuinely different proof has to produce a maximal kernel in R1, R2 or R3,
   and must therefore exploit a failure of one of the three properties for
   this specific non-quasi-finite ring.
7. **Transplant stability to certify finite normal generation
   (swarm-0917, stability-approximation).** *Dead as a class.*
   By [[fp-simple-groups-are-isolated]] and Cornulier--Guyot--Pitsch, a
   maximal `M` is finitely normally generated exactly when `Gamma/M` is
   isolated. The transplant tries to pick `M` so that `Gamma/M` is stable
   for a metric class `C`, and to read finitely many relators off the
   stability. `C` is Hilbert--Schmidt unitaries, Hamming permutations or
   operator norm. The obstruction is the stability invariant of the simple
   quotient, and it dies at the step "`C`-stable, hence finitely normally
   generated".

   - *Invariant.* Let `L` be a finitely generated infinite simple group, for
     example any `Gamma/M`. `L` has no nontrivial finite-dimensional unitary
     representation: its image would be a finitely generated linear group,
     hence residually finite (Malcev). So
     [[infinite-simple-group-hs-stable-iff-nonhyperlinear]] and
     [[infinite-simple-group-permutation-stable-iff-nonsofic]] apply with no
     presentation hypothesis. `L` is HS-stable iff it is not hyperlinear,
     and permutation-stable iff it is not sofic. The operator-norm case is
     the same argument: an asymptotic representation that is not trivial in
     the limit is injective on `L`, and stability would give a separating
     family of genuine finite-dimensional representations. That contradicts
     residual finiteness exactly as in
     [[hyperlinear-flexibly-hs-stable-group-is-residually-finite]].
     So `C`-stability of a simple quotient is a pure approximation invariant
     of its isomorphism type and carries no presentation data.
   - *Where every member dies.* Every finitely generated group is a quotient
     of a finitely presented one, so the step would prove that every
     finitely generated, infinite, simple, non-`C`-approximable group is
     finitely presented. This fails whenever a non-`C`-approximable
     countable group `N` exists. The groups `N x B` range over B. H.
     Neumann's continuum of two-generator groups `B`. Each one sits in a
     two-generator simple group by
     [[countable-group-embeds-in-two-generator-simple-group]], and in a
     Kazhdan one by [[countable-group-embeds-in-fg-simple-kazhdan-group]].
     A finitely generated group has only countably many finitely generated
     subgroups, so these envelopes have continuum many isomorphism types.
     Only countably many of them are finitely presented. All are
     non-`C`-approximable, since approximability passes to subgroups, and
     hence all are `C`-stable. If no such `N` exists, no infinite simple
     quotient is `C`-stable and the premise is never met. Adding property
     (T) does not rescue the step, by the Kazhdan envelopes. On a
     `C`-approximable quotient the premise fails outright.
   - *What survives in regime R4.* The approximation type of a witness is
     fixed by its ring type, not by a presentation. Let `R = U/I` be simple.
     The sandwich gives `p (rq) = 1` with `r = 1-g`, and there are two cases.
     - `(rq)p = 1`. Then `p` is a unit and `r` is right invertible, and
       direct finiteness makes `r` a unit.
     - `R` has the nonzero defect `1-rqp`. In positive characteristic,
       [[finite-additive-order-one-sided-defects-are-mf-invisible]] puts
       `e_12(1-rqp)` in `Rad_MF(E_4(R))`. Its image in the simple group
       `PE_4(R)` is nontrivial because `e_12(x)` commutes with `e_21(1)`
       only for `x = 0`. So `PE_4(R)` has no nontrivial homomorphism to a
       norm matrix corona.

     The same argument applies to any one-sided defect. So in positive
     characteristic an MF witness `PE_4(R)` forces `R` to be directly finite,
     with `1-g` and `p` units. In characteristic zero the analogous
     conclusion needs MF of `E_N(R)` for every `N`, by
     [[mf-elementary-groups-force-stably-finite-simple-rings]], which a
     witness does not supply. That is a constraint on the ring host of
     [[ck-maximal-kernel-four-regimes]], not a route to finite presentation.
     The approximation family can only screen ring types, and cannot supply
     the missing relators.
8. **Certify the kernel by measure, entropy, genericity or a limit
   (swarm-0917, entropy-measure).** *Dead as a class.*
   The class covers four kinds of argument.
   - Put a Borel probability measure on the proper normal subgroups of
     `Gamma`. Candidates are invariant or stationary random subgroups pushed
     to normal cores, Glasner--Weiss limits under property (T), laws of
     random quotients, or limits of counting measures on finite
     approximations. Then argue that a positive-measure or positive-entropy
     set of maximal kernels has the property.
   - Argue that a Baire-generic maximal kernel in some closed family has it.
   - Build `M` as the Chabauty limit of a construction sequence, such as
     iterated small-cancellation or random-quotient towers.
   - Use conjugation dynamics on normal subgroups.

   - *Invariant.* By [[fng-maximal-kernels-are-isolated-proper-normal-points]],
     a maximal `M` is finitely normally generated exactly when `M` is an
     isolated point of the Chabauty space `N(Gamma)`. The isolated points
     form a countable set. Isolation is a topological property that no
     measure detects.
   - *Where every member dies.* The step is "positive measure, entropy or
     genericity, or being a limit, implies finitely normally generated". A
     finitely normally generated maximal kernel in the support of `mu` is
     an atom of `mu`, so every non-atomic measure gives these kernels mass
     zero. A maximal kernel that is a limit of other normal subgroups is not
     finitely normally generated. A closed family with no isolated points
     contains no such kernel. The dynamics carries no information:
     conjugation acts trivially on `N(Gamma)`, every measure on it is
     invariant and stationary, and the ergodic ones are Dirac masses. So an
     ergodic IRS on normal subgroups names one kernel and certifies nothing
     about it, and Glasner--Weiss closedness under (T) is vacuous here.
   - *Why the atom branch is no survivor.* An atom certifies nothing by
     itself. By [[kazhdan-hyperbolic-continuum-non-fng-maximal-kernels]], a
     Dirac mass sits on a non-isolated maximal kernel just as easily. To
     prove that an atom is isolated one must exhibit a finite `F` with
     `<<F>>` maximal, which is this claim with no gain.
   - *Consequence for method.* Any proof must name its kernel by finitely
     many relators. In regime R4 of [[ck-maximal-kernel-four-regimes]] that
     means finitely many ideal generators. Probabilistic or ergodic input can
     only screen candidate relator sets, and screening must then be closed
     by a deterministic maximality proof.

9. **Realise regime R4 by a square-module ring host over an arbitrary base
   (swarm-0917, linear-characteristic).** *Dead for every host whose centre is
   infinite. What survives is a sharper decomposition.*
   - *The class.* It covers every witness in the sufficient branch of
     [[square-module-ring-hosts-are-sandwich-ring-quotients]]: a finitely
     presented simple `R ≅ R^d` (`d >= 2`) with `S <= R^x` and `PE_4(R)`
     finitely presented and simple, whose centre is an infinite field. This
     includes every characteristic `0` host (the centre contains `Q`) and
     Leavitt-tensor hosts `B ⊗ L_K(1,d)` over an infinite `K`.
   - *Invariant.* The central scalar subgroup `(Z(R)^x)^(d-1) I_4`. By
     [[square-module-elementary-centre-is-central-units]] it lies in
     `E_4(R)`, because scalars are invisible to `K_1` on a square module:
     `[c] = d[c]`.
   - *Where every member dies.* Clause (c) of
     [[ck-sandwich-ring-has-fp-projective-simple-quotient]], "`Z(E_4)`
     finitely generated", equivalently clause 2 of
     [[projective-elementary-fp-kernel-criterion]]. The subgroup
     `(k^x)^(d-1)` is not finitely generated for an infinite field `k`.
   - *Survivor.* Square-module witnesses must be `F_q`-algebras with finite
     centre. For `d = 2` the centre of `E_4(R)` is exactly `Z(R)^x`. So finite
     presentation of `PE_4(R)` splits into two independent prerequisites:
     `ker(St_4 -> E_4)` finitely normally generated, and `Z(R)^x` finitely
     generated.
   - *Where the premise of the Leavitt lane comes from.* Requiring `E_n`
     itself to be simple forces `Z(R) = F_2`, so the `F_2` premise there is
     forced.
   - *What escapes.* Rings that are not square-module escape, for example
     Dedekind-defect witnesses of R4 whose `K_1` detects scalars. A route
     through Ara--Goodearl--Pardo (purely infinite simple rings with `[1]`
     torsion in `K_0` are square-module) is not imported.

10. **Invert the hypotheses with a hereditarily undecidable group
    (swarm-0917-w5-pull-bh-2, minimal-counterexample).** *Kills every
    hypothesis-only proof. The claim stays OPEN only under its existential
    reading, for a clean marking.*
    - *Construction.* See [[miller-amalgam-ck-envelopes-have-no-fng-maximal-kernel]]
      (ESTABLISHED).
      - Take Miller's finitely presented `M`, all of whose nontrivial
        quotients have unsolvable word problem.
      - Put `w = a z a z^-1` in `M * <z>`.
      - Amalgamate `t = w` with `S`, where `t in S` has infinite order.
      - Apply CK Theorem 3 to this input with `g = s`.
    - *Result.* The output `Gamma` is finitely presented, has property (T),
      contains `S` and satisfies `Gamma = <<s>>`. Every proper normal `N` has
      `s notin N`, so `M` is not contained in `N`. So every nontrivial quotient
      has unsolvable word problem, and by Kuznetsov no maximal kernel is
      finitely normally generated, or even r.e.
    - *Invariant.* WP-poison of the normal generator.
    - *Where every member dies.* The step "fp + (T) + `S <= Gamma = <<s>>` +
      CK provenance for some input ⇒ fng maximal kernel". Attempts 1–3 belong
      to this class.
    - *Scope.* The route's own cores contain `Z`, since they are built from
      `G0 x Z`. So the universal reading fails there too.
    - *What survives.* The route picks a Clapham `H` with solvable word
      problem and may pick a decidable `T`. For that marking the mechanism is
      blocked by [[clean-ck-cover-confines-poison-to-covering-kernel]]. Any
      proof must use decidability of the marking at some step.
    - *Credit.* The same mechanism was first posted on the bus by `c-ckmax`,
      via a Heisenberg shift group; those nodes never entered the graph.

11. **Inverter: the biography of a counterexample becomes a construction.**
    *The statement as written is false for every `(S, s)`.* See
    [[poisoned-ck-envelopes-have-no-fng-maximal-kernel]].

    **The construction.**
    - Written into the commutators `[b, a^-n b a^n]` of a shift-invariant Heisenberg group, a pair
      of recursively inseparable sets gives a computably presented group `Q_k` with a central `c`
      of order `k`. Every quotient keeping `c` alive has unsolvable word problem
      ([[inseparable-heisenberg-shift-group-poisons-its-center]]).
    - Feed `S *_{s=c} Q_k` to CK Theorem 3 with normal generator `s`. The output `Gamma` is
      finitely presented, has property (T), contains `S`, and has `Gamma = <<s>>`.
    - Core survival keeps `c = s` alive in every proper quotient. So every nontrivial quotient is
      undecidable and no maximal kernel is even r.e.
    - The same holds for the marked Steinberg cover with this `Gamma` as its marking.

    **Where the old approaches die, and what survives.**
    - This corrects Attempt 4. The effective maximal kernel is not a different target: it is a
      **necessary prerequisite** that can fail on its own. It fails exactly when a core element is
      WP-poisoned in some finitely generated subgroup.
    - Every approach that uses only the envelope's hypotheses dies at the final
      `Gamma/M`-finitely-presented step. Those hypotheses are finite presentation, (T), normal
      generation, perfectness, no finite quotients, and a Steinberg/elementary cover over an
      arbitrary finitely presented marking.
    - A tenable restatement must name the specific marking of
      `boone-higman-via-ck-maximal-kernel` (Clapham's decidable envelope, then a derived-subgroup
      host `T`). It must split into (a) some simple quotient of that cover has solvable word
      problem, and (b) such a quotient is finitely presented.
    - The existential version ("some envelope of `S` has an fng maximal kernel") is merely
      Boone--Higman for `S` again, taking the fp simple envelope itself with `M = 1`. So only the
      specific-object version carries content.
    - Whether `U = Z[T]<p,q>/(p(1-g)q-1)` or `T` for the clean marking contains a poisoned
      element is open.

12. **Calibrate on the binary Leavitt host, and transfer stable K_2 (bh-ck-kernel,
    09-18).** *Establishes a positive instance of the existential reading and one
    transfer lemma. The specific-object version stays OPEN.*
    - *Instance.* [[ck-hole-holds-for-perfect-binary-leavitt-unit-subgroups]]: for every
      perfect `S <= L_(F_2)(1,2)^x`, the marking `T = H = E_4(L)`, `g = e_12(1)` gives a CK
      marked Steinberg cover with a finitely normally generated maximal kernel (regime
      R4, quotient `PE_4(L) ≅ L^x`). By Attempt 11 this is Boone--Higman for `S` again,
      so it adds no new case; it confirms the four-regimes machinery end to end on one
      explicit host.
    - *Transfer.* Clause (b) of [[ck-sandwich-ring-has-fp-projective-simple-quotient]]
      fails whenever the image of `K_2(4,R) -> K_2(R)` is not finitely generated. So every
      stable symbol obstruction on main also excludes the ring as an R4 witness. Stable
      `K_1` obstructions do not transfer to clause (c), since that clause concerns unstable
      rank-four `K_1`.
    - *Where it stops.* For the Clapham marking of the route, a witness needs a finitely
      presented simple quotient ring of `U` whose stable `K_2` image from rank four is
      finitely generated and whose rank-four scalar `K_1` kernel is finitely generated.
      No such quotient is known, and no obstruction to one is known.
