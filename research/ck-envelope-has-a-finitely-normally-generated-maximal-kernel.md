---
rg: 2
id: ck-envelope-has-a-finitely-normally-generated-maximal-kernel
kind: claim
title: The finitely presented normal-generator envelope has a maximal proper normal subgroup that is finitely normally generated
distinct_from:
  finite-infranormal-subgroup-is-normal: that is the elementary fact that a FINITE infranormal subgroup is normal, about conjugation preserving cardinality; this asks for a finite NORMAL GENERATING SET of a maximal normal subgroup, which is a condition on generating data rather than on the subgroup's size -- the kernel here is expected to be infinite.
  fp-quotient-iff-kernel-finitely-normally-generated: that is the general equivalence between finite presentability of a quotient and finite normal generation of its kernel, true for every finitely presented group; this asserts that one particular class of envelopes actually HAS such a kernel at a maximal element, which is the open existence statement the equivalence turns the conjecture into.
  boone-normal-closure-of-t-finitely-generated: that concerns the Boone HNN tower and finite generation of a normal closure AS A SUBGROUP; this concerns finite NORMAL generation of a maximal normal subgroup of an elementary matrix group, a different group, a different construction and a strictly weaker finiteness condition.
  every-nontrivial-core-element-normally-generates-the-envelope: that records how rigid the envelope is -- perfect, no finite quotients, every core element a normal generator; this asks for a compactness property of its normal lattice, and the audit found no implication from the rigidity clauses to this one.
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
