---
rg: 2
id: hyperbolic-rf-kernel-confines-residual-to-centralizer
kind: claim
title: A residually finite infinite normal kernel confines the finite residual of a hyperbolic group to the kernel's finite centralizer
distinct_from:
  leavitt-kazhdan-cover-rf-iff-kernel-rf: that treats covers of the binary Leavitt unit group and uses an acyclic quotient with no finite quotients; this holds for every finitely generated infinite normal subgroup of every hyperbolic group, over any quotient, and bounds the residual itself instead of equating completions.
  acyclic-quotientless-extension-completion-is-kernel-completion: that computes finite quotients and completions of an extension over an acyclic quotientless base; this makes no hypothesis on the quotient at all and concerns only where the finite residual can sit.
  rips-kernel-target-iff-hyperbolic-nonrf: that equates the finite-quotient-free Rips kernel target with Gromov's question; this proves that in a hyperbolic extension the base never contributes an invisible element outside a finite normal subgroup unless the kernel is itself not residually finite.
  finite-hyperbolic-residual-iff-persistent-class: that classifies counterexamples with finite nontrivial residual; this shows every counterexample with a residually finite infinite finitely generated normal subgroup is of that finite-residual shape.
---

**ESTABLISHED.** Let `G` be a non-elementary word-hyperbolic group and let
`N` be an infinite, finitely generated, normal subgroup of `G`. Write
`R(X)` for the finite residual of a group `X`, and `C_G(N)` for the
centralizer of `N`.

1. **Kernel trace.** `R(G) ∩ N` is contained in
   `Z_f(N) = { n in N : [n,x] in R(N) for all x in N }`, the preimage of
   the center of `N/R(N)`. No hypothesis on `G/N` is used.
2. **Finite centralizer.** `C_G(N)` is a finite normal subgroup of `G`.
3. **Confinement.** If `N` is residually finite, then `R(G) ⊆ C_G(N)`.
   In particular `R(G)` is finite.
4. **Torsion-free circularity.** If `G` has no nontrivial finite normal
   subgroup (for instance `G` torsion-free), then `G` is residually finite
   iff `N` is.

**Consequences for Gromov's question.**

- **Rips extensions.** Take any hyperbolic Belegradek--Osin extension
  `1 -> N -> G -> Q -> 1`, over any finitely presented `Q`. This includes
  quotientless, acyclic, Deligne-type and non-residually-finite `Q`. The
  kernel `N` is finitely generated, being a quotient of the input. It is
  infinite whenever `Q` is not word-hyperbolic, because a finite kernel would
  make `Q` quasi-isometric to `G`. An elementary `G` is residually finite
  anyway.
  - If `N` is residually finite, `R(G)` is finite.
  - If `G` is torsion-free, `G` fails residual finiteness exactly when `N`
    does, and then `N` is already a non-residually-finite subgroup.
  - Every infinite-order invisible element, and every infinite residual, of
    such a `G` is forced by a non-residually-finite kernel. The Schur classes
    in `Hom(H_2 Q, Z(N/M))`, which decide which kernel images are finite
    quotients of `G`, never add invisibility beyond item 1.
- **Torsion-free transfer.** The "Rips construction over the Kazhdan shape"
  attempt on [[torsion-free-non-residually-finite-hyperbolic-group]] is
  circular for every base, not only for the quotientless base: a
  torsion-free Rips total group is a counterexample iff its finitely
  generated kernel is not residually finite.
- **Infinite residuals.** A hyperbolic counterexample `G` with infinite
  `R(G)` has **every** infinite finitely generated normal subgroup not
  residually finite. A counterexample with one residually finite such
  subgroup has `1 < |R(G)| < infinity`. It therefore falls under
  [[finite-hyperbolic-residual-iff-persistent-class]].
- **Calibration.** In the Rips central pullback `P` of
  [[non-rf-hyperbolic-via-central-rips-pullback]], the invisible central
  element lies in `C_P(N)`, as item 3 requires. The infiniteness
  hypothesis on `N` cannot be dropped without the conclusion becoming the
  open question itself. Outside the hyperbolic class, a perfect central
  extension `1 -> C_p -> E -> Q -> 1` of a quotientless perfect `Q` has
  `R(E) = E` with `N = C_p` residually finite; see the proof, Step 5.

Proof in `hyperbolic-rf-kernel-confines-residual-to-centralizer-proof`.
The confinement is Baumslag's theorem that the automorphism group of a
finitely generated residually finite group is residually finite, combined
with the finiteness of centralizers of infinite normal subgroups in
hyperbolic groups. It is elementary and makes no historical novelty claim.
Its content for this graph is the exact scope it gives the Rips family.
It does not construct a counterexample.
