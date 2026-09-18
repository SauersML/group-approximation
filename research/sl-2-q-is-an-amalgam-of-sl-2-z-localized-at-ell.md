---
rg: 2
id: sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell
kind: claim
title: For every prime l, SL_2(Q) is the amalgam of two conjugate copies of the residually finite group SL_2(Z_(l)) over Γ_0(l), so PSL_2(Q) acts faithfully and cocompactly on the (l+1)-regular tree
distinct_from:
  pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori: that uses the action of PGL_2(Q) on the boundary P^1(Q_p) of the tree, inside a Rover--Nekrashevych group; this uses the action on the tree itself, whose vertex and edge stabilizers give the amalgam.
  sl-n-q-is-colimit-of-lattice-stabilizers: that presents SL_n(Q) through all primes at once, as an infinite restricted-product diagram of copies of SL_n(Z); this localizes at ONE prime l, giving a single amalgam with two vertex groups SL_2(Z_(l)) that already contain every other prime.
  gl-n-q-fixes-a-vertex-in-free-splittings: that shows SL_n(Q) fixes a vertex whenever edge stabilizers are trivial; this is the tree with finite-index edge stabilizers, where SL_2(Q) fixes no vertex, as that node's Scope paragraph anticipates.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that is the Bux--Llosa Isenrich--Wu embedding theorem; this is an input group satisfying all its hypotheses except finite presentation of edge stabilizers.
artifacts:
  - research/artifacts/gq-gq-infinite-primes.md
---

**ESTABLISHED (literature import)** through
`sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell-citation` (Ihara's theorem,
Serre, *Trees*, Ch. II §1.4). The consequences below are lane-proved, not
independently reviewed.

**Statement.** Let `l` be a prime, `A = SL_2(Z_(l))`, `α = diag(1, l)`,
`A^α = α A α^-1` and `Γ_0(l) = {[[a,b],[c,d]] in A : c in l Z_(l)}`. Then
`A ∩ A^α = Γ_0(l)`, and the inclusions induce an isomorphism

    SL_2(Q) ≅ A *_{Γ_0(l)} A^α .

`Γ_0(l)` has index `l+1` in both factors (it is the preimage of a Borel subgroup
of `SL_2(F_l)`). So `SL_2(Q)` acts on its Bass--Serre tree, the `(l+1)`-regular
tree `T_l` of homothety classes of `Z_(l)`-lattices in `Q^2`, with one edge
orbit.

**Consequences.**
1. **BLIW class.** `SL_2(Q)` lies in the class `BS_G` of Bux--Llosa Isenrich--Wu
   (`bliw-locally-finite-tree-actions-embed-in-fp-simple-groups`) for
   `G = SL_2(Z_(l))`: its vertex and edge groups are commensurable with `G`, and
   its edge inclusions have finite index.
2. **Faithfulness.** The kernel of the action on `T_l` is normal and lies in `A`.
   `PSL_2(Q)` is simple (`PSL_2(K)` is simple for every field with more than 3
   elements), so the kernel is `{±I}`, and `PSL_2(Q)` acts faithfully and
   cocompactly on the locally finite tree `T_l`.
3. **The one missing hypothesis.** So `PSL_2(Q)` satisfies every hypothesis of
   BLIW Theorem B except finite presentation of the edge stabilizers. Those are
   `PΓ_0(l)`, which is not even finitely generated: it contains `[[1,1/q],[0,1]]`
   for every prime `q != l`, while a finitely generated subgroup has entries in
   some `Z[1/m]`. `sl-2-q-via-hecke-overgroup-and-bliw` turns exactly this gap
   into the hypothesis `sl-2-z-localized-has-fp-hecke-overgroup`.
4. **Divisibility at l is made by the amalgam.** A vertex group
   `A <= GL_2(Z_(l))` contains no element of infinite order with `l^j`-th roots
   for all `j` (`infinitely-q-divisible-dvr-matrices-are-torsion` with
   `O = Z_(l)`). Yet `(Q,+) <= SL_2(Q)` is `l`-divisible. So the `l`-part of
   divisibility, which O1 of `gl-n-q-embeds-in-fp-simple-group` makes fatal for
   residually finite hosts, comes from the tree, while all other primes live in
   the residually finite vertex groups (`aff-n-over-z-localized-at-ell-is-rf-and-self-similar`).
   The unipotent `(Q,+)` fixes an end of `T_l` and no vertex.
5. **n >= 3.** The same argument as `sl-n-q-is-colimit-of-lattice-stabilizers`,
   run with the single prime `l` and base ring `Z_(l)` in place of `Z`, presents
   `SL_n(Q)` as the colimit of a finite simplex of groups: `n` vertex groups
   conjugate in `GL_n(Q)` to `SL_n(Z_(l))`, with all local groups of finite index.
   This extension is not part of the present claim. It inherits that node's
   imports (I2, I3) and stays OPEN with it.
