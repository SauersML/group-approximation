---
rg: 2
id: almost-v-fw-subgroups-act-through-finitely-many-germs
kind: claim
title: An FW group of Cantor homeomorphisms that are locally in V off finite sets virtually acts, modulo a subgroup of V, through its germs at finitely many fixed points
distinct_from:
  fw-subgroups-of-eventually-similar-groups-virtually-embed: that treats groups acting by eventually H-similar maps on all deep cones, with no singular points; this treats groups whose elements are locally in V except at finitely many points with arbitrary germs there (finite germ extensions of V such as VA and the shell groups), and puts the FW group into the germ groups at those points.
  shell-cantor-embeddings-are-finite-germ-extensions: that embeds every countable group in a finite germ extension of V; this is a necessary condition on where an FW subgroup of any such extension must live.
  germ-extensions-omit-standard-gl-n-q: that excludes standard analytic copies of GL_n(Q) from groups locally in a piecewise-projective group; this constrains arbitrary copies of FW groups in groups locally in V.
  normal-germ-extensions-of-thompson-v-contain-no-sl3z: its Theorem A puts a finite-index subgroup of SL_3(Z) into a finite product of germ groups of a Belk--Hyde--Matucci finite germ extension of V_{d,r}, through a fixed vertex of the CAT(0) germ complex; this treats every FW group, in the whole group H of almost-V homeomorphisms (no germ complex and no finiteness axioms), and gives the kernel of the germ map as a subgroup of a conjugate of V.
---

**ESTABLISHED** through `almost-v-fw-germ-reduction-proof` (lane-proved, not
independently reviewed; the method is the standard commensurated-subset
argument, and no novelty is claimed for it).

## Setting

- `C = {0,1}^N` is the Cantor set and `V <= Homeo(C)` is Thompson's group.
- A homeomorphism `g` of `C` is **V-local at** `x` if some `v in V` agrees with
  `g` on a neighbourhood of `x`. Its **singular set** `sing(g)` is the set of
  points where `g` is not V-local.
- `H = {g in Homeo(C) : sing(g) is finite}`. It is a group, since
  `sing(fg) ⊆ sing(g) ∪ g^-1(sing f)` and `sing(g^-1) = g(sing g)`. Every finite
  germ extension of `V` in the sense of Belk--Hyde--Matucci (arXiv:2407.03149),
  including `VA` and every shell group `E_nu`, is a subgroup of `H`.
- For `y in C`, `𝒢_y` is the group of germs at `y` of homeomorphisms fixing
  `y`. For a subgroup `E <= H`, the isotropy germ group `(E)_y` is the image of
  `Stab_E(y)` in `𝒢_y`.

## Statement

Let `Γ <= H` have property FW: every commensurated subset of every `Γ`-set is
transfixed. Property (T) implies FW.

1. **Germ reduction.** There are a finite-index subgroup `Γ_0 <= Γ`, a finite
   set `F ⊂ C` fixed pointwise by `Γ_0`, and `h in H` such that `h^-1 γ h` is
   V-local at every point outside `h^-1(F)` for every `γ in Γ_0`. Hence the
   germ homomorphism

       φ : Γ_0 -> ∏_{y in F} (Γ_0)_y ,   γ -> ([γ]_y)_{y in F}

   has kernel contained in `h V h^-1`.
2. **Kazhdan inputs.** If `Γ` is infinite and has property (T), then `F` is
   nonempty and some `y in F` has infinite germ image `[Γ_0]_y ⊆ (E)_y` for
   every `E <= H` containing `Γ`.

So an infinite Kazhdan subgroup of a finite germ extension of `V` cannot live
in the V-local part. A finite-index subgroup of it acts with infinite image on
the germs at a point it fixes.

## Consequences

- **Kazhdan germs.** If the Kazhdan group has only trivial or finite-index
  normal subgroups in each finite-index subgroup (a higher-rank lattice with
  trivial centre, by Margulis's normal subgroup theorem), then `φ` and one of
  its coordinates are injective on `Γ_0`, so a single isotropy germ group
  `(E)_y` contains `Γ_0`. That group is then neither amenable nor a-T-menable,
  so it lies in no `nV` (`brin-thompson-groups-nv-are-a-t-menable`). For
  `SL_3(Z)` this recovers, inside `H`, Theorem A of
  `normal-germ-extensions-of-thompson-v-contain-no-sl3z`. The case of `GL_n(Q)`
  is `gl-n-q-almost-v-hosts-need-lattice-germs`.
- **Scope.** The statement is about `H`, so it covers every finite germ
  extension of `V` at once, finitely presented or not. It is a transfer
  statement: a germ-extension host brings an FW input no closer to finite
  presentation than its isotropy germ groups already are.
- **Other bases.** The proof uses three facts about `V`:
  - it is full (a homeomorphism locally in `V` everywhere is in `V`);
  - any two nonempty clopen proper subsets of `C` admit a bijection that is
    locally in `V`;
  - its FW subgroups are finite.

  With the third fact dropped, parts 1 and the kernel statement hold for any
  base with the first two, for example `nV` on `C^n`.
