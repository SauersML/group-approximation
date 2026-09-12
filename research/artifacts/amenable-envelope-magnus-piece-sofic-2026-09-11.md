# Amenable envelopes of the Magnus piece make one-relator groups sofic

Date: 2026-09-11. Written proof, not a Lean certificate. It generalizes the
peelable-extreme theorem
(`peelable-extreme-one-relator-sofic-2026-09-11.md`) and records where the
generalization must stop.

## 1. Statement

Keep the setting of the peelable-extreme artifact. `G = <a,t | w>` is
torsion-free, `t` has exponent sum zero in `w`, and `W_0(a_m,...,a_n)` is the
Magnus rewriting with `m < n`. Put

    B_0 = <a_m, ..., a_n | W_0>,
    F_- = <a_m, ..., a_(n-1)>,     F_+ = <a_(m+1), ..., a_n>.

By the Freiheitssatz both `F_-` and `F_+` are free on the displayed letters.

**Definition.** An **amenable envelope** of `(B_0, F_-)` is a group `B'` with an
injective homomorphism `iota: B_0 -> B'` such that `B'` is obtained from
`iota(F_-)` by finitely many steps of the following two kinds, each applied to
the group `Y` built so far:

* (E1) `Y -> Y *_E X`, where `E <= Y` is amenable and `X` is a sofic group
  containing a copy of `E`;
* (E2) `Y -> HNN(Y; theta: E -> E')`, where `E, E' <= Y` are amenable and
  `theta` is an isomorphism.

Define an amenable envelope of `(B_0, F_+)` in the same way.

**Theorem.** If `(B_0, F_-)` or `(B_0, F_+)` has an amenable envelope, then `G`
is sofic.

## 2. Two lemmas

**Lemma 2.1 (monotonicity).** Let `C <= A <= A'` and `C <= B <= B'`, with the
two copies of `C` identified. The natural map `A *_C B -> A' *_C B'` is
injective.

*Proof.* If `a in A` maps into `C` inside `A'`, then `a in C`, because `C <= A`
and `A -> A'` is injective. So reduced alternating words with syllables in
`A \ C` and `B \ C` map to reduced alternating words in `A' *_C B'`. By the
amalgam normal form theorem, nonempty reduced words represent nontrivial
elements. ∎

**Lemma 2.2 (envelope transport).** Let `S` be a sofic group, `F <= S`, and
`(B', iota)` an amenable envelope of `(B, F)`. Then `S *_F B'` is sofic and
contains `S *_F B` as a subgroup.

*Proof.* Write `F = Y_0 <= Y_1 <= ... <= Y_r = B'` for the envelope steps and
put `Z_i = S *_F Y_i`. The pushouts compose, so `Z_(i+1)` is `Z_i *_E X` in
case (E1) and `HNN(Z_i; theta)` in case (E2). The associated subgroups
embed in `Z_i` because `Y_i` does. `Z_0 = S` is sofic. Amalgams over amenable
subgroups (Elek--Szabo, arXiv:1010.3424, Theorem 1) and HNN extensions over
amenable associated subgroups (Ciobanu--Holt--Rees, arXiv:1212.2739,
Proposition 3.2) keep each `Z_i` sofic. Lemma 2.1 with `A = A' = S` and
`B <= B'` gives the subgroup statement. ∎

## 3. Proof of the theorem

Assume `(B_0, F_-)` has an amenable envelope; the `F_+` case is the same
argument with indices reversed. As in §4 of the peelable artifact, it suffices
to show every group

    S_q = < a_i (i <= n+q) | W_p, ..., W_q >

is sofic. Put `F_j = <a_(m+j),...,a_(n+j-1)>` and
`B_j = <a_(m+j),...,a_(n+j) | W_j>`. The index shift carries `(B_0, F_-)` to
`(B_j, F_j)`, so each `(B_j, F_j)` has an amenable envelope `B'_j`.

Define sofic groups `S'_j` with injective maps `psi_j: S_j -> S'_j`. Start from
`S'_(p-1) = S_(p-1)`, the free group on `{a_i : i <= n+p-1}`. The invariant is
that `a_(m+j+1),...,a_(n+j)` freely generate a free subgroup of `S_j`.

Step `j`. By the invariant and the Freiheitssatz,
`S_j = S_(j-1) *_(F_j) B_j` is a genuine amalgam. Put

    S'_j = S'_(j-1) *_(F_j) B'_j,

with `F_j` embedded through `psi_(j-1)`. Lemma 2.2 makes `S'_j` sofic.
Lemma 2.1 makes the natural map `psi_j: S_j -> S'_j` injective, since
`S_(j-1) -> S'_(j-1)` and `B_j -> B'_j` are injective and agree on `F_j`.
The invariant passes to `S_j` through the Freiheitssatz in `B_j`, which embeds
in `S_j`.

So each `S_q` embeds in a sofic group and is sofic. The truncations of the
Magnus kernel are free products of such groups with free groups, the kernel is
their directed colimit, and `G` is sofic. ∎

## 4. Examples beyond peeling

1. **Peelable extremes.** When the top letter forms one syllable, or two
   syllables of equal absolute exponent, `B_0` is itself an envelope of
   `(B_0, F_-)`: cyclic root amalgams and cyclic HNN extensions are steps (E1)
   and (E2).
2. **Nested conjugators.** Let `U, X, Z` be nontrivial words in `F_-`, and
   `c = a_n U a_n^(-1)`. The relator

       W_0 = c X c^(-1) Z = a_n U a_n^(-1) X a_n U^(-1) a_n^(-1) Z

   has four top syllables, so it is unpeelable. But `B_0` is obtained from
   `F_-` by the cyclic HNN extension `<F_-, c | c X c^(-1) = Z^(-1)>` followed
   by the cyclic HNN extension `a_n U a_n^(-1) = c`. Eliminating `c` recovers
   `W_0`. So `B_0` is an envelope of itself, and `G` is sofic.
3. **Iterated nesting.** Any relator obtained by repeatedly substituting
   cyclic-HNN or root expressions for coefficients has an envelope of the
   same shape.

## 5. A necessary condition, and where envelopes stop

**Proposition 5.1.** Suppose `n - m >= 2` and `B_0` is not free. If
`(B_0, F_-)` has an amenable envelope, then `B_0` has a nontrivial splitting
as a graph of groups whose edge groups are amenable subgroups of `B_0`, in
which `F_-` lies in a vertex group.

*Proof.* Let `Y_0 <= ... <= Y_r = B'` be the envelope steps, and let `k` be
the least index with `iota(B_0) <= Y_k`. Since `Y_0 = iota(F_-)` is free and
`B_0` is not, `k >= 1`. The step from `Y_(k-1)` to `Y_k` gives an action of `Y_k`
on a Bass--Serre tree with amenable edge stabilizers, and `Y_(k-1)` is the
stabilizer of a vertex `v_0`. Suppose `iota(B_0)` fixes a vertex `u`. Then
`F_- <= B_0` fixes `u` and `v_0`. If `u != v_0`, `F_-` fixes the edges between
them and so is amenable, which is impossible for a free group of rank
`n - m >= 2`. If `u = v_0`, then `iota(B_0) <= Y_(k-1)`, contradicting the choice
of `k`. So the finitely generated group `B_0` acts on the tree without a global
fixed point. Bass--Serre theory gives a nontrivial splitting of `B_0` whose edge
groups are intersections of `B_0` with edge stabilizers, hence amenable, and
`F_-`, which fixes `v_0`, lies in a vertex group. ∎

So envelopes cannot reach a Magnus piece that is rigid relative to its Magnus
subgroup: one with no splitting over an amenable subgroup in which `F_-` is
elliptic, as for a one-ended hyperbolic piece with trivial relative JSJ
decomposition. Such pieces are virtually special with quasiconvex, hence
separable, Magnus subgroups. The complementary mechanism would be profinite
gluing along separable free subgroups, and no sofic permanence theorem with
that hypothesis is available. That is the exact wall between this method and
the open class.
