import GroupApproximation.Higman.BenignAmbient

/-!
# The finite-generation hypothesis in `mapEmb` cannot be dropped

`Higman.BenignWitness.mapEmb` (`Higman/BenignAmbient.lean:82`) is the image half
of Higman's Lemma 3.3:

> if `H` is benign in `G` and `θ : G ↪ N` embeds `G` in a finitely presented
> group, then `θ(H)` is benign in `N`,

and it carries two hypotheses beyond the statement: `[Group.IsFinitelyPresented N]`,
which is part of the notion, and `[Group.FG G]`, which is not.  The second is
there only because the witness is the amalgam `K *_G N` of the old witness with
the new ambient group, and `Amalgam.isFinitelyPresented_push`
(`Higman/AmalgamPushout.lean:173`) needs the glued subgroup finitely generated.

That looks like bookkeeping, and it is tempting to try to remove it --- in
particular for the case where `θ` is an *inclusion* of a subgroup, where the
image already sits inside the target and nothing appears to need gluing.  It
cannot be removed, in that case or any other, and this file proves it.

## The counterexample shape

The point is that **every subgroup is benign in itself**.  If `G` embeds in a
finitely presented group at all, then `⊤ : Subgroup G` has a benign witness ---
take the overgroup to be that finitely presented group and take `L = ⊤`, which
is finitely generated because a finitely presented group is finitely generated
(`benignWitness_top`).  Nothing about `G` is used, and `G` is arbitrary.

So feed `mapEmb`-without-`[Group.FG G]` the subgroup `⊤ ≤ S` for an arbitrary
subgroup `S` of an arbitrary finitely presented `N`, along the inclusion
`S.subtype`, which is injective and is exactly the "no gluing needed" case.  The
image of `⊤` is `S`, so the conclusion is that **every subgroup of every finitely
presented group is benign** (`benign_of_mapEmb_dropFG`).

That is absurd, by the classical argument, which is not formalized here because
it is about recursive enumerability rather than about groups.  A benign subgroup
is recursively enumerable: it is `L ∩ N` for a finitely generated `L` in a
finitely presented `P`, membership in `L` is recursively enumerable because one
can enumerate products of its generators and equality in a finitely presented
group is recursively enumerable, so `{n ∈ N | n ∈ L}` is recursively enumerable.
But a free group of rank two has continuum many subgroups --- it contains a free
subgroup of countably infinite rank, and distinct subsets of a basis generate
distinct subgroups --- while there are only countably many recursively
enumerable sets.  So most subgroups of `F₂` are not benign.

`[Group.FG G]` is therefore load-bearing, and the shape of what it buys is now
visible: with `G` finitely generated, `mapEmb` gives `θ(H)` benign in `N` with
**no hypothesis relating `G` to `N`** beyond the embedding, and that strength is
exactly what fails without it.

## What the true statement is instead

The statement that survives is transitivity, with the missing hypothesis put
back:

> if `H ≤ G ≤ N` with `N` finitely presented, `H` benign in `G` **and `G` benign
> in `N`**, then `H` benign in `N`.

That is true --- it follows from the recursive-enumerability characterization,
by composing the two enumerations --- and it is what the counterexample above
respects, since in it `S` is an arbitrary subgroup and so `G = S` is exactly the
thing not assumed benign.

It is also not available cheaply.  Its natural proof is the same amalgam:
in `P = K₁ *_G K₂` the normal form gives `K₁ ∩ K₂ = G`, so the witness `L₁` for
`H` in `G` satisfies `L₁ ∩ N ≤ K₁ ∩ K₂ = G` and hence `L₁ ∩ N = L₁ ∩ G = H`,
and `L₁` is already finitely generated --- but `P` is finitely presented only
when `G` is finitely generated, which is the hypothesis we were trying to
remove.  So transitivity for a non-finitely-generated middle group is open in
this repository, and dropping `[Group.FG G]` is not the way to it.

**Nothing here is a new leaf.**  `benign_of_mapEmb_dropFG` takes the
hypothesis-drop as an explicit binder and derives an absurd conclusion from it;
it inhabits nothing and asserts nothing about the repository's own `mapEmb`,
which keeps its hypothesis and stays true.
-/

namespace GroupApproximation
namespace Higman

/-! ## 1.  Every subgroup is benign in itself -/

/-- **Every subgroup is benign in itself.**  If `G` embeds in a finitely
presented group at all, `⊤ : Subgroup G` has a benign witness: the overgroup is
that finitely presented group and the finitely generated subgroup cutting `⊤`
out is the whole of it.

Nothing about `G` is used --- in particular `G` is not assumed finitely
generated, finitely presented, or benign anywhere. -/
def benignWitness_top {G N : Type} [Group G] [Group N] [Group.IsFinitelyPresented N]
    (θ : G →* N) (hθ : Function.Injective θ) : BenignWitness (⊤ : Subgroup G) where
  K := N
  emb := θ
  emb_injective := hθ
  L := ⊤
  L_fg := by
    obtain ⟨X, hX, hXfin⟩ :=
      Group.fg_iff.mp (ProductFinitePresentation.fg_of_isFinitelyPresented N)
    exact (Subgroup.fg_iff _).mpr ⟨X, hX, hXfin⟩
  comap_eq := Subgroup.comap_top θ

theorem benign_top_of_embedding {G N : Type} [Group G] [Group N]
    [Group.IsFinitelyPresented N]
    (θ : G →* N) (hθ : Function.Injective θ) : Benign (⊤ : Subgroup G) :=
  ⟨benignWitness_top θ hθ⟩

/-! ## 2.  Dropping the hypothesis makes everything benign -/

/-- **`[Group.FG G]` cannot be dropped from `BenignWitness.mapEmb`.**  Assume the
image half of Lemma 3.3 without it.  Then every subgroup of every finitely
presented group is benign --- apply the assumption to `⊤ ≤ S` along the
inclusion `S.subtype`, which is injective, and whose image is `S`.

The inclusion case is the one this rules out most sharply: `θ` here is a
subgroup inclusion, the case where the image already lies in the target and no
gluing appears to be needed.  See this file's header for why the conclusion is
absurd, and for the statement that survives. -/
theorem benign_of_mapEmb_dropFG
    (hdrop : ∀ {G N : Type} [Group G] [Group N] [Group.IsFinitelyPresented N]
      {H : Subgroup G}, BenignWitness H → ∀ θ : G →* N, Function.Injective θ →
        Benign (H.map θ))
    {N : Type} [Group N] [Group.IsFinitelyPresented N] (S : Subgroup N) : Benign S := by
  have hinj : Function.Injective S.subtype := fun _ _ h => Subtype.ext h
  have h := hdrop (benignWitness_top S.subtype hinj) S.subtype hinj
  have hmap : (⊤ : Subgroup ↥S).map S.subtype = S := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rwa [hmap] at h

end Higman
end GroupApproximation
