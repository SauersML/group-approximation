import GroupApproximation.Higman.TransportStar

/-!
# What blocks a hand-built direct-product witness for the conjugator graph

`Higman.Star.ConjugatorGraph` (`Higman/TransportStar.lean`) asks for
`BenignTF Star.graphSub`, where `graphSub = ⟨(a^h, h) : h ∈ K⟩ ≤ F₃ × F₃` is the
graph of the un-conjugation.  Everything else in Higman's Section 5 is proved
there; this is the one residual.

The attractive first attempt is to build its witness **by hand as a direct
product, with nothing glued** --- imitating `Higman.BenignWitness.ker`
(`Benign.lean:239`), whose overgroup is `G × B`, whose embedding is
`MonoidHom.inl`, and whose finitely generated `L` is *already a graph*
(`Benign.lean:247`), so that no amalgam and no finite-generation hypothesis on
a glued subgroup is needed.  That attempt does not go through in any of the
shapes this repository's direct-product machinery offers, and this file records
what blocks each of them, so the next reader does not spend the same time.

Stated exactly, so the scope is not overread: obstructions 1 and 2 below are
proved, and each closes off one specific shape --- the `ker` pattern, and the
seed-orbit pattern that `Higman/RowSubgroup.lean` uses.  Obstruction 3 is an
argument on paper about a presentation.  Together they cover every construction
I could see; they do **not** amount to a proof that no finitely generated `L`
exists, and no such proof is claimed --- indeed `graphSub` is recursively
enumerable, so Higman's theorem says a witness does exist.

**Nothing here is a new leaf.**  Every declaration is a proved theorem, and the
residual in `TransportStar.lean` is left exactly as it stands.

## The three obstructions

**1.  `graphSub` is not normal** (`not_normal_graphSub`).  So it is not a kernel,
and the `BenignWitness.ker` pattern --- whose `comap` along `inl` is by
construction the kernel of the homomorphism whose graph is `L` --- cannot
produce it, however the homomorphism is chosen.  The witness is explicit:
`(a,1)` lies in `graphSub` but its conjugate `(a^b, 1)` does not
(`conj_seed_notMem_graphSub`), because the first coordinate determines the word
by `Conj.cbHom_injective` and that word's second coordinate is `b ≠ 1`.

**2.  Conjugation cannot move the second coordinate off `1`**
(`snd_eq_one_of_conj`, `eq_one_of_conj_genPair`).  In *any* overgroup `P` of
`F₃ × F₃` that still admits a homomorphism `Q₂ : P →* F₃` restricting to the
second projection, a conjugate of any element with trivial second coordinate
again has trivial second coordinate.  The seed `genPair 1 = (a, 1)` has trivial
second coordinate and `genPair k` has second coordinate `k`, so no conjugate of
the seed is `genPair k` unless `k = 1`.

This is what kills the `Higman/RowSubgroup.lean` device at this subgroup.  There
the whole generating family is the orbit `t^i b t^{-i}` of a *single* base
element under a stable letter, and the collecting process works because that
orbit is the family.  Here the family `{(a^h, h)}` cannot be an orbit of one
seed under conjugation by anything, in any overgroup keeping the second
projection.

Note what this does **not** say.  For a finitely generated `L` with `L / ker`
free, the extension splits and `ker (Q|_L)` is the normal closure of finitely
many elements, so its generators are conjugates of finitely many seeds and their
second coordinates lie in finitely many conjugacy classes --- but that is *not*
by itself a contradiction, because a free group of infinite rank can perfectly
well be the normal closure of one element, and `graphSub` need not be generated
by the `genPair k` in such a witness.  The decisive statement is the narrow
formalized one: the *seed-orbit* shape, which is the one `RowSubgroup` uses and
the one to reach for here, is unavailable.  Ruling out every finitely generated
`L` would need a different argument, and I do not have one.

**3.  The natural repair collapses the group.**  Argued on paper, not
formalized, since it is a statement about a presentation rather than about a
group in the repository.  To get past obstruction 2 one adds a letter `ν` that
does not normalise `F₃ × F₃`, asks for `ν⁻¹ (a,1) ν = (a^b, b)`, and asks for `ν`
to commute with `K × K` --- which is exactly enough to make
`ν⁻¹ (a^h, h) ν = (a^{bh}, bh)` follow for *every* `h` from that one relation,
so the presentation stays finite.  It is also inconsistent: `ν` commutes with
`(1,c)` and `(a,1)` commutes with `(1,c)`, so `(a^b, b) = ν⁻¹ (a,1) ν` must
commute with `ν⁻¹ (1,c) ν = (1,c)`, which forces `[b, c] = 1` and collapses `F₃`.
Weakening the commutation is not available: both `ν⁻¹ (h,1) ν = (h,1)` and
`ν⁻¹ (1,h) ν = (1,h)` are used in that derivation, the second to supply the `h`
in the second coordinate of the answer.

Two further remarks, also on paper.  No automorphism of `F₃ × F₃` sends `(a,1)`
to `genPair k` for `k ≠ 1`, since every automorphism preserves or swaps the two
factors and so sends `(a,1)` to an element with a trivial coordinate.  And the
index shift `(a^h, h) ↦ (a^{hb}, hb)` --- which *is* an automorphism of
`graphSub`, because `graphHom_injective` makes the pairs a free basis and
`h ↦ h b` permutes the index set --- extends to no endomorphism of `F₃ × K`,
the natural finitely generated subgroup containing `graphSub`: writing the
second component of such an endomorphism as `u(x) v(y)` with commuting images,
`u(a) = b` forces both images into `⟨b⟩` (abelian subgroups of a free group are
cyclic and `b` is not a proper power), whence `h ∈ ⟨b⟩` for every `h ∈ K`, false
at `c`; and if `v` is trivial then `u(h)⁻¹ b u(h) = h b` makes `b` conjugate to
`c b`, false since conjugacy preserves the abelianised `c`-exponent.

## What this leaves

Route (1) is closed in the shapes the repository's direct-product machinery
offers.  What survives is the reduction recorded in `TransportStar.lean`'s "what
is left": `graphSub` is benign *in* `FreeGroup ↥K × F₃` by a `comap` of the
finitely generated diagonal, and the missing step is the passage from there to
`F₃ × F₃` along an injective map whose source is not finitely generated ---
`BenignTF.mapEmb` without `[Group.FG G]`, equivalently "benign in benign is
benign".  That is a question about the benign calculus rather than about this
subgroup, and it should be settled *at* `BenignTF` --- with the torsion-free
witness --- before anyone states it as a leaf, since the amalgam that
`mapEmb` builds is exactly what the finite-generation hypothesis is paying for.
-/

namespace GroupApproximation
namespace Higman
namespace Star

open GroupApproximation.Higman.Conj

/-! ## 1.  The graph is not normal -/

theorem mem_graphSub_genPair (h : ↥K) : genPair h ∈ graphSub :=
  mem_graphSub.mpr ⟨FreeGroup.of h, graphHom_of h⟩

/-- **A conjugate of the seed leaves the graph.**  `(a, 1)` lies in `graphSub`
and `(a^b, 1)` does not: the first coordinate determines the word by
`Conj.cbHom_injective`, and that word has second coordinate `b`, not `1`. -/
theorem conj_seed_notMem_graphSub : ((b⁻¹ * a * b, (1 : F₃)) : F₃ × F₃) ∉ graphSub := by
  intro hmem
  obtain ⟨w, hw⟩ := mem_graphSub.mp hmem
  have h1 : cbHom w = b⁻¹ * a * b := congrArg Prod.fst hw
  have h2 : evalHom w = (1 : F₃) := congrArg Prod.snd hw
  have hb : cbHom (FreeGroup.of (⟨b, b_mem_K⟩ : ↥K)) = b⁻¹ * a * b := cbHom_of _
  have hwb : w = FreeGroup.of (⟨b, b_mem_K⟩ : ↥K) := cbHom_injective (h1.trans hb.symm)
  rw [hwb, evalHom_of] at h2
  exact b_ne_one h2

/-- **The conjugator graph is not normal**, so it is not a kernel, and the
direct-product witness of `Higman.BenignWitness.ker` --- whose `comap` is by
construction a kernel --- cannot produce it for any choice of homomorphism. -/
theorem not_normal_graphSub : ¬ graphSub.Normal := by
  intro hnorm
  have hseed : genPair (1 : ↥K) ∈ graphSub := mem_graphSub_genPair 1
  have hconj := hnorm.conj_mem _ hseed ((b⁻¹, (1 : F₃)) : F₃ × F₃)
  have heq : ((b⁻¹, (1 : F₃)) : F₃ × F₃) * genPair (1 : ↥K)
      * ((b⁻¹, (1 : F₃)) : F₃ × F₃)⁻¹ = ((b⁻¹ * a * b, (1 : F₃)) : F₃ × F₃) := by
    refine Prod.ext ?_ ?_
    · show b⁻¹ * ((1 : F₃)⁻¹ * a * (1 : F₃)) * (b⁻¹)⁻¹ = b⁻¹ * a * b
      group
    · show (1 : F₃) * (1 : F₃) * (1 : F₃)⁻¹ = (1 : F₃)
      group
  rw [heq] at hconj
  exact conj_seed_notMem_graphSub hconj

/-! ## 2.  Conjugation cannot move the second coordinate off `1` -/

/-- **The second-coordinate obstruction.**  In any overgroup of `F₃ × F₃` that
still carries the second projection, a conjugate of an element with trivial
second coordinate again has trivial second coordinate. -/
theorem snd_eq_one_of_conj {P : Type} [Group P] (emb : F₃ × F₃ →* P) (Q₂ : P →* F₃)
    (hQ : ∀ z : F₃ × F₃, Q₂ (emb z) = z.2) (g : P) (x y : F₃ × F₃) (hx : x.2 = 1)
    (hconj : g⁻¹ * emb x * g = emb y) : y.2 = 1 := by
  have h := congrArg Q₂ hconj
  rw [map_mul, map_mul, map_inv, hQ x, hQ y, hx, mul_one, inv_mul_cancel] at h
  exact h.symm

/-- **No conjugate of the seed is a graph generator.**  `genPair 1 = (a, 1)` has
trivial second coordinate and `genPair k` has second coordinate `k`, so the
generating family of `graphSub` is not the conjugation orbit of one element in
any overgroup keeping the second projection.

This is the obstruction that stops `Higman/RowSubgroup.lean`'s device from being
re-run here: there the generating family *is* the orbit `t^i b t^{-i}` of one
base element under a stable letter, and the collecting process runs on exactly
that. -/
theorem eq_one_of_conj_genPair {P : Type} [Group P] (emb : F₃ × F₃ →* P) (Q₂ : P →* F₃)
    (hQ : ∀ z : F₃ × F₃, Q₂ (emb z) = z.2) (g : P) (k : ↥K)
    (hconj : g⁻¹ * emb (genPair 1) * g = emb (genPair k)) : (k : F₃) = 1 := by
  have hx : (genPair (1 : ↥K)).2 = 1 := rfl
  exact snd_eq_one_of_conj emb Q₂ hQ g _ _ hx hconj

end Star
end Higman
end GroupApproximation
