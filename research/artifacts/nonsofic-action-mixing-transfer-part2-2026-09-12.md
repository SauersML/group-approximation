# Mixing transfer for nonsofic actions, part 2: the theorem (2026-09-12)

Continues `research/artifacts/nonsofic-action-mixing-transfer-2026-09-12.md` (imports in Section 1,
Lemmas LC, ED, EQ in Sections 2-4). Lane `ex-nonsofic-action-relative`. Unreviewed at landing time.

## 5. THEOREM MT

**THEOREM MT.** Let `H` be a second countable locally compact group with the Howe--Moore property
(Ciobotaru Definition 2.6), `Γ <= H` a lattice, and `Γ ↷ (Z,ζ)` an ergodic p.m.p. action that is not
sofic. Put `Z' = Z × ({0,1},fair)^Γ` (diagonal action) and `W = H ×_Γ Z'`, with `H` acting on the left.
Then the restriction `Γ ↷ W` is essentially free, mixing, and not sofic.

*Proof.*

**Step 1 (the seed `Z'`).** `Γ` is infinite: a nonsofic action forces `Γ` nonamenable (Păunescu
Proposition 3.4). So the Bernoulli factor `B = ({0,1},fair)^Γ` is essentially free and mixing.

* `Z'` is essentially free, since a point fixed by `γ ≠ 1` has its `B`-coordinate fixed by `γ`.
* `Z'` is not sofic: `Z` is a factor (Lemma A).
* `Z'` is ergodic. `L²_0(Z × B) = (L²_0(Z) ⊗ 1) ⊕ (L²(Z) ⊗ L²_0(B))`. On elementary tensors of the
  second summand, `⟨γ(a⊗b), a'⊗b'⟩ = ⟨γa,a'⟩⟨γb,b'⟩ → 0` as `γ → ∞`, because `B` is mixing. By density
  and uniform boundedness every matrix coefficient of that summand tends to `0`. An invariant vector `ξ`
  has constant coefficient `‖ξ‖²` and `Γ` is infinite, so the second summand has no invariant vectors.
  The first has none because `Z` is ergodic.

**Step 2 (the coupling).** `H` is unimodular because it has a lattice, so Haar measure `m_H` is left and
right invariant. On `Ω = H × Z'` with `m = m_H ⊗ ζ'`, two copies of `Γ` act by

```text
Γ_ℓ :  γ · (h, z) = (γ h, z),          Γ_r :  γ ∗ (h, z) = (h γ^(−1), γ z).
```

They commute and preserve `m`, and both are free. Let `D ⊆ H` be a Borel set meeting each coset `hΓ`
exactly once, and `D' ⊆ H` one meeting each `Γh` exactly once. Both have Haar measure `c = covol(Γ)`,
because inversion exchanges them. So `X_r = D × Z'` is a fundamental domain for `Γ_r`, `X_ℓ = D' × Z'`
one for `Γ_ℓ`, and `m(X_r) = m(X_ℓ) = c < ∞`. The quotients are

```text
W = Ω / Γ_r  ≅ X_r   with the action of Γ_ℓ (restriction of the H-action),
V = Γ_ℓ \ Ω  ≅ X_ℓ  = Γ\H × Z'   with Γ_r acting diagonally:  γ ∗ (Γh, z) = (Γ h γ^(−1), γ z).
```

**Step 3 (`V` is free and not sofic).** If `γ ∗ (Γh, z) = (Γh, z)` then `γ z = z`, so `γ = 1` off a null
set. The projection `(Γh, z) ↦ z` is a `Γ_r`-equivariant, measure-preserving factor map onto `Z'` (with
`m` normalized on `X_ℓ`). So `V` is not sofic by Lemma A and Step 1.

**Step 4 (`W` is free).** `[h,z]` denotes the class of `(h,z)` under `Γ_r`. If `γ·[h,z] = [h,z]`, there
is `δ ∈ Γ` with `(γh, z) = (hδ^(−1), δz)`. Off the `Γ_r`-invariant null set `H × {z : Stab(z) ≠ 1}`
this forces `δ = 1`, hence `γh = h` and `γ = 1`.

**Step 5 (`W` is mixing).** First, `H ↷ W` is ergodic. An `H`-invariant measurable set of `W` pulls back
to a set `E ⊆ H × Z'` that is `Γ_r`-invariant and satisfies `m(gE Δ E) = 0` for all `g ∈ H`. By Fubini,
for `ζ'`-a.e. `z` the section `E_z ⊆ H` is invariant mod null under a.e. `g ∈ H`. The set of such `g` is a
conull subgroup, hence all of `H`, so `E_z` is null or conull in `H`. So `E = H × E_0` mod null, and
`Γ_r`-invariance makes `E_0 ⊆ Z'` `Γ`-invariant, hence null or conull by Step 1.

The Koopman representation of `H` on `L²_0(W)` is a continuous unitary representation without nonzero
invariant vectors. By the Howe--Moore property all its matrix coefficients are `C_0`: for
`f, f' ∈ L²_0(W)` and `ε > 0`, the set `{g ∈ H : |⟨g f, f'⟩| >= ε}` is compact. `Γ` is discrete, so that
set meets `Γ` in a finite set. So `⟨γ f, f'⟩ → 0` as `γ → ∞` in `Γ`, and `Γ ↷ W` is mixing.

**Step 6 (orbit equivalence).** Let `R` be the orbit relation of `Γ_ℓ × Γ_r` on `Ω`, and `X = X_ℓ ∪ X_r`.
For `x, x' ∈ X_r`, `x R x'` iff `[x'] ∈ Γ_ℓ·[x]` in `W`, so `R|_{X_r}` is the `Γ_ℓ`-orbit relation of `W`.
Likewise `R|_{X_ℓ}` is the `Γ_r`-orbit relation of `V`. `R|_X` is countable, and `m|_X` is invariant
because `R` comes from a measure-preserving group action.

`R|_X` is ergodic. Let `E ⊆ X` be `R|_X`-invariant. Its saturation `Ẽ = [E]_R` is `Γ_ℓ × Γ_r`-invariant with
`Ẽ ∩ X = E`. `Ẽ` descends to a `Γ_ℓ`-invariant subset of `W`, which is null or conull by Step 5 (mixing
implies ergodic). So `Ẽ ∩ X_r` is null or conull in `X_r`, and so is `Ẽ = ∪_δ δ ∗ (Ẽ ∩ X_r)` in `Ω`.

By Lemma EQ, applied to `R|_X` with `A = X_r`, `B = X_ℓ`, there is `φ ∈ [[R]]` from a conull part of
`X_r` onto a conull part of `X_ℓ`. It preserves `m`, and since `φ(x) R x`, it carries `R|_{X_r}`-classes
onto `R|_{X_ℓ}`-classes. After normalizing the measures by `c`, `φ` is an orbit equivalence between
the free actions `Γ_ℓ ↷ W` and `Γ_r ↷ V`.

**Step 7 (conclusion).** Transport `V`'s action to `W` along `φ`. Two free actions on the same space
then have the same orbits. If `Γ_ℓ ↷ W` were sofic, Păunescu Theorem 1.5 would make `Γ_r ↷ V` sofic,
contradicting Step 3. ∎

## 6. Corollaries

**COROLLARY MT1 (dichotomy for one lattice).** Let `H` and `Γ` be as in Theorem MT. Then either every
p.m.p. action of `Γ` is sofic (`Γ ∈ 𝒮`), or `Γ` has an essentially free, mixing, nonsofic p.m.p.
action. *Proof:* if `Γ ∉ 𝒮`, Corollary ED gives an ergodic nonsofic seed, and Theorem MT applies. ∎

**COROLLARY MT2 (SL_3(Z) implies mixing).** If `SL_3(Z)` has a p.m.p. action that is not sofic, then
some countable sofic group has an essentially free mixing p.m.p. action that is not sofic.

*Proof.* `SL_3(R)` is a connected, noncompact, simple real Lie group with finite center, so it has the
Howe--Moore property (Ciobotaru Theorem 1.1). `SL_3(Z)` is a lattice in it (Furman, p. 5). Apply
Corollary MT1. `SL_3(Z)` is residually finite (reduction mod `p` separates each nonidentity element
from `1` for large `p`), and residually finite groups are sofic: finite quotients in which a given finite
set injects give sofic approximations by left multiplication. ∎

The same argument gives, for every lattice `Λ` in a group covered by Ciobotaru Theorem 1.1: `Λ ∉ 𝒮`
implies that `Λ` has a free mixing nonsofic action. Finitely generated lattices in the first two
families are linear, hence residually finite and sofic.

## 7. Scope

* **Conditional.** No lattice of a Howe--Moore group outside `𝒮` is recorded in the graph or in the
  sources of Section 8. Every recorded nonsofic action of a sofic group comes from a Kun--Thom pair
  (`kun-thom-free-nonsofic-action`, `groups-containing-kun-thom-pair-have-nonsofic-actions`). In a lattice
  of the tree family such a pair cannot exist: a Kazhdan `G` acting on a tree fixes a vertex, so `G`
  lies in a finite vertex stabilizer, and finite infranormal subgroups are normal
  (`finite-infranormal-subgroup-is-normal`). In the Lie and algebraic families,
  `arithmetic-integral-subgroup-is-incompressible` excludes compressions of `SL_n(Z)` itself inside
  `SL_n(Q)`, but says nothing about infinite-index Kazhdan subgroups.
* **What it changes.** The mixing root no longer needs a mechanism that works on mixing actions
  themselves. It is enough to find one Howe--Moore lattice outside `𝒮`, by any mechanism,
  fixed-algebra ones included.
* **Different lattices.** Transfer from `Γ` to another lattice `Λ` of the same `H` uses the coupling
  `H × Z'` with index `covol(Λ)/covol(Γ)`. That needs soficity of relations to be invariant under
  restriction to positive-measure sets and under amplification. Păunescu Theorem 1.5 and Elek--Lippner
  Theorem 1 cover only orbit equivalence of index one. Not done here.
* **Hyperlinear version.** Theorem 1.5 also transfers hyperlinearity between the free actions `W` and
  `V`. But hyperlinearity of `V = Γ\H × Z'` does not follow from hyperlinearity of the seed, so no
  hyperlinear version is claimed.

## 8. Literature check (bounded)

Read on 2026-09-12: Păunescu arXiv:1002.0605v5 (full text), Elek--Lippner arXiv:0906.3619 (Sections
1-2), Dykema--Kerr--Pichot arXiv:1111.2842 and Bowen arXiv:1210.1992 (searched for "orbit equivalence",
"restriction", "measure equivalence"), Furman arXiv:0901.0678 (Sections 2-3), Kun--Thom arXiv:2608.06222v3
(searched for "mixing", "lattice", "measure equivalence"). None states a mixing nonsofic action, the
Howe--Moore transfer, or Lemma ED in this form. Lemma LC is the standard finite-model form of Păunescu's
definition, and its proof uses only the lifting in his Lemma 1.6. The check was bounded to these sources.
