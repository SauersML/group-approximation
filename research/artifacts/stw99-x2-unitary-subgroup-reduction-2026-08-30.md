# X(2): unitary-subgroup reduction and the hyperfinite-character boundary

## Scope and status

This audit records an unconditional reduction of STW Problem X(2), together
with one obstruction and two open witness searches.  It does **not** assert
that the hyperfinite II1 factor `R` is non-quasidiagonal.

The established implication is

```text
R quasidiagonal
  => every countable subgroup of U(R) is MF.
```

Consequently, a countable non-MF subgroup of `U(R)` would refute X(2).  No
such subgroup is constructed here.  The nodes
`non-mf-subgroup-of-hyperfinite-factor-unitary-group`,
`literal-group-embeds-in-hyperfinite-unitary-group`, and
`hyperfinite-factor-not-quasidiagonal` remain open claims.

## The unconditional reduction

Let `Gamma <= U(R)` be countable and put `A=C*(Gamma) subset R`.  If `R` is
quasidiagonal, then its C-star subalgebra `A` is quasidiagonal.  Hence `A` is
MF and embeds in a norm matrix ultraproduct.  Restriction to the distinguished
unitaries gives operator-norm almost-representations of `Gamma` which separate
every nonidentity element.  Thus `Gamma` is MF.

Taking the contrapositive gives the live route
`hyperfinite-factor-not-qd-via-non-mf-unitary-subgroup`: one non-MF subgroup
of `U(R)` would imply that `R` is not quasidiagonal.  This reduction is
strictly about an honest embedding into `R`; an embedding into `R^omega`,
such as the one supplied by soficity, is insufficient.

## Which groups embed in `U(R)`

A countable group embeds in `U(R)` precisely when it has a faithful character
whose GNS von Neumann algebra is hyperfinite.  Here faithfulness on the group
means `tau(g) != 1` for every `g != 1`.  This criterion makes the remaining
witness problem concrete:

```text
find a non-MF group with a faithful hyperfinite character.
```

Amenable and residually finite groups provide many embeddings but are MF, so
cannot be witnesses.  Known non-MF groups therefore require a character very
different from their regular character.

## Property-(T) obstruction

There is an unconditional obstruction to the most immediate candidates.  If
a finitely generated property-(T) group embeds in `U(R)`, its induced faithful
character has hyperfinite GNS closure and is amenable.  Kirchberg's
property-(T) rigidity for amenable traces approximates that character by
finite-dimensional characters.  Since the character separates group
elements, finite-dimensional representations separate them as well.  Their
finitely generated linear images are residually finite by Mal'cev, and the
original group is residually finite.

Therefore every finitely generated Kazhdan subgroup of `U(R)` is residually
finite and hence MF.  The known simple and torsion-free Kazhdan non-MF groups
cannot embed in `U(R)`.  This invalidates the route
`non-mf-unitary-subgroup-via-kazhdan-non-mf-groups` but says nothing decisive
about non-Kazhdan groups.

## Literal-group candidate

The remaining recorded candidate is the literal non-MF group `E`.  Its
soficity embeds it in `U(R^omega)`, not in `U(R)`.  An embedding into `U(R)`
would amount to a faithful hyperfinite character.  Splitting at its central
involution mark `w` reduces one proposed construction to:

1. a faithful hyperfinite character of `E/<w>`; and
2. a hyperfinite projective representation on which `w` acts as `-1`.

Both pieces are open.  Finite-dimensional representations kill the mark, so
the second piece would have to be genuinely infinite dimensional.  The
coherence needed to replace an ultrapower representation by an honest
representation in `R` is exactly the unresolved step.

## Integrity boundary

The graph deliberately separates established and open nodes:

- `hyperfinite-factor-qd-forces-unitary-subgroups-mf` and
  `kazhdan-groups-in-hyperfinite-unitary-group-are-rf` are established;
- `non-mf-subgroup-of-hyperfinite-factor-unitary-group` and
  `literal-group-embeds-in-hyperfinite-unitary-group` are open;
- `hyperfinite-factor-not-quasidiagonal` is an open target reached only if a
  non-MF subgroup witness is supplied.

No route in this lane currently closes X(2).

---

The sections below were appended by the lane that wrote the reduction; they
record the hyperfinite covariant obstruction and its application to the
Clifford witnesses (`hyperfinite-covariant-obstruction-lemma`,
`clifford-witness-has-no-hyperfinite-marked-representation`).

## Addendum A (same day). The covariant obstruction lemma

**Lemma.**  Let `Γ = Λ ⋊ Σ`, `ρ : Γ → U(W)` with `W` finite, faithful
normal trace `τ_W`, `M = ρ(Λ)''`, `α_g = Ad ρ(g)|_M`.  If `α_g` is properly
outer on `M` for all `g ∈ Σ \ {e}` (no nonzero `x ∈ M` with
`x a = α_g(a) x` for all `a ∈ M`), then `τ_W(ρ(g)) = 0` for `g ≠ e`,
`ρ(Σ)'' ≅ L(Σ)`, and if `W` is injective then `Σ` is amenable.

Proof.  With `E : W → M` the trace-preserving expectation and
`x_g = E(ρ(g))`: `x_g a = E(ρ(g) a) = E(α_g(a) ρ(g)) = α_g(a) x_g`, so
`x_g = 0`; then `τ_W(a ρ(g)) = τ_W(a x_g) = 0`, the character of `Σ` is
`δ_e`, `ρ(Σ)''` is the completion of `(C[Σ], δ_e)`, i.e. `L(Σ)`, and a von
Neumann subalgebra of a finite injective algebra is injective, so `Σ` is
amenable by Connes.  ∎

## Addendum B. The marked witnesses have no hyperfinite representation

Site set `X = Σ/B`, `Σ = Z[1/2]^3 ⋊ (SL_3(Z) × Z)`, `B = Z^3 ⋊ SL_3(Z)`,
`K = τ^{-1} B τ = (1/2)Z^3 ⋊ SL_3(Z)`, blocks `Σ/K` of eight sites.

**Theorem.**  Let `Γ` be the Clifford witness `W = Cl(X) ⋊ Σ` (all
distinct lamps anticommute up to the sign `ζ`) or the block-commuting
quotient `E_⊗` of the literal group `E` (lamps in one block anticommute up
to `ζ`, lamps in distinct blocks commute).  Every homomorphism from `Γ`
into the unitary group of a finite injective von Neumann algebra sends
`ζ` to `1`.  In particular `Γ` does not embed in `U(R)`.

Proof.  Compress to the `−1`-eigenspace of `ρ(ζ)`, a central projection of
`ρ(Γ)''`, so `ρ(ζ) = −1`.  (1) The marked lamps generate a UHF algebra:
`Cl(ℓ^2 X) ≅ M_{2^∞}` for `W`, `⊗_{Σ/K} Cl_8 = ⊗ M_16 ≅ M_{16^∞}` for
`E_⊗`; both simple, so `A = C*(ρ(Λ))` is that UHF algebra.  (2) `τ_W|_A` is
its unique trace and `M = ρ(Λ)'' ≅ R`.  (3) Every `g ≠ e` moves infinitely
many sites and infinitely many blocks: with `g = t_a m τ^k`,
`t_v^{-1} g t_v = t_{a − v + m(2^k v)} m τ^k ∈ B` forces `k = 0` and
`(m−1) v ∈ Z^3 − a`; for `m ≠ 1` the map `(m−1)` on `(Z(2^∞))^3` has
infinite image so infinitely many `v` fail; for `m = 1`, `k = 0`, `a ≠ 0`,
`(τ^n t_v)^{-1} t_a (τ^n t_v) = t_{2^{-n} a} ∉ B` for large `n`; for
`k ≠ 0` no conjugate lies in `T ⊇ B`.  (4) Hence `α_g` is outer on `R`:
if `Ad u = α_g`, approximate `u` in 2-norm by `u_0` supported on finitely
many sites `F`; take an even traceless unitary `x` (a product of two lamps,
or a traceless unitary of one block) supported off `F` and moved off itself
by `g`; then `u_0 x u_0^* = x`, `‖x − α_g(x)‖_2 = √2`, while
`‖u x u^* − u_0 x u_0^*‖_2 ≤ 2‖u − u_0‖_2`.  (5) The lemma gives `Σ`
amenable; `SL_3(Z) ≤ Σ`.  ∎

This is the Hilbert--Schmidt-exact counterpart of the manuscript's
obstruction (`commuting-lamp-quotient-not-mf`): the sign is invisible to
norm-matrix coronas by property (T) and finiteness of matrices, and
invisible to hyperfinite tracial representations by uniqueness of the UHF
trace, outerness of the site action, and nonamenability of `SL_3(Z)`.  The
sign survives in `U(R^ω)` (the witness is sofic), and the proof breaks in
`R^ω` only at injectivity.

## Addendum C. The literal group E

`E = C(𝒢) ⋊ Σ` with lamp kernel a central amalgam of Clifford blocks.  A
faithful hyperfinite character of `E` needs a `Σ`-invariant hyperfinite
character `τ_Λ` of `Λ = C(𝒢)` with `τ_Λ(w) = −1` on whose GNS closure some
`g ≠ e` is inner on a nonzero central piece (else the lemma applies).
Dead families: canonical characters of `Σ`-invariant quotients with a
non-commuting pair of blocks (GNS contains `M_16 * M_16`, not injective);
the block-commuting quotient (Section 4); direct integrals of
finite-dimensional block-labeling representations over a `Σ`-invariant
product measure (type I closure, essentially free centre action, properly
outer); full innerness of some `g` (its normal closure contains a
translation, every nontrivial translation is conjugate into `K \ B`, and
identifying adjacent lamps kills `w`).  Open: partial innerness for a
general `Σ`-invariant hyperfinite marked character.

## Addendum D. The mark of E itself is invisible to hyperfinite representations

**Theorem.**  Let `W` be a finite injective von Neumann algebra with
faithful normal tracial state `τ`.  Every homomorphism `ρ : E → U(W)`
satisfies `ρ(w) = 1`.  So `E` does not embed in `U(R)`, and every uniformly
amenable trace on `C*(E)` (Brown 3.2.2) is trivial on `w`.

Proof.  Compress to the `−1`-eigenspace of `ρ(w)` (a central projection of
`ρ(E)''`; the compression is finite injective), so `ρ(w) = −1`.
(1) The eight lamps of the base block pairwise anticommute, so they generate
a unital `M_16 ⊂ W`, `W ≅ M_16 ⊗ W_1`, `τ = tr_16 ⊗ τ_1`, and for `k ∈ K`
(the block stabiliser) `ρ(k) = V_k w_k` with `V_k ∈ M_16` implementing the
site permutation and `w_k ∈ W_1`.  (2) A non-integral half-translation
`t_v ∈ K` permutes the eight Clifford generators by four disjoint
transpositions; `|tr V|^2 = tr(Ad V) = Σ_j C(4,j)(−1)^j = 0`, so
`χ(t_v) = tr(V_{t_v}) τ_1(w_{t_v}) = 0`.  (3) `t t_v t^{-1} = t_{2v}` and
every nonzero `u ∈ Z[1/2]^3` is `2^n v` with `v` a non-integral
half-translation, so `χ(t_u) = 0` for all `u ≠ 0`; hence
`𝒜 = ρ(Z^3)'' ≅ L^∞(T^3)` with Haar trace.  (4) For `m ∈ SL_3(Z) \ {1}`,
`x = E_𝒜(ρ(m))` satisfies `x f = σ_m(f) x`, so `x` is supported on the
Haar-null set `Fix(m) = ker(m − 1) ⊂ T^3`; `x = 0` and `τ(f ρ(m)) = 0` for
`f ∈ 𝒜`.  Thus `χ|_B = δ_e` on `B = Z^3 ⋊ SL_3(Z)`.  (5) `ρ(B)'' ≅ L(B)` is
not injective (`B` nonamenable) but sits with a trace-preserving expectation
inside the injective `W`.  ∎

Property (T) is not used.  The corona theorem of the manuscript and this
theorem kill the same element by unrelated mechanisms; together with the
Kazhdan obstruction, every known non-MF group of the compression family is
excluded as a witness for non-quasidiagonality of `R`.

## Addendum literature

* N. P. Brown, Invariant means and finite representation theory of
  C\*-algebras, Mem. AMS 184 (2006), no. 865: Theorems 3.1.6, 3.1.7,
  3.2.2, Lemma 4.1.11, Proposition 4.1.12.
* E. Kirchberg, Discrete groups with Kazhdan's property T and factorization
  property are residually finite, Math. Ann. 299 (1994).
* B. Blackadar, E. Kirchberg, Generalized inductive limits of
  finite-dimensional C\*-algebras, Math. Ann. 307 (1997).
* J. Carrión, M. Dadarlat, C. Eckhardt, On groups with quasidiagonal
  C\*-algebras, JFA 265 (2013).
* A. Connes, Classification of injective factors, Ann. of Math. 104 (1976).
* K. Dykema, Free products of hyperfinite von Neumann algebras and free
  dimension, Duke Math. J. 69 (1993).
