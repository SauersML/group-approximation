# Adversarial review (reviewer-2): hyperbolic-rf, fp-surjunctive, fixed-price, determinant

Reviewer lane `reviewer-2`, 2026-09-12. Proofs read line by line; literature
inputs identified but 1972/2000-era primary sources not re-derived. Verdicts
are PASS / GAP / conditional, with the trust surfaces named. Nothing here is
Lean-verified.

## 1. hyperbolic-rf

### 1a. `filling-no-finite-quotient-iff-simple-image-orders` (+ proof) — PASS
Elementary and correct. (⇒) `ord φ(g) | n` makes `φ` factor through
`Γ/⟨⟨g^n⟩⟩`. (⇐) any nontrivial finite quotient has a simple subquotient `S`,
and `g^n = 1` in the filling forces `ord φ(g) | n`. Conditions (1)–(3) are the
`ord = 1`, abelian, and congruence specializations. No novelty is claimed.

### 1b. `sp21-lattice-positive-characteristic-images-finite` (+ proof) — PASS (trust surfaces)
The standard nonarchimedean-superrigidity argument. Steps check:
an infinite image gives an element of infinite order (Schur); in char `p` a
matrix all of whose eigenvalues are roots of unity is finite order, so some
eigenvalue `λ` is not a root of unity; Tits' lemma embeds into a nonarchimedean
local field with `|σ(λ)| > 1`; `det ρ_k` factors through the finite `Γ^ab`
(property (T)); the Gromov–Schoen fixed point on the (locally finite, finite
residue field) building forces all eigenvalue ratios to modulus 1, hence via
the determinant all eigenvalues to modulus 1, contradicting `|σ(λ)| > 1`.
Trust surfaces, correctly flagged in the node: Gromov–Schoen over a char-`p`
local field, and Tits' lemma. No gap.

### 1c. `sp21-bounded-rank-simple-quotients-almost-all-congruence` (+ proof) — PASS (trust surface: SR)
Correct assembly. A putative infinite family of fixed type `X` assembles along
an ultrafilter into `ρ: Γ → GL_M(K)`; Łoś + finite presentation make the image
infinite; 1b forces `char K = 0`; Larsen–Pink/Łoś give Zariski density;
Margulis-form superrigidity writes `ρ = τ ∘ σ`; specializing the arithmetic
ring map reads congruence off along `U`, contradicting the non-congruence
choice. **Main trust surface (correctly flagged):** superrigidity over an
abstract characteristic-0 field for cocompact `Sp(n,1)`/`F4(-20)` lattices,
taken as Corlette + Gromov–Schoen + the Margulis global argument. This is the
standard arithmeticity-from-superrigidity package; not re-derived here. The
stated consequence — infinite families of simple quotients of a one-element
filling can only be alternating or unbounded-rank classical — follows.

### Payoff route `quotientless-hyperbolic-via-sp21-simple-quotient-bound` — PASS as a CONDITIONAL reduction
The two-step Olshanskii surjection argument (surjection trick `Γ = Δ·ker φ`,
G-subgroup at each step, torsion-freeness from conjugacy-class bijectivity,
congruence density killing `Γ̄_S`) is internally correct. **But it is
conditional:** it requires `sp21-lattice-few-alternating-and-large-rank-quotients`,
whose only route `sp21-simple-quotient-bound-from-congruence-property` requires
`sp21-lattice-has-congruence-subgroup-property` — the **open** CSP for `Sp(n,1)`.
So the route does not establish `hyperbolic-group-without-finite-quotients`;
that root must stay OPEN. Verified: the lane reports the crux as CSP-hard, and
the graph keeps the root open. The reduction is sound; the honesty is intact.
Do not let any later edit make `sp21-lattice-has-congruence-subgroup-property`
established without an independent proof — that would falsely fire the payoff.

## 2. `fp-surjunctive-nonsofic-group-exists` and `kt-lef-graph-wreaths-surjunctive-and-nonsofic` — PASS (KT v3 trust surface)
Finite presentation of `D = G *_Γ G` checks:
`R = F_2[x_1^{±},x_2^{±},x_3^{±}]` is a finitely presented ring; Krstić–McCool
gives `St_6(R)` finitely presented (rank `6 ≥ 4`); K2-stability at `6 = dim R + 3`
gives `ker(St_6 → EL_6) = K2(R)`; the Bass–Heller–Swan / fundamental-theorem
recurrence gives `K2(R) = Z^3` (I recomputed: `K1(R_j) = K1 ⊕ K0`, `K2(R_j) =
K2 ⊕ K1`, from `K0(F_2)=Z, K1(F_2)=0, K2(F_2)=0`, yielding `K2(R_3)=Z^3`), so
three relators cut `EL_6(R)` out of `St_6(R)`; `G = EL_6(R) ⋊ SL_3(Z)` is f.p.;
the amalgam of two f.p. groups over the finitely generated `Γ` is f.p.
Surjunctivity is the reviewed graph-fold permanence (`review-surjunctive` PASS);
nonsoficity is Kun–Thom Theorem A v3 for the double.

`lef-lamp-graph-wreaths-are-surjunctive`: the RF-lamp case reduces to the
reviewed finitary split-extension permanence via Green's induced-graph
retractions; the LEF case is the marked-limit closure (Lemma 3.1, finite-table
form) plus the transplant Lemma 4.1, which records every intermediate
graph-product reduction coefficient and replaces coefficients by a LEF image
into a finite group. Lemma 4.1 is rigorous: reducedness depends only on the
unchanged vertex sequence and on which coefficients are nontrivial, both
preserved by the injective `θ`. PASS.
**Trust surface, fleet-wide:** Kun–Thom arXiv:2608.06222 is an unrefereed v3;
only its statements are imported (the 4.1 corollary already PASSed by `reviewer`).

## 4. `fpbs-elementary-matrix-semidirect-fixed-price-one` (+ proof, + citation) — PASS; credit correct
`G = EL_r(R) ⋊ H` (`R` countable infinite commutative, `r ≥ 3`, `H` countable
acting by ring automorphisms) has fixed price one. The commuting/normalizing
root-subgroup chain `K_0 = E_12(R) ≤ K_1 ≤ K_2 ≤ K_3 = G` was checked
step by step against the Steinberg commutation rule `[e_ij(a),e_kl(b)] = 1`
for `j≠k, i≠l`: every added generator commutes with or normalizes an infinite
subgroup already present, and `K_3` recovers every root subgroup plus `H`.
`K_0` is infinite amenable (cost 1). Three applications of Gaboriau's
Theorem 2.45 give `C(R_G) = 1` for every free action.
**Credit check (the coordinator's flag): resolved.** The node explicitly states
"a direct application of Gaboriau's criterion, not a new theorem," quotes
Theorem 2.45 verbatim, cites Crit. VI.24, and notes `R=Z, H` trivial is
Gaboriau's `SL(n,Z)`. The only new content is the chain choice covering the
Kun–Thom Theorem E group. Correctly scoped. The instance conclusion — the
nonsofic action, the Bernoulli shift and the profinite actions of the
Kun–Thom group all have cost one, so cost does not detect soficity there — is
correct.

## 5. `finite-spectrum-integral-elements-obey-determinant` (+ proof), `zalesskii-idempotent-trace-is-rational` — PASS
For any group `G` and self-adjoint `A ∈ M_n(Z[G])` with finite spectrum:
the minimal polynomial is in `Z[x]` (linear dependence over `C` of the `A^j`
in the `Q`-space `M_n(Q[G])` descends to `Q`; `Z[A]` is a finite `Z`-module so
`A` is integral; Gauss), so `σ(A)` is a Galois-stable set of totally real
algebraic integers. Spectral projections `E_λ = p_λ(A) ∈ M_n(K[G])` are
idempotents; their traces are rational — `n=1` is Zalesskii, general `n` via
the degree-`n` `Q`-rational standard representation of `S_{n+1}` embedding
`M_n(K) ↪ K[S_{n+1}]` with trace scaling `n/(n+1)!`, then Zalesskii on
`K[S_{n+1} × G]`. Galois conjugates carry equal mass (`Tr(E_λ) ∈ Q` is
`Gal`-fixed, and `σ(Tr E_λ) = Tr E_{σλ}`). The Serre inequality then holds
orbit by orbit: `|Norm(Q(λ_O))| ≥ 1` for a nonzero integer, so `∫ log|Q| dμ_A
≥ 0`; the case `Q = x` gives `det_{N(G)}(B) ≥ 1` for `B*B` of finite spectrum.
I checked the trace-scaling constant and the `Z`-module integrality step; both
hold. This is a genuine unconditional result over every group (nonsofic
included) — but an obstruction, not a solution: it forces determinant
violations to have infinite spectrum, correctly invalidating
`determinant-counterexample-via-galois-unequal-atoms`.
The Zalesskii import (idempotent trace in `K[G]`, char 0, lies in `Q`) is a
correct literature statement; the 1972 primary source was not re-read.

## 3. gottschalk-positive-host Seward Thm 6.7 transfer — NOT YET REVIEWABLE
The dichotomy-transfer nodes were not on main at review time. Deferred.

## Summary
PASS: 1a, 1b, 1c, 2, 4, 5. Conditional (correctly so): the quotientless-hyperbolic
payoff, gated on the open CSP for `Sp(n,1)`. No false establishment found; every
conjecture-level root stays OPEN. Residual trust surfaces: abstract-field
superrigidity (1c), Gromov–Schoen char-`p` (1b), Kun–Thom v3 (2), Zalesskii 1972 (5).
