---
rg: 2
id: shell-germ-algebra-fp-forces-fp-germ-group
kind: claim
title: If the germ-groupoid Steinberg algebra of a shell envelope is finitely presented, then its germ group at the singular point is finitely presented
requires: [shell-germ-steinberg-algebra-is-finitely-presented, shell-germ-fp-is-an-ascending-hnn-gate]
distinct_from:
  shell-envelope-fp-forces-fp-germ-group: that derives a finitely presented germ group from finite presentation of the shell GROUP; this asks the same conclusion from finite presentation of the ALGEBRA, which would make the algebra gate at least as hard as half of the group gate.
  bhm-singfix-condition-forces-fp-germ-groups: that derives it from the SingFix hypothesis of Belk--Hyde--Matucci Theorem 2.1; this derives it from an algebra presentation.
  fp-crossed-products-force-finitely-presented-acting-group: that is the model argument (truncation plus a configuration model) for crossed products of subshifts; this asks it for a non-principal germ groupoid, where the model must be a truncated shell.
---

**OPEN.** Let `P`, `nu`, `E_nu`, `G_nu` and `A_nu = A_(F_2)(G_nu)` be as in
`shell-germ-steinberg-algebra-is-finitely-presented`, and let `Q_nu` be the germ group of
`E_nu` at the singular point `p = 0^∞`. The claim: if `A_nu` is finitely presented, then
`Q_nu` is finitely presented. Equivalently, by `shell-germ-fp-is-an-ascending-hnn-gate`: then
the near-shift group `R_nu = <λ(P), s>` is finitely presented and satisfies the ascending
HNN condition there.

## Why it decides the value of the algebra gate

If this holds, the route `boone-higman-via-germ-steinberg-algebra-presentation` needs at
least the germ-group half of the group gate. Attempt 1 of
`steinberg-resolvent-shell-envelope-is-finitely-presented` records that no one-ended input
is known to pass that half. So the exchange of gates would buy nothing where it matters. If
it fails, the algebra gate is strictly weaker than the group gate on the one condition that
currently blocks every one-ended input. **So this is the first thing to decide before
investing in the algebra gate.**

## What is proved toward it (lane proof)

1. **Locality lives on the Schreier graph of `R_nu`, not on `N` or on `P`.** Represent `A_nu`
   on `F_2[Ω]`, `Ω = V·p` the eventually-zero sequences, and write `sh(w 0^∞) = n` when the
   first `1` of `w` is at position `n`. The Leavitt generators move `sh` by at most `1`:
   `s_0` sends shell `n` into shell `n + 1`. The input generators move shell `n` to
   `ρ_g(n)`. So a monomial of length `≤ ℓ` evaluated at a point of shell `n` depends only
   on the rooted `ℓ`-ball at `n` of the graph `Σ_nu` on `N` with edges `n ~ n+1` and
   `n ~ ρ_g(n)`. That graph is the Schreier graph of the near action of `R_nu`. So any
   truncation argument must be run over `R_nu`, as in
   `fp-crossed-products-force-finitely-presented-acting-group`, with configurations replaced
   by truncated shells.
2. **The locality is never along `N` for a one-ended input.** If every generator of `P`
   moves every shell by at most `C`, i.e. `|ν(gx) - ν(x)| <= C` for `x ∈ P` and `g` a
   generator, then the ball of radius `r` in `P` embeds in an interval of length
   `2Cr + 1`. So `P` has linear growth and is virtually cyclic. Hence, for every input that is
   not virtually cyclic, the homoclinic and shell-filling obstructions of the crossed-product
   family on main (`fp-minimal-crossed-products-have-no-homoclinic-pairs`) do not transfer
   along `N`; only a transfer along `Σ_nu` is possible. This matches
   `rational-regular-shell-actions-require-virtually-cyclic-input`, which says the same about
   finite-state realizations.

## The expected proof, and where it is stuck

Write `R_nu = F(T)/K` and truncate: `K_M` is the normal closure of the relators of length
`<= M`, and `R_M = F(T)/K_M`. The crossed-product proof builds a model in which the algebra
relators hold but one long group relator fails. Here the model should be a shell over `R_M`:
a countable set carrying an `R_M` near action whose `ℓ`-balls match those of `Σ_nu`, glued
onto a Cantor set as in `shell-cantor-embeddings-are-finite-germ-extensions`. The step that
does not yet work is that `R_nu` acts on `N` only as a near action (germs modulo finitary
permutations), so an `R_M` near action with the right local structure has to be built
without a genuine action to pull back. No such construction is written here.

## Attempts

1. **The input-letter truncation (bh-ck-kernel, 09-18).** *Proves the part of the claim that
   survives, and isolates what remains.*
   [[shell-germ-algebra-fp-forces-bounded-germ-presentation]]: truncating by the number of
   input letters, not by word length, the model of "The expected proof" above can be built
   inside a matrix representation over `F_2[Q']`, with no near action at all. Result: if `A`
   is finitely presented, then `Q` has a presentation whose relators have boundedly many
   input letters, but arbitrary exponents of the shift `τ`.
   - **What remains for this claim:** bounding the shift exponents. That is exactly the
     Bieri--Strebel / ascending-HNN clause of `shell-germ-fp-is-an-ascending-hnn-gate`, and
     nothing in the algebra argument forces it. One algebra relator, read along shell `n`,
     produces germ relations with shift exponent `rho_g(n) - n`.
   - **Consequence.** The algebra gate, if it holds, may avoid the ascending-HNN clause that
     the group gate needs. The way to refute this claim is an enumeration whose germ group is
     boundedly but not finitely presented, with a finitely presented algebra.
2. **The counterexample side (bh-free-53, 09-18).** *No counterexample found. It shows that
   the claim has two versions, and that Attempt 1 covers only one of them.*
   - **`A_nu` is never simple.** By [[shell-germ-steinberg-algebras-are-never-simple]], for every
     `g ≠ 1` the element `f_g = (1 - u_g) s_0 (1 - u_g) t_0` is a nonzero singular function,
     supported on four germs at `p`. So the Boone--Higman route has to use a simple quotient,
     most naturally `A_nu/J` with `J` the singular ideal. The version of this claim the route
     needs is: `A_nu/J` finitely presented ⇒ `Q_nu` finitely presented.
   - **Attempt 1 does not reach that version.** Its matrix model is the fibre module over
     `F_2[Q]`. There the `p`-column of `f_g` is `1 + r_g + τ r_g τ^(-1) + r_g τ r_g τ^(-1)`,
     which is nonzero in `F_2[Q]`, and nonzero in `F_2[Q']` too, because the four words are
     already distinct in `Q`. So the model is not a representation of `A_nu/J`, where
     `f_g = 0`. A model for `A_nu/J` must kill these four-term combinations. The orbit module
     `F_2[Ω]` does kill `f_g`, but that is the near-permutation setting in which "The expected
     proof" is stuck.
   - **Where a counterexample for `A_nu` must live.** By Attempt 1, `Q_nu` must have a
     presentation with boundedly many input letters but no finite presentation, as for
     `Z ≀ Z`. The germ groups have room for lamp-type subgroups: `r_g` moves only even shells
     and `τ r_h τ^(-1)` moves only odd shells, so they commute exactly on large shells, and
     `P × P <= Q_nu` via `(g, h) |-> r_g τ r_h τ^(-1)`. No enumeration was found for which
     `Q_nu` is boundedly but not finitely presented while `A_nu` is finitely presented.
   - **The characteristic-2 mechanism.** Linear relations among germs can imply group relations.
     For example `1 + b + c + d = 0` with `b^2 = c^2 = d^2 = 1` forces `bc = cb` over `F_2`.
     This is a way for an algebra presentation to be shorter than a group presentation. Its standard instance, Bartholdi's tree-enveloping algebra of the
     Grigorchuk group, is recursively presented with the infinite families `σ^n(CACACAC)` and
     `σ^n(DACACAD)` (arXiv math/0410226, theorem `thm:=2:pres`, read from the e-print). So it gives no finitely presented instance. Search log:
     `research/artifacts/gq-bh-bh-free-53-algebra-gate-counterexample-search.md`.
