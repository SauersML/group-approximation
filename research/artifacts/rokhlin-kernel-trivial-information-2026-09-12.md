# Information on which large finite subgroups act trivially is free for Rokhlin entropy

Lane `ex-rokhlin-lower`, 2026-09-12. The proofs are handwritten, and nothing was computed.

**Supports:**
- `factors-fixed-by-large-finite-subgroups-have-zero-outer-entropy`, with its route
  `factors-fixed-by-large-finite-subgroups-zero-outer-proof`;
- the Attempts entry on `kun-thom-wreath-bernoulli-rokhlin-maximal`.

## 0. Conventions

- `W` is a countable group acting freely and ergodically, preserving `mu`, on a standard probability
  space `(X, mu)`.
- For a countable partition `alpha`, `sigma-alg_W(alpha)` is the smallest `W`-invariant sigma-algebra
  containing `alpha`.
- **Outer Rokhlin entropy** of a collection `C` of Borel sets:
  `h_W(C) = inf { H(alpha) : alpha a countable partition of X with C ⊆ sigma-alg_W(alpha) }`.
- **Relative Rokhlin entropy:** `h_W(X | F) = inf { H(alpha | F) : sigma-alg_W(alpha) v F = B(X) }` for
  a `W`-invariant sigma-algebra `F`.
- These are the definitions of `seward-rokhlin-entropy-subadditivity` (Seward, arXiv:1501.03367v4,
  Section 2), specialised to ergodic actions.

**(S2) Two-step subadditivity.** This is Corollary 2.5 there, with `C = B(X)`, trivial `Sigma`,
`F_1 = F` and `F_n = B(X)` for `n >= 2`:

    h^Rok_W(X) <= h_W(F) + h_W(X | F).

## 1. The theorem

**Theorem L.** Let `W ↷ (X, mu)` be free, ergodic and p.m.p. Let `F` be a `W`-invariant sub-sigma-algebra,
and let `beta ⊆ F` be a countable partition with `H(beta) < infinity` and `F ⊆ sigma-alg_W(beta)`.
Suppose `W` contains finite subgroups `T_n` with `|T_n| -> infinity`, and each `T_n` acts trivially on
`F`: `t.B = B` mod null for every `B` in `F` and every `t` in `T_n`. Then:

1. `h_W(F) = 0`;
2. `h^Rok_W(X) = h_W(X | F)`.

*Proof.* **Part 1.** Fix `n` and put `T = T_n`.
- **A transversal.** `T` is finite and acts freely. Fix a Borel linear order on `X` and let `M` be the set
  of points that are least in their `T`-orbit. Then `M` is Borel and `X = ⊔_(t in T) t.M`, so
  `mu(M) = 1/|T|`.
- **The partition.** Put `alpha = {X \ M} ∪ {B ∩ M : B in beta}`.
- **Its entropy.** For `B` in `beta` and `t` in `T`, `mu(B ∩ t.M) = mu(t^-1.B ∩ M) = mu(B ∩ M)`, because
  `t^-1.B = B`. The sets `t.M` partition `X`, so `mu(B ∩ M) = mu(B)/|T|`. Hence

      H(alpha) = H(1/|T|, 1 - 1/|T|) + (1/|T|) H(beta).                      (1.1)

- **It generates `F`.** `M` is a union of atoms of `alpha`, so every `t.M` lies in `sigma-alg_W(alpha)`.
  For `B` in `beta`,

      B = ⊔_(t in T) (B ∩ t.M) = ⊔_(t in T) t.(t^-1.B ∩ M) = ⊔_(t in T) t.(B ∩ M),

  and each `t.(B ∩ M)` is a translate of an atom of `alpha`. So `beta ⊆ sigma-alg_W(alpha)`, and
  `F ⊆ sigma-alg_W(beta) ⊆ sigma-alg_W(alpha)`.

So `h_W(F)` is at most (1.1) for every `n`. Letting `n -> infinity`, the right side tends to `0`, since
`H(beta) < infinity`.

**Part 2.** By (S2) and Part 1, `h^Rok_W(X) <= h_W(F) + h_W(X | F) = h_W(X | F)`. Conversely, a generating
partition `alpha` satisfies `sigma-alg_W(alpha) v F = B(X)` and `H(alpha | F) <= H(alpha)`, so
`h_W(X | F) <= h^Rok_W(X)`. QED

**Remarks.**
0. **Credit (correction added the same day).** Part 1 is a special case of Alpeev–Seward, arXiv:1705.09707,
   Theorem 1.11(ii), imported as `alpeev-seward-stabilizer-growth-kills-outer-entropy`.
   - Their statement: "If |Stab_G(f(x)) : Stab_G(x)| = ∞ for µ-almost-every x ∈ X then hRok_(G,µ)(Y,ν) = 0."
   - It needs only an aperiodic action and infinite-index stabilizer growth along the factor: no finite
     subgroups and no finite-entropy generator.
   - The first version of this artifact did not cite it. The transversal proof above is a re-derivation of
     the special case, and Sections 2 and 3 hold with "finite subgroups of unbounded order" replaced by
     "an infinite subgroup acting trivially on the factor".
1. **Relation to Seward's Theorem 6.7.** Step 4 of the proof of Theorem A in
   `research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md` uses the same transversal.
   - There, the atoms are made `T`-invariant through a subgroup `G` that commutes with `T`, and the input
     is `h^Rok_sup(G) < infinity`.
   - Here the `T`-invariance is a hypothesis on the factor, and no finiteness of any supremum is used.
   - The two statements are independent. Theorem L needs no commuting subgroup and no finite supremum.
     Theorem A needs no factor fixed by `T`.
2. **Model test.** Two cases.
   - **The hypothesis fails and so does the conclusion.** Take `W = Z` acting on the 2-shift, with
     `F = B(X)`. No nontrivial finite subgroup exists, and `h_W(X | X) = 0 != log 2 = h^Rok_W(X)`.
     Moreover, in a free action a nontrivial `T` cannot act trivially on `B(X)`.
   - **A real object satisfying the hypothesis.** Take `W = (Z/2) wr Z`, `X` the product of a free
     `W`-Bernoulli shift with the pullback of the `Z`-Bernoulli 2-shift, and `F` that pullback. The lamp
     subgroups `(Z/2)^[-n,n]` act trivially on `F`. Here the conclusion agrees with Kolmogorov–Sinai
     theory: `W` is amenable and `F` has zero `W`-entropy, because the infinite normal lamp subgroup acts
     trivially on it.
3. **Freeness.** Freeness is used only to find the transversal `M`, and ergodicity only to apply (S2).

## 2. Consequences for normal subgroups and the Kun–Thom wreath

**Corollary L1 (joining with quotient actions adds nothing).** Let `N ◁ W` contain finite subgroups of
unbounded order, and put `Q = W/N`. Let `W ↷ X` be free and ergodic, let `Q ↷ Y` be p.m.p. with a
finite-entropy generating partition, and let `W` act on `Y` through `Q`. Suppose `X × Y` is ergodic, for
example when `X` is weakly mixing. Then

    h^Rok_W(X × Y) = h_W(X × Y | B(Y)) <= h^Rok_W(X).

*Proof.* Put `F = B(Y)`.
- `X × Y` is free, since `X` is, and `N` acts trivially on `F`. Theorem L gives the equality.
- For a generating partition `alpha` of `X`, the partition `alpha × Y` generates `X × Y` together with
  `F`. Also `H(alpha × Y | F) = H(alpha)`, since `alpha` is independent of `F`. QED

**Corollary L2 (sofic-visible information is free over Kun–Thom wreaths).** Let `W = (Z/2) wr_(G/Γ) G`
for a Kun–Thom Theorem E pair.
- **The radical.** By `kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`, `Rad_sof(W)` is the
  subgroup `N_0` of fibre-even lamp configurations over `G/N` with `N = Γ̂`.
- **Large finite subgroups.** `Γ` is not profinitely closed, so some fibre of `G/Γ -> G/Γ̂` has two
  points. Every `g`-translate of that fibre is again a fibre, and distinct translates are disjoint.
  So `N_0`, a locally finite elementary abelian 2-group, contains finite subgroups of unbounded order.
- **The conclusion.** For every free ergodic `W`-action `X` and every factor `F` on which `N_0` acts
  trivially, with a finite-entropy generator:
  - `h_W(F) = 0`;
  - `h^Rok_W(X) = h_W(X | F)`.

  In particular this holds for every action of the residually finite quotient
  `W/Rad_sof(W) = (Z/2) wr_(G/Γ̂) G`, joined into `X` as in Corollary L1.

**Reading.** Every sofic approximation of `W` factors through `W/Rad_sof(W)`. The information in any
factor on which the radical acts trivially is exactly the information sofic methods can see, and it
contributes nothing to Rokhlin entropy. So any positive Rokhlin entropy of a free `W`-action lives
entirely in information on which the invisible lamps act nontrivially. This is the action-level
counterpart of the witness localization in `kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers`
and `sofic-radical-localizes-bernoulli-deficit-witnesses`, where every deficit configuration folds on an
invisible element.

## 3. What this does not give

- **No lower bound.** Theorem L is a vanishing statement.
- **The uniform Bernoulli shift over `W` has no nontrivial factor on which `N_0` acts trivially.**
  - The restriction to the infinite subgroup `N_0` is mixing.
  - A sigma-algebra fixed by `N_0` consists of `N_0`-invariant sets, and so it is trivial.
  - So Corollary L2 does not reach `kun-thom-wreath-bernoulli-rokhlin-maximal`. It says only that the
    candidates for POS built from the actor or the sofic quotient are all dead.
  - This upgrades the `Z^2` example on `every-group-has-positive-rokhlin-entropy-action` from one failed
    lower bound to a theorem: over the Kun–Thom wreath, joining with an action of the actor or of the
    sofic quotient never raises Rokhlin entropy.
- **No zero-or-infinity dichotomy for `W`.** Theorem A of the self-copy artifact needs a finite-supremum
  subgroup commuting with the `T_n`. The lamp subgroups of `W` are normalised by the actor, not centralised
  by it, and Theorem L does not replace that input.
