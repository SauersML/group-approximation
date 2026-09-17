---
rg: 2
id: reversible-automata-that-never-lower-rest-counts-preserve-them
kind: claim
title: A reversible automaton fixing the rest configuration that never lowers the number of non-rest sites never raises it
distinct_from:
  count-raising-reversible-automata-lower-biased-rokhlin-entropy: that proves a count-raising reversible automaton forces Rokhlin supremum zero on its group; this asserts that no such automaton exists over any group.
  passive-fixing-injective-automata-are-surjective: that proves surjectivity when reserved symbols stay in place; this is the count statement that makes every design moving its star set by a reversible automaton surjective.
  every-injective-ca-has-uniform-single-site-output-law: that asks uniform input to give a uniform one-site law, and is equivalent to surjunctivity; this asks small-bias inputs not to lose non-rest density exactly, for count-monotone automata only, and no equivalence with surjunctivity is known.
  finite-injective-charge-noncreation-forces-surjectivity: that is charge noncreation for finite-injective automata with a quiescent symbol; this is the count statement for a reversible automaton that never lowers the count, obtained by applying that theorem to the inverse with unit charge.
artifacts:
  - experiments/track-deficit-2026-09-17/deficit.py
---

**ESTABLISHED** by `rest-count-preservation-from-charge-noncreation`, from
`finite-injective-charge-noncreation-forces-surjectivity`, over every group.

Let `G` be a countably infinite group, `A` a finite alphabet, `a ∈ A`, and `ψ` a bijective cellular
automaton on `A^G` with `ψ(a^G) = a^G`. For `x` with finitely many sites outside `a`, write `|x|` for their number.
If `|ψ(x)| >= |x|` for every such `x`, then `|ψ(x)| = |x|` for every such `x`.

Equivalently, with `Φ = ψ^-1`: an injective automaton fixing `a^G` that never raises the count, and restricts to a
bijection of the finitely supported configurations, never lowers it.

**Why it matters.** It is item 6.2 of `notes/gottschalk-surjunctivity-conjecture-frontier-swarm-2026-09-16.md`. Take
`C = A ⊔ {*}` and an injective automaton on `C^G` whose output star set is `ψ(Z)` whenever the input star set is
`Z`, for a bijective `ψ` on `{0,1}^G` fixing all-stars. Injectivity makes `ψ` never lower the non-star count, and
count preservation makes the design surjective (`count-raising-reversible-automata-lower-biased-rokhlin-entropy`,
first consequence). So this claim kills every such design, over every group, as a route to a strict automaton.

**Known cases.**
- **Sofic groups.** They have infinite Rokhlin supremum, so the established theorem forbids a count-raising `ψ`.
- **Any group with a free ergodic action of positive Rokhlin entropy.** Its supremum is positive
  (`positive-rokhlin-entropy-action-gives-positive-supremum`), and the same theorem applies. This gives the route
  `reversible-count-preservation-from-positive-rokhlin-entropy`.
- **Low counts, over every group, binary alphabet.** Counts 1 and 2 are kept (part B of
  `count-raising-reversible-automata-rokhlin-deficit-proof`).
- **Finite groups** are excluded by hypothesis. There the statement holds trivially: summing `|ψ(x)| - |x| >= 0`
  over the finite set `A^G` gives `0`.

## Attempts

- **Induction on the count** (solo follow-up, 2026-09-17). Singletons and pairs split into finitely many near
  translation classes and far ones that `ψ` fixes up to a uniform shift. So an injection that lands among near
  classes is a bijection of them. From count 3 on, a near cluster can map to a far one, the far thresholds grow
  with the count, and the class count is no longer finite. It dies there.
- **Charge expansion.** With binary alphabet, the change `|Φ(Z)| - |Z|` expands as `Σ_{∅ ≠ V ⊆ Z} Γ(V)`, where
  `Γ` is translation invariant and supported on subsets of translates of the memory. A first loss sits at a set
  `V` of size `m >= 3` inside one translate of the memory. That confines the witness but gives no contradiction
  without a measure on the group, and the measure argument needs a positive Rokhlin supremum.
- **Charge noncreation on the inverse** (a-gs-track-deficit, swarm-0917, 2026-09-17). Closes the claim over every
  group: route `rest-count-preservation-from-charge-noncreation`. `τ = ψ^-1` is an automaton fixing `a^G`, and it
  never raises the count, because `|τ(y)| = |x| <= |ψ(x)| = |y|` with `x = τ(y)`. Unit charge off `a` in
  `finite-injective-charge-noncreation-forces-surjectivity` gives equality. The same step, applied to `Φ`, shows the
  hypothesis of `count-raising-reversible-automata-lower-biased-rokhlin-entropy` is never satisfied. So item 15 was
  never tied to the Rokhlin barrier, and the Rokhlin route is superseded.
- **Deficit as a transport index** (lane (b) of `notes/agent-coordination-playbook-2026-09-17.md`; same agent).
  This was a failed approach, recorded as a dead end. The script `experiments/track-deficit-2026-09-17/deficit.py`
  computes the exact `H(x | Φx)` over F_2 windows for designs 6, 6c and 7, with `A = (Z/2)^2` and reversible `τ` in
  {id, shift, shear, shear∘swap∘shear}.
  - **Invariance fails.** On `W = {e,a,b}`, design 6 has deficit 0 for `τ = id` and 3.52 bits for `τ = shift`.
  - **No uniform value.** The shear, which both raises and lowers counts, has deficit 0 in design 6. Design 7 gives 1.50, 0.35, 1.45 and 1.42 bits for the four `τ` on `W = {e,a,b,ab}`, none of them
    `log2|A| = 2`.
  - **Where it dies.** At the first step of shape (1), invariance under composing `τ` with a reversible automaton.
    The count change is a cocycle along compositions, not an invariant, so no deficit value can name the gate.
  - **What replaces it.** The surviving gate is creation. Design 6c writes `*` only at star sites where `τ(Fx)` is
    `a_0`. For injective `τ` it is injective exactly when `τ` never turns a vacuum site non-vacuum. If `τ` creates at a star
    site, filling that star by `a_0` gives a colliding input. If `τ` never creates, the output star set equals the
    input star set and the output determines `τ(Fx)`, hence `x`. The script asserts the no-creation direction on its
    windows. A strict design with a vacuum
    must raise every positive charge on some finite configuration.
