# The Wächter–Weiß check-mark automaton, layer by layer (bh-free-02, 09-18)

**Why this matters.** `pspace-fp-simple-via-lift-presented-automaton-overgroups` needs a
lift-presented automaton group containing one Wächter–Weiß group. The group's own action is the first
candidate. By `lift-presentation-passes-to-invariant-subalphabets`, that candidate needs the check-mark
group `C` to be lift-presented. Here `C` is analysed unencoded, as `C'`, layer by layer. Everything
below is proved by hand unless marked otherwise. None of it is run code.

## The automaton C'

Letters: `0, 1, γ, #, $`. Only `A` and `A'` move letters, swapping `0` and `1`; every state fixes
`γ`, `#` and `$`. Sections are listed in that letter order:

```text
A  = σ(Z, A', 1, 1, 1)     increment, block status unknown
A' = σ(N, A', 1, 1, 1)     carry, block known nonzero
Z  = (Z, N, K, 1, 1)       block zero so far
N  = (N, N, A, 1, 1)       block nonzero: at γ continue with A
K  = (K, 1, K, A, 1)       skip: zeros and γ only; at # restart with A; dies on 1
```

Source: Figure `fig:checkmarkingAutomaton` of arXiv:1906.03424v3, with continuation `id`. The figure's
code sends the `Γ`-edge of state 3 to an undefined node `(1)`; by the text it is the check-mark state.
`C` is the binary encoding of `C'`. Whether lift-presentation survives this prefix-code re-encoding
is **not proved**. Uniform regrouping is `lift-presentability-is-invariant-under-level-regrouping`.

## Layer 1: one configuration (no #)

On `{0,1,γ}^*`, `K` acts trivially. The restriction is `C_2`, and it is lift-presented by
`[A',N]` and `[Z,N]` (`single-configuration-check-mark-group-is-lift-presented`).

## Layer 2: configurations

Three separator facts, each immediate from the table:
- **(S1)** At `$`, every section is `1`.
- **(S2)** At `#`, every letter receives `#`. `K` goes to `A` and all other letters die, so
  `w|_# = A^{e_K(w)}`. For a relator this is freely trivial. So every path through `#` or `$` is good
  for the path-by-path criterion `lift-ideal-membership-is-decided-along-paths`.
- **(S3)** At `γ`: `A` and `A'` die, `Z` goes to `K`, `N` to `A`, and `K` to `K`.

So only paths in `{0,1,γ}^ω` matter, and on that subtree `K` acts trivially. That is how `K` hides.

### Two lamplighters

- **L1. `⟨A, K⟩ ≅ Z ≀ Z`.**
  - *The kernel is abelian.* An element trivial on configuration-1 words `{0,1,γ}^*` has sections at
    every `u#` that are powers of `A`, by (S2). So these elements form an abelian group `L`, embedded
    in `Z^{configs}`.
  - *The quotient is cyclic.* Restricting to `{0,1,γ}^*` gives `⟨A,K⟩ -> ⟨A|⟩ ≅ Z`, with kernel
    `L = ⟨⟨K⟩⟩`.
  - *The lamps are independent.* `A^n K A^{-n}` is the lamp at the configurations `A^n(0⋯0)`: the
    `#`-sections of `A^{±n}` cancel. On a first block of length `k` with `2^k` larger than the spread,
    these lamps are independent. So `L ≅ Z[t^{±1}]`.
- **L2. `⟨K, N⟩ ≅ Z ≀ Z`, with `N ↦ A`, and both generators are persistent at `0`.**
  - *Persistence.* `K(0) = N(0) = 0`, `K|_0 = K` and `N|_0 = N`.
  - *The recursion.* A word `w(K,N)` satisfies
    `w = (w, N^{e_N}, w(K,A), A^{e_K}, 1)`. So `w = 1` iff `w(K,A) = 1` in `⟨A,K⟩`: the exponent
    conditions follow, and uniqueness settles the `0`-coordinate.
  - *The full triple.* `⟨Z, N, K⟩ ≅ (Z ≀ Z) × Z`, through `(φ, e_Z)` with `φ: Z ↦ K, N ↦ A, K ↦ K`.
    It is a retract of `Stab(0^ω)` through the eventual section along `0^ω`, which is a homomorphism
    on the stabilizer.

### The crux

- **The relators involved.** The relators of `⟨K,N⟩ ≅ Z ≀ Z`, for example `r_n = [K, N^n K N^{-n}]`,
  are **fixed by the section at 0** (`r_n|_0 = r_n`). Their other sections are:
  - freely trivial at `1`, `#` and `$`;
  - the `⟨A,K⟩`-relator `[K, A^n K A^{-n}]` at `γ`.
- **Why lift steps cannot produce them.** A lift step never produces `r_n`, because the needed section
  is `r_n` itself. So `r_n` can enter a lift ideal only through normal closure.
- **The two families feed each other.**
  - *From L1 to L2.* The section at `0` of `[K, A^{2m} K A^{-2m}]` is
    `[K, (A'Z)^m K (A'Z)^{-m}]`, by `A^2 = (A'Z, ZA', 1, 1, 1)`. After about `log m` further digit
    steps the conjugator loses its `A'` letters and the word lands in `⟨Z, N, K⟩`.
  - *From L2 to L1.* The `γ`-sections go back to `⟨A,K⟩`.
- **Open question.** Do the relators of the persistent lamplighter `⟨K,N⟩`, together with their
  `A'`-conjugate variants, lie in a finitely generated lift ideal of `C'`?
  - **If not,** `C'` is not lift-presented. Given the encoding step, the finite-`R` Wächter–Weiß
    groups are then not lift-presented in their own actions, and the PSPACE rung needs a genuinely new
    overgroup.
  - **If so,** the path-by-path criterion should finish `C'`. The finite lamp group of the checkers
    remains after that.
- **What existing tools say.** Loop retraction is blind to this. The letters fixed by every state are
  `γ`, `#` and `$`, with eventual section groups `⟨K⟩` or `1`, which are finitely presented. The
  persistence is along a ray, `0^ω`, that `A` moves.

## A tool this suggests (open)

**Ray retraction?** Suppose a sub-automaton `S_0 ⊆ S` is persistent along a ray `ξ` that is not fixed
by all of `S`. Must `⟨S_0⟩` be finitely presented whenever `V_d(G)` is?
- It holds when `ξ = x^ω` with `x` fixed by all of `S`: that is loop retraction.
- The obstacle: the section along `ξ` is a homomorphism only on the preimage of `Stab(ξ)`, which has
  infinite index. So the normal-closure step of the loop-retraction proof does not transfer.
- The analogy: the persistent action of `Z/2 ≀ Z` has non-finitely-presented `V_4`
  (`persistent-automata-rn-group-fp-iff-group-fp`). That suggests the answer "no, `C'` is not
  lift-presented", but proves nothing.
