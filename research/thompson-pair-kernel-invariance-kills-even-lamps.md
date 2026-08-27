---
rg: 2
id: thompson-pair-kernel-invariance-kills-even-lamps
kind: claim
title: Actor-invariance of the pair kernel kills an exact even-lamp representation
distinct_from:
  thompson-even-lamp-fp-finite-state-detector: that assumes an exact finite-dimensional representation of the whole semidirect product and argues through joint character supports; this assumes no actor representation at all and consumes only the two-point kernel relation of the lamp restriction.
  finitary-alternating-augmentation-lamp-global-rounding-no-go: that is a locally finite counterexample to global semidirect rounding; this is a positive lemma about one exact lamp representation whose pair kernel is approximately actor-invariant.
  finite-presentation-must-expose-whole-module-with-uniform-defect: that asks for uniform multiplicativity over all module elements before rounding; this consumes a bound over two-point lamps only, and only after an exact lamp representation already exists.
artifacts:
  - research/artifacts/finite-memory-pair-kernel-audit-2026-08-23.md
---

ESTABLISHED.  Let a group `A` act transitively on a countably infinite set
`X`, let `S` be a finite symmetric generating set of `A`, and suppose `A` has
no nontrivial finite quotient.  Write

```text
I_X = ker(sum : F_2^(X) -> F_2),
b_(x,y) = e_x + e_y.
```

Let

```text
rho : I_X -> U(d)
```

be an **exact** homomorphism (`d` finite).  If for every `s in S`

```text
rho(b_(x,y)) = I   =>   ||rho(b_(s x,s y)) - I||_op < 2       (PKI1)
```

for all `x,y in X`, then `rho` is trivial on `I_X`.

Three ingredients.

1. **Discreteness.**  `rho(m)` is an exact involutive unitary for every
   `m`, so its spectrum lies in `{+1,-1}` and

   ```text
   ||rho(m)-I||_op in {0,2}.                                  (PKI2)
   ```

   Hence `(PKI1)` is not an approximate hypothesis at all: any strict bound
   below `2` forces `rho(b_(s x,s y)) = I` exactly.

2. **Finiteness.**  `x ~ y iff rho(b_(x,y))=I` is an equivalence relation,
   because `b_(x,z)=b_(x,y)+b_(y,z)`.  The image of `rho` consists of
   commuting involutions, hence is simultaneously diagonalizable and has
   order at most `2^d`; the class of `x` is determined by `rho(b_(x,x_0))`,
   so `X/~` has at most `2^d` elements.

3. **No finite quotient.**  By 1 and 2 each `s in S` maps classes to
   classes, and `S` is symmetric, so `A` acts on the finite set `X/~`.  That
   action is trivial, and transitivity then makes `~` universal.  Pair lamps
   generate `I_X`, so `rho = 1`.

For Thompson `V` acting on its countable Cantor orbit the hypotheses on `A`
hold: `V` is transitive and infinite simple.

**Scope, and the reason this is a lemma and not a target.**  The converse is
immediate — a trivial `rho` satisfies `(PKI1)` — so for a *fixed* exact `rho`
the hypothesis and the conclusion are logically **equivalent**.  Asking for
`(PKI1)` as a new prerequisite would therefore be a restatement dressed as a
reduction, not a smaller problem.  What the lemma genuinely buys is the shape
of the surviving witness: the analytic input needed is a bound on two-point
lamps only, not the whole-module modulus `(IWE6)` of
`infinite-character-actor-word-energy-interface`, and it is needed only up to
the constant `2` rather than as a modulus tending to zero.  The obstruction to
supplying that input from a finite presentation is
`exact-lamp-lifts-admit-moving-pair-kernel-jumps`.
