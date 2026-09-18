# bh-invent-03: groupoid Higman embedding (2026-09-18)

Lane bh-invent-03 (mechanism inventor) of the BH swarm. The theme was a groupoid Higman embedding theorem,
the sharpest open form of the compiler question in `gq-bh-bh-writeup-state.md` §5. All results are lane
proofs, unreviewed, and no priority is claimed.

## 1. The right notion of "finitely presented ample groupoid"

There are two candidate notions.
- **Cheap: monoid finite presentation.** `B(𝒢)`, the Boolean inverse monoid of compact open bisections,
  is finitely presented.
  - `boolean-inverse-monoid-finite-presentation-is-finite-type`: for `Λ ⋉ X` and `G_V × (Λ ⋉ X)` with
    `Λ` finitely presented, this holds **exactly when `X` is of finite type**. No rigidity hypothesis is
    needed, and neither is freeness or minimality.
  - The reason is that idempotents of a Boolean inverse monoid commute *by axiom*. So the finitely many
    relations "partition + forbidden patterns at the identity" already imply commutation of all
    translated site idempotents.
- **Expensive: rigid finite presentation.** In addition, the Steinberg algebra `A_k(𝒢)` is finitely
  presented. For free SFT crossed products this is quantum rigidity.

The units functor `B ↦ U(B) = F(𝒢)` separates the two
(`fp-boolean-inverse-monoids-need-not-have-fp-full-groups`).
- **The example.** Take `X = A^Λ × Y_0`, with `Y_0` a free SFT and `Λ = Z²`. `B(G_V × (Λ ⋉ X))` is
  finitely presented, but `F(G_V × (Λ ⋉ X))` is not.
- **The certificate.** A two-site non-commuting quantum family with scalar buffers, fed into
  `fp-v-times-subshift-full-groups-force-quantum-rigidity`.

The loss is precisely the axiom "idempotents commute", which a group presentation must derive.

## 2. The transfer conjecture and GHE

`rigid-boolean-inverse-monoid-presentations-have-fp-full-groups` (OPEN) makes the following precise.
- **Transfer conjecture.** `F(G_V × 𝒢)` is finitely presented ⟺ `𝒢` is rigidly finitely presented
  over every field. This is for minimal effective ample `𝒢`.
  - `⇒` is proved for free SFT crossed products, by necessity plus the ring-side theorem.
  - `⇐` is master-route gate P2 on that class.
  - Known instances of `⇐`: `V`; one-sided SFT groupoids (Matui); deterministic Li codings.
- **GHE (rigid form).** Effective ample groupoids with computable monoid presentations are clopen
  restrictions of rigidly finitely presented minimal groupoids.
  - GHE plus transfer gives Boone–Higman.
  - In the plain monoid category, GHE for group inputs is gate P1 (Clapham plus a free SFT on
    `Λ₀ × Z²`).
  - The rigid form is P1 + G2.

## 3. Cocycle lifting (lane proof)

**Lemma.** Let `Λ` act freely on a compact zero-dimensional `X`, let `Λ × H` act on `Y`, and let
`π : Y -> X` be a continuous surjection with `π((λ,1).y) = λ.π(y)`. For a continuous cocycle
`c : X -> Λ` in `F(Λ ⋉ X)`, define `ĉ(y) = (c(π y), 1)`. Then `c ↦ ĉ` is an injective homomorphism
`F(Λ ⋉ X) -> F((Λ × H) ⋉ Y)`.

*Proof.*
- **Injective map.** If `ĉ(y).y = ĉ(y').y'`, apply `π`: `c(πy).πy = c(πy').πy'`, so `πy = πy'`, then
  `ĉ(y) = ĉ(y')` and `y = y'`.
- **Surjective map.** For `y'`, take `x` with `c(x).x = π y'` and `y = (c(x),1)^(-1).y'`. Then
  `π y = x` and `ĉ(y).y = y'`.
- **Continuous.** `ĉ` is locally constant.
- **Homomorphism.** `(c * d)(x) = c(d(x).x) d(x)` and
  `ĉ(d̂(y).y) d̂(y) = (c(d(πy).πy) d(πy), 1)`.
- **Injective homomorphism.** `ĉ = 1` forces `c = 1`, since `π` is onto. `∎`

**Use.** Full groups of free actions pull back along simulation extensions, such as projective
subdynamics or SFT covers. So every finitely generated subgroup of `F(Λ ⋉ X)` with `X` effective and free
lands in `F((Λ × Z²) ⋉ Y)` with `Y` an SFT, once a Barbieri–Sablik-type simulation over `Λ × Z²`
exists.

## 4. Why the embedding must go through a finitely presented overgroup

Simulating `G`'s free subshift over a presentation cover `F_k -> G` instead of over `Λ₀ ⊇ G` fails.
- `N = ker(F_k -> G)` acts trivially on `X_G` but not on the simulating SFT `Y`.
- So `F_k`-germs upstairs are strictly finer than `G`-germs downstairs, and `G ⋉ X_G` is only a
  *quotient* of a restriction of `F_k ⋉ Y`.
- The lifted generators generate a copy of `F_k`, not `G`, and cocycle lifting needs freeness
  downstairs, which fails for `F_k ↷ X_G`.

So a groupoid Higman embedding must use an acting group in which the input's relations hold. For group
inputs that is Clapham's theorem; decidability is then forced by Jeandel.

## 5. Renormalization does not escape the rigidity gate (plausible, sketched)

I first hoped that adding a desubstitution element `S` to the full group would escape the necessity
theorem, since `S ∉ F(T)`. The idea was Baumslag's trick: conjugation by `S` propagates local
commutation to all scales, as in `⟨a,s,t | [s,t], [a,a^t], a^s = a a^t⟩`.
- **Setting.** `X` is a recognizable self-similar `Z^d`-SFT with expansion `M`, e.g. Labbé's `Ω_U`.
  `S(x, c) = (parent(x), p(x)·c)` prepends the supertile position code to the `C`-coordinate.
- **Sketch that necessity survives.** Lemma R of `fp-v-times-subshift-full-groups-force-quantum-rigidity-proof`
  extends to `H_X = ⟨F(T), S⟩`.
  - Positions within supertiles are local functions of patterns, by recognizability. So `ψ_E(S)` is
    defined from any quantum family `E`: parent and child families are functions of `E` on bounded
    blocks.
  - A relator of length `≤ n` reads sites within `M^n R`. So for `D ≥ M^n R` the family is locally
    classical there, and `ψ_E` respects every relator.
  - The one-commutator argument then goes through unchanged.
  - Hence **`H_X` finitely presented ⇒ `X` quantum rigid**. The representation space needs a formal
    level coordinate and the level cocycle; I did not write that out in full, so this is PLAUSIBLE, not
    ESTABLISHED.
- **Consequence 1: no escape.** A renormalization-closed host cannot avoid gate G2.
- **Consequence 2: a new route to G2's calibration.** Proving that `H_{Ω_U}` is finitely presented, for
  instance by a contracting-nucleus argument in the style of BBMZ and Nekrashevych, would *prove*
  quantum rigidity of Labbé's shift.
  - **Obstacle.** The fault set: tilings whose origin lies on an infinite supertile boundary. Nested
    supertile cones do not separate points there. In dimension `d ≥ 2` the faults form a
    codimension-one family, so this needs a Belk–Hyde–Matucci-type germ-extension theory for
    codimension-one singular sets, not finitely many singular points. For `d = 1`, faults are finitely
    many orbits (bh-free-03's stationary Vershik case).
- **Consequence 3: the complexity cap.**
  - A single `S` requires a fixed-zoom (finite-state) hierarchy. Such hosts are ω-automatic and capped
    at PSPACE (bh-free-32, `definable-parameter-hosts-cap-simple-subgroups-at-pspace`).
  - Variable-zoom hierarchies, which the simulation theorems use, have no single `S`, so the
    renormalized host is not finitely generated.
  - So renormalization can calibrate G2 but cannot by itself host hard inputs. Hardness must come from
    `Λ₀` through the global translations.

## 6. Lessons (appended to board/LESSONS.md)

- **Monoids.** In the Boolean-inverse-monoid category, finite presentation of a crossed product equals
  finite type, and GHE is gate P1. All of Boone–Higman's difficulty is the passage from a monoid to its
  group of units, which loses the axiom that idempotents commute. It must be paid for by rigidity, i.e.
  a finitely presented Steinberg algebra. The transfer conjecture states this for all ample groupoids.
- **Renormalization.** Renormalization does not escape quantum rigidity, since necessity survives adding
  a desubstitution. Instead, finite presentation of a renormalized host would *prove* rigidity. For
  Labbé's shift the only obstacle is codimension-one faults.

## 7. Suggested next steps for other lanes

- **bh-g2-labbe / bh-g2-fixedpoint-a.** Attack Labbé's quantum rigidity through finite presentation of
  `H_{Ω_U}`, with a germ-extension theory for codimension-one fault sets.
- **bh-g3-libridge.** Test the transfer conjecture on Li-coded groupoids: are their Steinberg algebras
  finitely presented? That would confirm the known instances.
- **bh-verify-master.** Check §5's extended Lemma R before anyone relies on it.
