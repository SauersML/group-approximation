# Biography of the negation: "GL_n(Q) embeds in no finitely presented simple group"

Lane gq-inverter, gq swarm, 2026-09-17. Role inverter: assume the root
`gl-n-q-embeds-in-fp-simple-group` fails, list what that forces, and turn the
constraints into construction recipes. Status tiers: ESTABLISHED items are
landed nodes, agent-verified only. Items marked (remark) are not nodes.

## 1. The negation, normalized

From `gl-n-q-targets-are-cofinal-in-n`, `gl-n-q-embeddings-detected-by-nontrivial-homomorphisms`
(252700d24) and `gl-n-q-embeddings-are-branches-of-homomorphism-trees`
(94a11bab0):

- **Up-set in n.** If `GL_n(Q)` has no finitely presented simple host, neither
  has `GL_(n')(Q)` for `n' >= n`. The negation is "from some `n_0` on".
- **One inequality.** The root fails iff for all large odd `m` there is no
  finitely presented simple `S` and no homomorphism `SL_m(Q) -> S` with
  `e_12(1) ↦ nontrivial`. Injectivity is automatic, because `PSL_m(Q)` is
  simple.
- **Trees.** Equivalently, for all large odd `m`, every one of the countably
  many computable trees `T_S` (homomorphisms of `E_m(Z[1/k!])` keeping
  `e_12(1)`) has no infinite branch. The negation is `Π^1_1`, the root `Σ^1_1`.

## 2. What the negation forces

1. **Boone--Higman fails, with named witnesses.** By
   `gl-n-q-embeds-in-fg-simple-and-fp-decidable-groups` (a62eb875f), `GL_n(Q)`
   lies in a two-generated decidable `G*` and in a finitely presented decidable
   group. Under the negation both are Boone--Higman counterexamples, so
   `boone-higman-conjecture` fails for a finitely presented group, and so does
   `permutational-boone-higman-conjecture`.
   - Through `boone-higman-iff-simple-kazhdan-decidable-inputs` (ESTABLISHED
     per its node) there would then also be an infinite finitely generated
     simple Kazhdan counterexample with solvable word problem. (remark)
   - Mikaelian's announced explicit 2-generator finitely presented overgroup
     (arXiv:2507.04347 §1.4) would be a counterexample too if its word problem is
     solvable. (remark)
2. **Only the conjunction is missing.** Finitely presented plus decidable, and
   finitely generated plus simple plus decidable, are both achieved (a62eb875f).
   The negation says the two adjectives cannot be had at once, for this one
   countable input.
3. **A compactness failure.** Each `GL_n(Z[1/k!])` lies in `B_A`
   (`char-zero-linear-groups-satisfy-permutational-boone-higman`), hence has a
   finitely presented simple host. Under the negation, neither `B_A` nor the
   class of groups with finitely presented simple hosts is closed under this one
   ascending union.
   - By the Konig part of 94a11bab0, every finitely presented simple `S` then
     either misses some `GL_n(Z[1/k!])`, or embeds infinitely many
     `Aut(S)`-classes of some `GL_n(Z[1/k!])`.
4. **No finite certificate refutes a host that contains all finite groups.**
   `T_V` has every level nonempty, via reduction mod large primes into finite
   `SL_m(F_p) <= V`, and no branch (94a11bab0, item 3). So every refutation of
   a candidate host containing `V` must be infinitary: roots (Higman, O3),
   distortion (O4), residual finiteness (O1), property FW of `SL_3(Z)` (O2).
   A calibrator should never expect a finite search to kill a candidate.

## 3. What any host must contain (constraints for constructors)

(remark; elementary, from the matrices)

- **A divisible, scalable element.** Put `u = e_12(1)`.
  - `u` has roots of every order: `e_12(1/k)^k = u`.
  - `u` is conjugate to `u^a` for every nonzero integer `a`:
    `diag(a,1) u diag(a,1)^-1 = u^a`. In particular it is conjugate to `u^-1`.
  - So any host `S` has an infinite-order element with roots of all orders that
    is conjugate to all its nonzero powers. In `S`, `u` has zero translation
    length for every conjugation-invariant homogeneous length function.
  - This excludes hyperbolic and CAT(0) hosts, and it is the source of the
    exponential distortion in O4.
  - The minimal group carrying this is `Aff(Q)`, which by 252700d24 embeds as
    soon as some homomorphism keeps `t_1`.
- **n >= 3.** The host contains `SL_3(Z)`. Every action of a finite-index
  subgroup of `SL_3(Z)` on a CAT(0) cube complex fixes a point, and survey
  Remark 4.12 uses this to kill `VA`. Any host built from cube-complex
  actions with V-like vertex stabilizers dies the same way.
- **Envelope type.** The finitely generated simple host `G* V_(G*)` comes from
  the translation action, which never has finitely many orbits of pairs. A
  finitely presented host needs an overgroup of `GL_n(Q)` with a genuinely
  oligomorphic action (`gl-n-q-in-permutational-boone-higman-class`).

## 4. Could the negation be contradicted internally?

No contradiction was found. The negation implies the failure of Boone--Higman
and nothing else known to be false. It is consistent with every established
fact in the cone:
- every finitely generated subgroup embeds;
- `(Q,+)` and `Q^x` embed in `VA`;
- the known hosts `V`, `VA`, `T-bar` and Brin's `A` all fail for infinitary
  reasons.

A contradiction from the negation alone would prove the root.

## 5. Recipes (the negation turned around)

- **R1, one inequality.** Find, in a finitely presented simple `S` (ideally with
  a type (A) action), elements `y_ij(q)` satisfying a presentation of `SL_m(Q)`
  for one odd `m >= 3`, with `y_12(1) != 1`. By cofinality, one odd `m` for
  each of infinitely many values suffices. The Steinberg relations alone give
  `St_m(Q)`; the `K_2(Q)` symbols must also die.
- **R2, Aff(Q) first.** It is the minimal carrier of the scalable element. The
  host must contain the following, with `u` nontrivial:
  - `u`, with compatible roots `u_k` (`u_(k+1)^(k+1) = u_k`, `u_1 = u`);
  - commuting elements `d_p` (`p` prime) and an involution `d_(-1)`, with
    `d_p u_k d_p^-1 = u_k^p`;
  - `d_p^-1 u_k d_p = u_(k')^(k'!/(p·k!))` for any `k'` with `p·k!` dividing `k'!`
    (for example `k' = k + p`).

  Test every family on this before `GL_n`.
- **R3, rigidity plus Konig.** Find `S` in which embeddings of each
  `SL_m(Z[1/N])` fall into finitely many `Aut(S)`-classes. Superrigidity-type
  finiteness for higher-rank S-arithmetic groups inside a host would make
  coherence automatic.
- **R4, decouple uniformity from coherence.** A weaker necessary target: one
  finitely presented simple group containing a copy of `SL_m(Z[1/N])` for every
  `N`, with no compatibility required. If this fails, the root fails. If it
  holds, R3 is the remaining step. (Spark; not a node.)
- **R5, oligomorphic overgroups.** Aim at `B_A` membership through an overgroup
  of `GL_n(Q)` with finitely many orbits on pairs, never at `G*`-type
  envelopes.

## 6. Landed nodes of this lane

| Node | Landing | Status |
|---|---|---|
| `gl-n-q-embeds-in-fg-simple-and-fp-decidable-groups` (+ `-proof`) | a62eb875f | ESTABLISHED, assembly of survey theorems |
| `gl-n-q-embeddings-detected-by-nontrivial-homomorphisms` (+ `-proof`) | 252700d24 | ESTABLISHED, elementary plus Jordan--Dickson |
| `gl-n-q-embeddings-are-branches-of-homomorphism-trees` (+ `-proof`) | 94a11bab0 | ESTABLISHED, elementary |

None has been independently reviewed. None settles the root, Problem 2.7 or a
stepping stone, so no referee was requested.
