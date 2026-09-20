---
rg: 2
id: thompson-v-is-not-mf
kind: claim
title: Thompson's group V is not MF
distinct_from:
  thompson-v-not-hyperlinear: that excludes approximate unitary models in the normalized Hilbert--Schmidt length; this excludes them in operator norm, which neither implies nor is implied by it for a general group.
  thompson-v-not-lef: that is the classical exclusion of exact local embeddings into finite groups; this excludes operator-norm asymptotic unitary representations, which LEF-failure does not control.
  leavitt-mf-quotients-see-thompson-vd-through-parity: that shows every MF quotient of the Leavitt unit group sees V at most through parity, which is a statement about the ambient's approximations; this is about V's own approximations, which need not extend to the ambient.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that excludes exact finite-dimensional unitary representations; this excludes approximate ones in operator norm.
  kazhdan-free-leavitt-collapse-typing-dichotomy: that shows any image-typed Kazhdan-free collapse produces a non-MF Kazhdan-blind group; this names the most economical such group, V itself.
---

**OPEN.** Thompson's group `V = G_(2,1)` does not embed in the operator-norm
ultraproduct of unitary groups `prod_omega U(n) / {(u_n) : ||u_n - 1||_op -> 0}`.

Because `V` is simple, the following are equivalent:
- `V` is not MF;
- `Rad_MF(V) != 1`;
- `Rad_MF(V) = V`.

**Kazhdan blindness.** `V` has the Haagerup property
(`thompson-v-has-haagerup-property`). So every Kazhdan subgroup of `V` is
finite, and every homomorphism from a Kazhdan group to `V` has finite image.
`V` is finitely presented (`thompson-v-finitely-presented-infinite-simple`),
so by compactness a proof of this claim can be taken to be a statement about
`V`'s own finite presentation. Every certificate group for this claim
surjects onto `V`, and so is not Kazhdan. This is the opposite of the
situation in `kazhdan-free-leavitt-collapse-typing-dichotomy` (b).

The Kazhdan compression engine is vacuous here:
`thompson-v-has-no-rigid-compression-defect` shows that every rigid pair
inside `V` is finite with trivial defect, in every ambient group.

**Consequences.**
- `property-t-free-leavitt-via-thompson-v-not-mf`: this claim closes the
  Kazhdan-free Leavitt goal, in the image-typed sense.
- It would give the first recorded non-MF group with the Haagerup property.
- It is implied by the non-MF-ness of any subgroup of `V`, for example
  Thompson's `F` or `T`. For `F` that is stronger than non-amenability of `F`,
  since amenable groups are MF.

## Attempts

1. **K-theory, trace and rational-cohomology lanes are dead** (swarm-0917 w16,
   2026-09-19). See `thompson-v-k-shadow-cannot-detect-mf`.
   - By simplicity, MF for `V` is the nonvanishing of the single rank class
     `r(Ψ(p_s))` of `p_s = (1-s)/2`.
   - Traces on `K_0(C*V)` are rational, by Higson--Kasparov and Lück Theorem
     0.3. So the positive integer shadow `a_n ε_* + b_n τ_*` satisfies every
     ordered-`K_0`, unit, character-simplex and finite-subgroup-packet
     constraint, and gives that class the value `b_n/2 ≠ 0`.
   - `H^(2k)(·; Q)`, `k ≥ 1`, vanishes for `V` and for every torsion
     centralizer (`thompson-v-torsion-centralizers-are-rationally-acyclic`).
     So Dadarlat-type and delocalized cohomological obstructions have no input.

   Death step: any such argument must conclude `r(Ψ(p_s)) = 0`. A proof must
   use data that is not homotopy invariant, namely operator-norm defects of
   the infinite-order relators and how local models glue.

2. **swarm-0917 (ptl-last1), operator-norm defect gap: a reduction, with numerics that carry no weight.**
   The hole stays **OPEN**.
   - **Reduction (ESTABLISHED, written proof).**
     - Claim: `thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes`, via
       `thompson-v-mf-iff-opnorm-s4-s3-defect-gap-proof`. Take `G0 = S4 *_Z2 S3`, so that
       `V = G0/<<r5..r8>>`.
     - Statement: this claim holds **iff** there is `epsilon_0 > 0` such that every nontrivial irreducible
       finite-dimensional unitary representation `sigma` of `G0` has
       `max_i ||sigma(r_i) - 1||_op >= epsilon_0`.
     - Proof steps:
       - operator-norm correction of the two finite subgroups;
       - aligning the two copies of `a` by a unitary `Z` with `||Z - 1|| <= ||S - T||`;
       - simplicity of V, together with `||rho(a) - 1|| = 2` for an exact nontrivial involution, so no
         amplification is needed.
     - Consequences:
       - each `delta_n` is attained and `> 0`, and `delta_1 = 2`;
       - "V MF" is an explicit Pi_2 sentence over Tarski-decidable matrix problems.
     - Unlike the tracial and sofic criteria, a single low-defect irreducible summand is already a witness,
       because padding only adds trivial summands. The whole hole is therefore a **uniform-in-dimension lower
       bound for exact representations of a virtually free group**.
   - **Permutation models are dead (elementary).** Let `rho` be a nontrivial permutation representation of
     `G0`, e.g. through a finite quotient acting on a set. Then `D(rho) >= sqrt 3`.
     - **Invariant.** The spectrum of a permutation matrix `P != 1`: each cycle of length `m >= 2` carries
       all `m`-th roots of unity, so `||P - 1|| >= 2 sin(pi floor(m/2)/m) >= sqrt 3`.
     - **Where it dies.** If `D(rho) < sqrt 3`, every `rho(r_i)` is the identity, so `rho` factors through V.
       It is then trivial by `thompson-v-has-no-nontrivial-fd-unitary-representation`.
     - **Consequence.** Any MF witness sequence must leave the permutation (and finite-quotient-permutation)
       class for good.
   - **Computation.** All files are in `experiments/thompson-v-opnorm-defect-gap-2026-09-17/`.
     - `delta_2` is in `[1.92374, 1.92385]`, by a Lipschitz grid scan in `scan_n2.py`.
     - Local-search upper bounds for V (`delta_n.py`, `out_V.json`) for `n = 3..7` are
       `1.744, 1.688, 1.680, 1.698, 1.702`, so `delta_7 <= 1.680`.
   - **Calibration FAILS. Do not repeat local search on `delta_n`.**
     - The planted PSL(2,17) word set gives the same plateau at `n <= 9`: `2, 1.84, 1.69, 1.71, 1.60, 1.65,
       1.65, 1.66, 1.70` (`out_CTRL2.json`). At `n = 9` it misses its own exact solutions, the two
       9-dimensional irreducibles of PSL(2,17).
     - On the pattern of its exact 17-dimensional Steinberg representation (`D = 5e-15`), the same search
       stalls at `1.764`. With a Frobenius warm start it stalls at `1.766` (`calibrate_ctrl2.py`).
     - So values `~1.6-1.77` are a landscape artifact for words of length 26-37. They are not evidence of a
       gap.
     - Any computational attack on the gap needs either certified lower bounds, e.g. a Lipschitz scan or a
       sum-of-squares relaxation over `U(n-k) x U(k)`, or a structured ansatz for witnesses. Blind search
       in the normal form does neither.
   - **Next hole.** The uniform gap for irreducibles of `G0`. Neither of the following is proved:
     - the case of irreducibles whose restriction to `S4` has bounded multiplicity pattern type;
     - a spectral-gap argument on the representation variety.

3. **swarm-0917 (w17 nh-break, host-geometry): class kill by the Lie closure; the hole stays OPEN.**
   - **Result (ESTABLISHED, written proof, unreviewed).** Claim:
     `thompson-v-gap-witnesses-need-unbounded-lie-closure`, via
     `thompson-v-gap-witnesses-need-unbounded-lie-closure-proof`. For a nontrivial irreducible
     `sigma` of `G0`, let `K` be the closure of `sigma(G0)` and `N_sigma = dim [Lie K, Lie K]`.
     - A nontrivial permutation of an orthogonal block decomposition forces `D >= sqrt 2`. So monomial
       models (torus regauges with arbitrary phases) and all induced models die.
     - If `K^0` is abelian (for example, finite or virtually abelian image), then `D >= 1/2`.
     - **Adjoint transfer:** `D(sigma) >= min(1/2, delta_(N_sigma)/2)`, uniformly in `dim sigma`.
     - If `D < 1/4`, then `sigma` restricted to `K^0` is irreducible.
   - **Invariant:** `N_sigma`, the dimension of the derived algebra of the closure.
   - **Death step (for every class with `N_sigma` bounded by `N`):** the adjoint action of `G0` on
     `[Lie K, Lie K]_C` is a nontrivial representation of dimension at most `N`, with defect at most
     `2 D(sigma)` (Hilbert--Schmidt contraction `||Ad(u) - 1|| <= 2||u - 1||`). It is gapped by
     `delta_N > 0`. If it is trivial, `K^0` is central and a Frobenius commutator descent inside the
     finite group `K/K^0` forces `D >= 1/2`.
   - **Dead model classes:**
     - tensor powers, Schur functors and `Sym^m` towers of a fixed representation;
     - more generally, `pi o phi` for any fixed compact Lie group `M`, which has
       `D >= c_(dim M) > 0`;
     - finite-image, virtually abelian, monomial and induced models;
     - `tau (x) pi` with a nontrivial finite projective factor `pi`.
   - **Survivors.** Any MF witness sequence `sigma_j` must eventually be primitive and
     Lie-irreducible, with `N_(sigma_j) -> infinity`. Examples are closures equal to `SU(n_j)` or to
     simple groups of growing dimension. The adjoint representations of such a sequence form a second
     witness sequence.
   - **Next hole.** The uniform gap on Lie-irreducible `sigma` whose closure is large. A natural next
     step is to show that witnesses can be taken with Zariski-dense image in `SU(n)`, and then to look
     for a quantitative obstruction there, for example a Weyl-equidistribution or Kazhdan-type
     spectral gap for the two finite subgroups `S4` and `S3` inside `SU(n)`.
3. **swarm-0917 w17 (ptl-break), the amenable-image locus is gapped at 1/2: a class kill.** The hole stays **OPEN**.
   - **Result (ESTABLISHED, written proof).** Claim: `thompson-gap-witnesses-need-nonamenable-image`, via
     `thompson-gap-witnesses-need-nonamenable-image-proof`.
     - Every nontrivial representation `rho` of `G0 = S4 *_Z2 S3` whose image is virtually solvable (by Tits,
       equivalently amenable, or free of `F_2`) has `D(rho) >= 1/2`, in every dimension.
     - The same holds for pairs `A^4 = B^3 = 1` against the Lochak--Schneps relators of T.
   - **Invariant.** The Frobenius ball.
     - In a virtually solvable subgroup of `U(n)`, elements within `1/2` of `1` commute (dimension-free).
     - The proof runs the commutator descent `h -> [g,h]` into the toral identity component of the closure,
       which a near-identity normalizer must centralize, and then back-tracks by the eigenspace lemma.
   - **Where every member dies.**
     - The relator images and their conjugates commute, so their normal closure `N` is abelian.
     - `image/N` is a virtually solvable quotient of the simple group V, so it is trivial and the image is abelian.
     - `rho` then factors through `G0^ab = Z/2`, where the sign character pays `||rho(r5) - 1|| = 2`. For T, the
       characters of `Z/12` pay at least `2 sin(pi/12)`.
   - **Kills.**
     - finite quotients of `G0`, of every kind (not only permutation models, which entry 2 had at `sqrt 3`);
     - monomial and induced-from-character models;
     - virtually abelian and solvable images.
     - A sanity run over 419 random monomial gluings gives min `D = 1.95`
       (`experiments/amenable-image-gap-witnesses-2026-09-17/`).
   - **Consequences.**
     - An MF witness sequence for V (or T) must consist of representations whose image contains `F_2` once
       `D < 1/2`: the Zassenhaus descent must converge without terminating.
     - The finite PSL(2,17) planted control of entry 2 is structurally the wrong calibration class: its exact
       solutions have finite image, which is impossible for V below 1/2.
   - **Next hole.** The uniform gap on the Tits-free locus. A first test class is images whose closure has
     identity component of bounded semisimple rank (e.g. `SU(2)^m`-by-finite), where Lemma 4 of the route fails.
4. **swarm-0917 w21 (nh-break, census-computation), 2026-09-20: which relators can carry the gap.** The hole
   stays **OPEN**.
   - **Result (ESTABLISHED, exact computation).** Claim: `thompson-v-single-relator-quotients-have-no-small-images`.
     Put `Gamma_S = G0/<<S>>` for `S` inside `{r5,...,r8}`.
     - `eta(r5) = eta(r8) = -1` and `eta(r6) = eta(r7) = +1`, so `Gamma5` and `Gamma8` are perfect.
     - `Gamma5` and `Gamma8` have no nontrivial homomorphism to `PGL(2,F)` for any field `F`. This is exact
       in characteristic 0 and in every characteristic `p`, including 2 and 3.
     - They have no nontrivial action on at most 16 points (9593374 actions at `m = 16`).
     - They have no nontrivial map to `U3(3)`, `L3(4)`, `U4(2)`, `U3(4)`, `U3(5)`, `J1` or `L3(5)`.
     - Hence every nontrivial finite quotient has a simple quotient of order at least `|M22| = 443520`.
     - Files: `experiments/thompson-v-relator-blind-2026-09-17/`.
   - **Class kill: gap proofs that use only `r6`, `r7`.**
     - *Invariant:* the sign character `eta`.
     - *Death step:* `eta` is a nontrivial exact representation with `eta(r6) = eta(r7) = 1`. So no bound on
       `max(||sigma(r6) - 1||, ||sigma(r7) - 1||)` alone can be uniform.
     - Every proof of the gap of entry 2 must read `r5` or `r8`, in every dimension.
     - `r6` and `r7` are individually weak words. In each simple group above they have 20 to 300 times the
       random-word solution count.
   - **New decomposition: one-relator strengthenings.**
     - `Gap(r5)`: there is `epsilon > 0` with `||sigma(r5) - 1|| >= epsilon` for every nontrivial irreducible
       unitary `sigma` of `G0`. `Gap(r8)` is the same for `r8`.
     - Each implies this claim.
     - Every exact obstruction to them tested so far is absent.
     - If `Gamma5` has no nontrivial finite quotient, entry 3's form (A) gives `Gap(r5)` at `1/2` on the whole
       virtually solvable-image locus, without using that V is simple.
   - **Calibration (the evidence is weak).**
     - `chi(G0) = -7/24`.
     - `r5` and `r8` hit zero exactly as random words would: about 1 expected solution per simple group.
     - So the computation does **not** distinguish "`Gamma5 = V`" from "`Gamma5` is a large one-relator group
       with no small quotients". Do not extend the finite census to larger simple groups expecting it to
       decide this.
   - **Next hole.** Decide whether `Gamma5 = V`, that is, whether `r6, r7, r8` lie in `<<r5>>` in `G0`.
     - If yes, V is a one-relator quotient of `S4 *_Z2 S3`, and this claim is exactly `Gap(r5)` for a single
       word. That would be the most compressed form of the hole.
     - If no, look for a nontrivial finite-dimensional unitary representation of `Gamma5`. It would kill `Gap(r5)`
       but not this claim, and it would show which of `r6`, `r7`, `r8` the gap must read.
     - A bounded shortlex Knuth--Bendix run (`kb_r5.py`, rule length at most 22, 36244 rules) reduced none of
       the three words, whose residues kept lengths 28, 26 and 37. The system is not confluent, so this is
       inconclusive. Do not repeat it at this scale.
