# RBS invariant random subgroups carry no strict design (2026-09-18)

Agent `swarm-0917-w10-w10-gs-last1`, wave swarm-0917. Target hole:
`non-co-sofic-free-group-irs-carry-no-strict-design`, the single open prerequisite of
`irs-surjunctivity-via-rank-corrected-co-sofic-split` and `gottschalk-via-irs-surjunctivity`.

Source: L. Bowen and M. Chapman, *Surjunctivity does not characterize cosoficity of invariant random
subgroups*, arXiv:2511.06586v1 (HTML version, fetched 2026-09-18 with `curl`, tags stripped, and MathML
replaced by its `alttext`). The quotes in `bowen-chapman-rbs-irs-surjunctivity-toolkit` are from that text.

## 0. Dictionary

Repo setting: `research/artifacts/irs-surjunctivity-heretic-2026-09-17.md`, Section 2. There, `Gamma = F_r`
acts on the right on `X_H = H\Gamma`, and a design `D = (tau, sigma)` is a pair of shape-dependent automata of
radii `R_tau, R_sigma`, with `r = R_tau + R_sigma`. The IRS `mu` **carries a strict design** if
`eps_D(mu) = 0 < delta_D(mu)` for some `D`.

Bowen–Chapman setting (BC). `sub(F, Sigma)` is the set of pairs `(K, c)` with `K <= F` and `c : F -> Sigma`
`K`-invariant, i.e. constant on the right cosets `Kx`. So `c` is a colouring of the vertex set `K\F` of the
Schreier graph of `K`, rooted at the coset `K`. `P(K, c) = K`, and `Dom(pi) = P^-1(supp pi)`. The group acts by
`w.(K, c) = (w K w^-1, w.c)` with `(w.c)(x) = c(w^-1 x)`. The measure is `u_pi = E_{K ~ pi}[1_K x u_K]`, with
`u_K` iid uniform on the cosets.

The map `phi_w : K\F -> (wKw^-1)\F`, `Kx -> wKx`, is well defined, because `wKw^-1 . w x = wKx`. It preserves
the right action, since `Kx.a -> wKxa`. It sends the root `K` to the coset `wK`. It carries `c` to `w.c`,
because `(w.c)(wx) = c(x)`. So `phi_w` is an isomorphism of coloured labelled Schreier graphs from
`(K\F, c)` to `(wKw^-1\F, w.c)`.

The isomorphism need not fix the root: it sends the root `K` to `wK = (wKw^-1) w`. This is harmless, because
shape-dependent automata commute with every label-preserving isomorphism, rooted or not. Also
`(c o phi_w^-1)(wKw^-1 y) = c(w^-1 y) = (w.c)(y)`, so `w.c = c o phi_w^-1`.

## 1. The bridge lemma

**Lemma B.** Let `pi` be an IRS of `F = F_r` and `D = (tau, sigma)` a design with `eps_D(pi) = 0` and
`delta_D(pi) > 0`. Define `Phi : Dom(pi) -> Dom(pi)` by `Phi(K, c) = (K, tau_K c)`, where `tau_K` is `tau`
acting on colourings of `K\F`. Then `Phi` is a cellular automaton on `pi` in the sense of BC Definition 1.5,
it is injective on a `u_pi`-conull set, and it is not surjective. So `pi` is not surjunctive in the sense of BC
Definition 1.6.

*Proof.* We check four things.

1. *`Phi` is a BC cellular automaton.*
   - `P o Phi = P` holds by construction, so `Phi` maps `Dom(pi)` into itself.
   - For `x in F`, `(tau_K c)(Kx)` is the rule of `tau` applied to the coloured ball `B_R(Kx)`. Its shape is
     decided by whether finitely many words of the form `x u x^-1` lie in `K` (with `|u| <= 2R + 1`), and its
     colours are values of `c` at finitely many points `xu`. So the map is continuous in the product topology.
   - Conjugate invariance: `phi_w` is a label-preserving isomorphism with `w.c = c o phi_w^-1` (Section 0). So
     `tau_{wKw^-1}(w.c) = (tau_K c) o phi_w^-1 = w.(tau_K c)`, which is `Phi(w.(K, c)) = w.Phi(K, c)`.
2. *Injective almost everywhere.*
   - `eps_D(pi) = 0` and invariance make every vertex of `K\F` forward-good for `pi`-a.e. `K` (heretic
     Section 2, Definition). The argument: `F` is countable, and vertex `Kx` of `K` is the root of
     `x^-1 K x`, which has law `pi`.
   - So `sigma_K tau_K = id` on all of `Sigma^(K\F)` for `K` in a `pi`-conull set `S_0`.
   - Hence `Phi` is injective on `P^-1(S_0) ∩ Dom(pi)`, which is `u_pi`-conull.
3. *An open set of `Dom(pi)` of positive measure.*
   - Reverse-badness of the root is decided by the shape of `B_r(K)`, and there are finitely many shapes.
   - So some shape `s` has `pi(B_r(K) has shape s) > 0`, and some colouring `p` of the shape `s` has
     `tau sigma p (root) != p(root)`.
   - Put `O = {(K, c) in Dom(pi) : B_r(K) has shape s and c|B_r(K) = p}`. It is open in `Dom(pi)`, and
     `u_pi(O) = pi(shape s) * |Sigma|^(-|s|) > 0`.
4. *`Phi` misses `O`.*
   - Take `K in S_0` and suppose `Phi(K, c) = (K, y)` with `(K, y) in O`.
   - Then `y = tau_K c`, and `sigma_K tau_K = id` gives `tau_K sigma_K y = tau_K sigma_K tau_K c = tau_K c = y`.
   - But `(tau sigma y)(root)` depends only on `y|B_r(root) = p`, and it differs from `p(root) = y(root)`.
     This is a contradiction.
   - So `Phi^-1(O) ⊆ P^-1(Sub(F) \ S_0)`, a `u_pi`-null set.
   - `Phi^-1(O)` is open in `Dom(pi)` by continuity. BC state that `supp(u_pi) = Dom(pi)` (proof of their
     Theorem 3.6), so every nonempty open subset of `Dom(pi)` has positive `u_pi`-measure.
   - Therefore `Phi^-1(O)` is empty. Since `O` is nonempty, `Phi` is not surjective.
   - Also `(Phi_* u_pi)(O) = 0 < u_pi(O)`. So `Phi` fails surjectivity in the measure sense as well.

This proves Lemma B. `∎`

The theorem is stated for "(almost everywhere) injective" automata. The proof of BC Theorem 3.6 (quoted in the
toolkit) uses injectivity only through two facts:
- stabilizers are preserved `u_pi`-a.e.;
- `Phi_* u_pi` is isomorphic to `u_pi`.

Both need only injectivity on a conull set. So Lemma B meets its hypothesis in either reading, and its
conclusion fails in both the topological and the measure reading of "surjective".

## 2. Theorem R and consequences

**Theorem R.** If an IRS `pi` of `F_r` satisfies the RBS criterion (BC Definition 3.5), then `pi` carries no
strict design.

*Proof.* BC Theorem 3.6 says `pi` is surjunctive in the sense of BC Definition 1.6. Lemma B turns a strict
design into an a.e.-injective, non-surjective BC automaton on `pi`, which is a contradiction. `∎`

**Corollary R1 (a second proof of the co-sofic case).** Every co-sofic IRS carries no strict design.
- BC Corollary 5.4: every cosofic IRS satisfies RBS.
- BC cosofic means a weak-* limit of finitely described IRS. That is the repo's co-sofic: weak-* limits of the
  laws of `Stab(o)` with `o` uniform in a finite `F`-set.
- This recovers the qualitative content of `co-sofic-free-group-irs-carry-no-strict-design` independently. It
  does not recover that node's linear bound `delta <= C eps`.

**Corollary R2 (where a counterexample must live).** Suppose some IRS `pi` refutes
`non-co-sofic-free-group-irs-carry-no-strict-design`.
- Then `pi` fails RBS. So for some finite `Sigma`, the Bernoulli bundle has Rokhlin entropy relative to `P`
  strictly below `log|Sigma|`.
- BC Theorem 5.3 states that `IRS_RBS(F)` is weak-* closed (quoted). It presents `IRS_RBS(F)` as the
  intersection over finite `B` of computable compact convex polytopes `PRBS(B)` of pseudo-IRS. The
  intersection formula is cut off in the fetched text. Granting it, the restriction of `pi` to some finite `B`
  lies outside `PRBS(B)`. That is a finite, checkable certificate of the entropy deficit.
- *Convex splitting.* Write `pi = t pi_1 + (1 - t) pi_2` with `pi_1` RBS and `0 < t < 1`.
  - `eps_D` and `delta_D` are affine, so `eps_D(pi_1) = eps_D(pi_2) = 0`.
  - Theorem R forces `delta_D(pi_1) = 0`, so `delta_D(pi_2) > 0`.
  - So the witness lives entirely on the non-RBS components.
- *Bowen–Chapman's witness is not a counterexample.* The proof of BC Theorem 1.2 optimises over RBS IRS: it
  defines `val_RBS(T)` as a supremum over IRS satisfying RBS. It produces a non-cosofic IRS satisfying RBS. The
  last point comes from a WebFetch summary, not from a quote. By Theorem R that IRS carries no strict design.
  So the known non-cosofic surjunctive IRS are consistent with the hole, and the hole is true on a nonempty
  part of its own domain.

## 3. Obstruction: the RBS route is dominated by Rokhlin maximality for groups

Consider the natural decomposition

    free-group-irs-carry-no-strict-design  <=  Theorem R  +  (every IRS of F_r satisfies RBS).

By Corollary 5.4 the open half is "every non-cosofic IRS satisfies RBS". It dies as an independent
decomposition at the atomic normal IRS.

**Proposition D.** Let `N` be a normal subgroup of `F_r` of infinite index, and `Gamma = F_r / N`. If
`1_N` satisfies RBS, then the uniform Bernoulli shift of `Gamma` has Rokhlin entropy `log|Sigma|` for every
finite `Sigma`.

*Proof.* Under `u_{1_N}` the map `P` is a.s. the constant `N`, so `P^-1` of the Borel sets is the trivial
sigma-algebra mod null sets. So the relative Rokhlin entropy is the plain Rokhlin entropy. The space is
`Sigma^(N\F) = Sigma^Gamma` with `F` acting through `Gamma`, as the Bernoulli shift. For every partition
`alpha`:
- the `F`-invariant and `Gamma`-invariant sigma-algebras coincide;
- `sigma-alg_F(alpha) = sigma-alg_Gamma(alpha)`.

So the infima defining the two Rokhlin entropies are over the same set of partitions of the same quantity. `∎`

So "every IRS satisfies RBS" implies Rokhlin maximality for every infinite finitely generated group (every such
group is some `F_r / N`). By Higman–Neumann–Neumann every countable group embeds in a finitely generated one,
and `bernoulli-rokhlin-maximality-passes-to-subgroups` then extends it to every countable group. That is
`bernoulli-rokhlin-entropy-maximal-for-every-group`, which already gives the goal through
`gottschalk-via-maximal-bernoulli-rokhlin-entropy`.

The route therefore needs a statement at least as strong as an open prerequisite that closes the goal without
the IRS detour. Every entropy-measure proof of the IRS hole through the BC criterion passes through Rokhlin
maximality for all groups.
- The invariant is the relative Rokhlin entropy `H_Rok(F ↷ (sub(F, Sigma), u_pi) | P)`.
- The step where each such proof dies is its specialisation at `pi = 1_N`, Proposition D.
- This does not show the IRS hole is harder than Gottschalk: the converse, from Rokhlin maximality for groups to
  RBS for all IRS, is open.

## 4. What this does not do

It does not close `non-co-sofic-free-group-irs-carry-no-strict-design`. It establishes a strictly larger class
of IRS with no strict design (RBS, which contains the cosofic IRS and some non-cosofic ones). It gives a finitary
necessary condition on counterexamples, and it shows the entropy route through this class is dominated.
