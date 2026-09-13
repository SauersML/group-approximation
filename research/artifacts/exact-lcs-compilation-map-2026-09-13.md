# Exact reduction to linear-system games: where exactness breaks (2026-09-13)

Lane `solve-nh-exact-lcs`. Target: `non-hyperlinear-group` through a gapless,
exact reduction into linear-system games. Verdict: **partial.**
- No exact compilation step past the known boundary was found.
- One new consolidating firewall is landed:
  `group-corner-exact-compilers-force-source-affine-safety`.
- The exact break point is pinned below, with sources.

## 1. What has to be reduced (pinned against sources)

**Paddock--Slofstra, arXiv:2310.07901 (TeX `main.tex`, fetched on MSI).**
- l.1252 (Proposition): "There is a constraint system $B$ with contexts over
  LIN such that $B$ is tracially-satisfiable but not
  $\mcR^{\mcU}$-satisfiable if and only if there is a non-hyperlinear
  finitely presented group."
- l.1294 (`cor:nofun`): "If $B$ is a BCS with contexts over LIN, then $B$ is
  tracially satisfiable if and only if $B$ is algebraically satisfiable."
- l.1333: a construction of an LCS $B'$ with a homomorphism from the BCS
  algebra "would have to use some particular feature of $B$, such as the
  fact that it is tracially satisfiable."
- l.1345--1351 (Theorem `thm:dichotomy2`, part (b)):
  "$\SAT_{\mcR^{\mcU}}(\mcL)$ is coRE-hard, and contained in $\Pi_2^0$."
- l.1410--1412: "Proving that $\SAT_{\mcR^{\mcU}}(\LIN)$ is
  $\Pi^0_2$-complete (or even just that it contains RE) would imply the
  existence of a non-hyperlinear group."

**Mousavi--Nezhadi--Yuen, arXiv:2110.04651 (TeX `arxivsubmittable.tex`).**
- l.380--382 (Theorem `thm:main-intro`): "The problem of deciding whether
  $\val_q(G) = 1$ for nonlocal games $G$ is complete for $\Pi_2$."
- l.594: "for this argument it did not matter that reduction from
  $\Sigma_1$-sentences $S_n$ to games $H_n$ is gapped".
- l.791--794 (Theorem `thm:synchronous`, adapted from Helton et al. and
  Kim--Paulsen--Schafhauser): perfect co-value gives a perfect synchronous
  strategy, and perfect q-value gives finite-dimensional synchronous
  strategies with values approaching 1.
- l.796: "the games constructed in the proof of $\MIP^* = \RE$ are all
  synchronous."

**Consequences for the target.**
- For the endpoint, Sigma_1-hardness is enough. The gapless Pi_2 machinery
  of MNY adds nothing to the linear-system target.
- In repo form the family version is `re-oriented-lcs-compiler-gives-nonhyperlinear-group`
  (ESTABLISHED): halting gives `J != 1`, nonhalting gives strict matrix
  soundness.
- The one-instance version is `perfect-lcs-gap-implies-nonhyperlinear`.
- If `J != 1` holds uniformly, the recursion-theorem layer is not needed.
- Under "every group is hyperlinear", `SAT_{R^U}(LIN)` equals the Pi_1 set
  `J != 1` (`cor:nofun` plus Proposition 5.8 of Paddock--Slofstra), so
  RE-hardness is a contradiction.

## 2. The compilation chain and where exactness breaks

**Stage 1: halting to synchronous BCS games. Exact.**
- JNVWY / MNY give synchronous Boolean constraint games with perfect
  completeness on halting instances.
- Their sources' perfect models are affine-unsafe:
  `jnvwy-perfect-introspection-forces-full-seed-support` and
  `jnvwy-active-output-has-no-affine-safe-perfect-model` are recorded as
  established firewalls on main.

**Stage 2: BCS to a group corner. This is where exactness breaks.** Three
kinds of decoder are available, and each is closed or open as follows.
- **(a) Affine decoders, exact on every trace.** They force affine-safe
  source supports for **every** central-character group-corner syntax. This
  covers binary linear systems, `Z_d` systems, nonabelian ancilla relations
  and infinite ambient groups, and is landed this lane as
  `group-corner-exact-compilers-force-source-affine-safety`.
  - Proof: the canonical trace of the corner is uniform on answer cosets in
    every finite abelian context (CS1), and an affine map sends cosets to
    affine sets (CS2).
  - Binary LCS case: `locally-affine-support-bcs-is-exactly-the-lcs-boundary`.
  - R_* gadget case: `fano-cap-witness-sections-force-source-affine-safety`.
  - Source with every perfect trace affine-unsafe:
    `matrix-conj-forces-unsafe-support`.
- **(b) Non-affine exact decoders.** The source involutions are then
  realized by non-group elements of the corner algebra, i.e. the OPEN hole
  `non-ru-bcs-is-satisfiable-in-a-group-factor` with its recorded fences.
- **(c) Decoders exact or approximate only on Connes-embeddable models.**
  This is the Taller--Vidick noisy long-code route. Perfect completeness
  forces the mask to be 1 on the honest support, and the tailored-noise
  repair runs into the random-guessing floor
  (`notes/FALSE_PERFECT_COMPLETENESS_MASK_NO_GO.md` §§2--4).

**Stage 3: group corner to binary LCS. Exact.**
- Slofstra's embedding (Paddock--Slofstra l.1277--1283, citing [Slof19,
  Theorem 3.1]) turns a marked finitely presented group into a linear
  system, preserving both nontriviality of `J` and triviality in approximate
  representations.
- Changing the target syntax therefore never helps. This is also the reason
  the consolidating claim covers every corner syntax at once.

## 3. Gadgets tested in this lane

- **Carry read-out over `Z_4`.** Dead: coset relations are closed under the
  Maltsev term `a-b+c` (idea file `nh-undecidable-J`, approach 1).
  (CS2) subsumes the trace-level form.
- **Nonabelian ancilla relations.** Dead in exact trace-level form. By (CS1)
  the canonical trace is uniform on cosets in every abelian context,
  whatever the ambient group. `central-pinning-forbids-nonlinear-predicates`
  gives the finite-group reason.
- **Infinite ambient groups, context subgroups infinite but answers finite.**
  Same conclusion. Only finite abelian context subgroups enter (CS1).
- **Tensor-power affinization.** Dead, by a hand argument.
  - Products `X_v^(1)...X_v^(k)` over `k` independent copies of a perfect
    trace have context support equal to the `k`-fold sumset of `S_c`.
  - For odd `k >= |S_c|` that sumset is `Aff(S_c)`, so it is affine.
  - But a sound allowed set must contain the `k`-fold sums of all accepted
    points, which for large odd `k` is `Aff(C_c)`. That is the classical
    affine relaxation of the source relation, and it is unsound in general.
  - Small `k` does not keep `Aff(S_c)` inside the `k`-fold sumset of `C_c`.
- **Tailored mask noise with bounded honest support size `m`.** It gives a
  perfectly complete test, but the Fourier decoder recovers only about
  `1/m` agreement (PCM11, PCM13). Against MIP* soundness `omega_q <= 1/2`,
  that is useless for `m >= 2` (the note's §4).

## 4. Exact remaining gap

A non-hyperlinear group by this route needs one of three things.
- **(i)** A source BCS with a non-CE perfect tracial state whose context
  supports are affine-safe. This is equivalent to the root by
  `locally-affine-support-bcs-is-exactly-the-lcs-boundary`, and the natural
  MIP* sources are recorded affine-unsafe.
- **(ii)** A non-affine exact decoder into a group corner, which is the
  group-factor hole.
- **(iii)** A perfectly complete compiler whose soundness decoding works only
  on Connes-embeddable target models and beats the random-guessing floor of
  the long-code decoder.

No computable exact reduction preserving perfect `R^U`-satisfiability in
both directions was found. Every exact construction examined in this lane
stops at (i) or (ii).
