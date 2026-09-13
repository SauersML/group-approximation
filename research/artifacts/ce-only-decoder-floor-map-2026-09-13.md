# CE-only decoders: where the random-guessing floor comes from (2026-09-13)

Lane `solve-nh-ce-decoder`. Target: `non-hyperlinear-group` through break
(iii) of `research/artifacts/exact-lcs-compilation-map-2026-09-13.md`. That
break asks for a perfectly complete compiler into LCS or group corners whose
decoding is only required on Connes-embeddable (CE) target models, and which
beats the long-code random-guessing floor.

**Verdict: partial.** One firewall is landed:
`ce-exact-affine-compilers-force-nonhyperlinear-corners` (CS3; ESTABLISHED,
not reviewed, no novelty claimed). The floor is not intrinsic to perfect
completeness plus robust soundness. It is intrinsic to the *randomized
non-affine readout* of the long-code decoder. `non-hyperlinear-group` stays
OPEN.

## 1. Step 1: is the floor intrinsic? The proposed no-go and its failing step

**The proposed no-go.** "Every perfectly complete compiler that is sound on
R^U target models already has a decoder that is sound on all traces with
affine readout, hence falls under (CS2)."

**What is true (CS3).** Suppose the target group `Gamma` is hyperlinear. Then
the canonical corner trace `tau_omega` is Connes-embeddable:
- by Step 1 of the route, `(p_omega L(Gamma) p_omega, tau_omega)` is the
  twisted group von Neumann algebra `L_(omega o alpha)[Gamma/<J>]`;
- by Thom's Lemma 3.3 (`thom-central-corner-criterion`), that algebra embeds
  into `R^omega` when `Gamma` is hyperlinear.

(CS2) only ever evaluates the decoder on `tau_omega`. So on hyperlinear
targets, CE-exact affine decoding already gives (CS2)'s conclusion, with the
extra information that the affine-safe source model is itself CE.

**The failing step.** On a nonhyperlinear target, `tau_omega` need not be CE,
and CE-only decoding says nothing about it. So the upgrade "CE-sound implies
sound on all traces" is exactly as hard as proving the compiled groups
hyperlinear. It cannot be proved as a lemma about compilers.

**Consequences.**
- If the source has no affine-safe perfect CE model, a CE-exact affine
  compiler with `J` of order `n` forces `Gamma` nonhyperlinear.
- The active JNVWY outputs have no affine-safe perfect model of any kind
  (`jnvwy-active-output-has-no-affine-safe-perfect-model`). At halting inputs
  they are perfectly CE-satisfiable, as limits of finite-dimensional
  strategies with value tending to one.
- So for an RE-orientation compiler with (PC1) and an asymptotically exact
  affine ultraproduct decoder, the output at **one** explicit halting input
  is already a nonhyperlinear group.
- The proof-search fixed point and the nonhalting-side soundness add nothing
  to the difficulty of this decoder class.

## 2. Step 2: escape candidates, with sources

### 2a. Taller--Vidick long code (the floor's origin)

arXiv:2507.22444, TeX `main.tex` fetched on MSI.
- **l.134:** "Achieving the same result with $\epsilon=0$ would imply the
  existence of a non-hyperlinear group."
- **l.181:** imperfect completeness "is a direct consequence of introducing
  noise into the linearity test, which is a necessary component of the
  construction."
- **l.189--193:** "it is not possible, in general, to associate with every
  BCS $B$ an LCS $B'$ such that $\calA(B)$ admits a $*$-morphism into
  $\calA(B')$ ... any attempt to generically reduce such protocols to LCS
  protocols, in a way that induces a $*$-embedding of the associated algebras,
  is ruled out". This is the trace-level barrier; (CS2) is its
  group-corner form.
- **l.784--786 (decoder):** "Given that the result of the measurement was
  $\beta$, she will choose $\psi\in\beta$ uniformly at random and will respond
  with $\psi$."

**Verdict.**
- The readout `beta -> uniform element of beta` is not a mixture of affine
  maps. On odd `beta` an affine map extending the dictators returns the odd
  sum of the elements of `beta`, which is generally outside `beta`.
- So (CS2)/(CS3) do not apply, and the cost is the floor `1/|beta|` of
  `perfect-correlated-masks-have-undamped-conditioned-spectrum`: perfect
  completeness leaves `hat D(beta) = 1` for `beta` inside the honest support.
- **Completeness on the canonical perfect trace:** exactly 1 only after the
  mask is trivial on the honest support, and then damping vanishes.
- **CE-only soundness:** yes, finite-dimensional.
- **Floor:** `delta^2 / m^u` against the source's classical floor `m^(-u)`.

### 2b. BLR linearity / Hadamard test

Natarajan--Vidick, arXiv:1610.03574, TeX `fullpaper.tex` fetched on MSI.
- **Figure `fig:linearity` (l.1118--1137):** consistency test plus
  "Linearity test: if $c = a + b$, accept if and only if
  $\gamma = \alpha \beta$".
- **Theorem `thm:qblr_game` (l.1141--1156):** success at least
  $1-\eps$ gives observables with
  $\E_{a,b} \Tr_{\rho'}(A(a) A(b) A(a+b)) = 1-O(\sqrt{\eps})$.

Rounding to an exact representation of `F_2^n` is Gowers--Hatami
(arXiv:1510.04085; see `gowers-hatami-normalized-hs-source-audit-2026-08-21.md`:
flexible stability with error `O(epsilon)` uniformly in the finite group, and
enlarged dimension `d <= m <= d/(1-4 epsilon^2)`).

**Verdict.**
- **Completeness:** exactly 1 on every representation of `F_2^n`, including
  the canonical trace, since every character is linear.
- **Soundness:** holds on every model, not only CE ones. The solution group
  is finite, so exact models are representations.
- **Readout:** the character itself. It is affine and has no floor: the loss
  is `O(sqrt eps)` with no `1/m`.
- **What it certifies:** only affine structure. It is an all-trace exact
  affine decoder, so (CS2) confines it to affine-safe supports.

### 2c. Pauli braiding with Magic Square

Natarajan--Vidick, same source.
- **l.374:** "By using the Magic Square game instead, it is possible to
  devise a test with perfect completeness, $\omega^*=1$, which can be achieved
  using an honest strategy based on the use of $(n+1)$ EPR pairs."
- **Theorem `thm:braiding` (l.462--474, informal):** success
  $\omega^*_{\rm opt}-\eps$ gives
  $A(x) \approx_{\delta} \otimes_i \sigma_X^{x_i}$,
  $A(z) \approx_{\delta} \otimes_i \sigma_Z^{z_i}$, with
  $\delta=\poly(\eps)$.
- A TeX comment at l.606 says the CHSH version "does not have perfect
  completeness". l.374 is the perfect-completeness variant.

**Verdict.**
- The target is a Weyl--Heisenberg-type finite group with `J = -1`, so it has
  a unique irreducible representation with `J = -1` (standard, not re-read).
- **Completeness:** the canonical corner trace is the maximally mixed state,
  whose X- and Z-context supports are full cosets, as (CS1) predicts.
  Completeness is exactly 1.
- **Robustness:** loss `poly(eps)`, no floor.
- **Readout:** affine. Bilinear phases appear only between non-commuting
  contexts, never as a context support.

### 2d. Low individual degree / Reed--Muller over `F_(2^k)`

Ji--Natarajan--Vidick--Wright--Yuen, arXiv:2001.04383v3, TeX
`compression_arXiv_v3.tex` fetched on MSI.
- **l.2060:** "we only consider finite fields $\F_q$ such that $q = 2^k$".
- **l.13131:** the trace of `a in F_q` is `sum_i a_i` in the self-dual normal
  basis. So F_q-linear consistency checks are F_2-parity checks.
- **Theorem `lem:ld-soundness` (l.4561--4585):** success at least $1-\eps$
  gives polynomial measurements `G^w` with
  $\delta_{\ld} = a (dm \ldc)^a (\eps^b + q^{-b} + 2^{-bmd})$.
- **l.4559:** the soundness analysis of the original quantum low-degree test
  has a gap, so they use the low individual degree test (quantum soundness
  from ML20, generalized in ji2021quantum).

**Verdict.**
- The answers, restrictions of polynomials, form F_2-linear spaces, and the
  consistency is F_2-linear. So the test is of LCS type with affine readout
  through the global polynomial measurement.
- **Completeness:** honest polynomial strategies pass with probability one.
  This is the decider's design; the completeness statement was not re-pinned
  here.
- **Soundness floor:** the decoding error at `eps = 0` is
  `a (dmk)^a (q^(-b) + 2^(-bmd))`. That is not zero at fixed field size, so
  this is a constant-gap affine decoder at fixed parameters, not the `1/m`
  floor.
- **What it certifies:** affine-safe blocks only, as in 2b.

## 3. Exact remaining gap for break (iii)

1. **(iii-a) Asymptotically exact affine readout.** By (CS3), soundness at one
   halting affine-unsafe input already makes that output group nonhyperlinear.
   So this is the root problem at a single explicit instance.
2. **(iii-b) Randomized non-affine readout.** This is the Taller--Vidick
   regime. A decoder whose loss on undamped Fourier sets `beta` below the
   honest support beats `1/|beta|` against the source's classical floor is
   needed.
   - Main has no such decoder, and the published one is sharp at `1/|beta|`
     (PCM13).
   - One untested idea: consistent-hashing selection. For each edge the
     W-player can compute `pi_2(beta)` itself and hash-select an element. It
     is exact on a single edge, but it fails on odd parity families where one
     `phi` must serve every neighbour (clause example `C_W` of size 7 with
     positive literals).
3. **(iii-c) Constant-gap affine readout.** Here near-perfect models give
   source value at least `s < 1`. (CE) on the canonical trace of a hyperlinear
   target gives a CE strategy of value at least `s` with context supports
   uniform on affine sets. A no-go needs a quantitative firewall: an upper
   bound below `s` on the value of such strategies for active JNVWY outputs.
   Main records only the qualitative firewall (no affine-safe **perfect**
   model).

## 4. What was not done

- No positive compiler step was found.
- No quantitative affine-support value bound for JNVWY outputs was attempted.
- The Weyl--Heisenberg uniqueness, the Kim--Paulsen--Schafhauser limit
  statement and the low-degree completeness were used at statement level and
  not re-read.
- No literature search for novelty beyond the four sources above and the
  repo.
