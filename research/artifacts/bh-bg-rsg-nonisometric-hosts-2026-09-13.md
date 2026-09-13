# Baumslag--Gersten and Higman groups in rational similarity groups with non-isometric local actions

Lane `solve-bh-rational-similarity`, 2026-09-13.

## Notation

- **Groups.**
  - `BG = < a, t | b a b^-1 = a^2 >`, where `b = t a t^-1`.
  - `H4 = < g_i | g_i g_(i+1) g_i^-1 = g_(i+1)^2 >`.
- **RSGs.** Rational similarity groups, local actions `g|_α`, the nucleus and
  "contracting" are as in Belk--Bleak--Matucci--Zaremsky, arXiv:2309.06224v3. The
  definitions are quoted in `research/artifacts/bh-rational-similarity-hosts-2026-09-12.md` §3.
- **Source.** The TeX was re-read on MSI on 2026-09-13:
  `hyperbolic_boone_higman.tex`, lines 687--835 and 1785--1810.

## 0. Results

| # | Statement | Status |
|---|---|---|
| R1 | `rsg-proper-power-conjugate-germs-torsion-at-finite-orbits`. In an RSG with finite nucleus, suppose `f g^k f^-1 = g^l` with `|k| ≠ |l|`. At every rational `g`-periodic point with finite `f`-orbit, a power of `g` is the identity nearby. | ESTABLISHED (not independently reviewed) |
| R2 | `dyadic-affine-bs12-model-lies-in-no-finite-nucleus-rsg`. The dyadic coding of `x ↦ x+1`, `x ↦ 2x` on `R ∪ {±∞}` is rational, with `a ∈ F` and `a` not equicontinuous. No RSG with finite nucleus contains it. | ESTABLISHED (not independently reviewed) |
| O | `finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous`. If true, it excludes every finite-nucleus RSG host for `BG`, including the hyperbolic-group hosts of BBMZ. | OPEN |

## 1. Where the pumping proof fails

The proof is `graph-almost-automorphism-exponent-pumping-proof`. Its steps use
isometric local actions in four places, and each fails for RSGs.

- **Item 0: images of cones are cones.**
  - Nuclear maps need not be surjective. In the second binary example of BBMZ
    (TeX line 820 onward), `f(0ω) = 0 f(ω)`, `f(10ω) = 011ω` and `f(11ω) = 10ω`,
    so `im(f) = C_0 ∪ C_10`.
  - Line 844 says "the elements of $\Nuc$ might not even be invertible."
  - So `g(C_α)` is a clopen set inside `C_(ḡ(α))`, not a cone.
- **Item 1: a locally constant exponent cocycle.**
  - For RSGs, `ḡ(α s) = ḡ(α)·(g|_α)‾(s)`, and `|(g|_α)‾(s)| - |s|` depends on `s`.
  - So the length change is not refinement invariant, and it can be unbounded
    along a cycle of the nucleus automaton.
  - In R2, `b` has local action `P` at every `1^j`, with `P(1v) = 11 P(v)`.
    There is no cone around `1^∞` on which `b` is a similarity.
- **Item 2(i): conjugation invariance of the periodic spectrum.**
  - **Exponent at a rational fixed point.** Let `z = σ τ^∞` and let `c` be the
    canonical shift `σ w ↦ σ τ w`. If `[x]_z^N = [c]_z^j`, put
    `e_z(x) = j|τ|/N`. This is well defined because `[c]_z` has infinite order.
  - **The rescaling involution `q`.** Define `q(0v) = 11 q(v)`, `q(10v) = 10v`
    and `q(11v) = 0 q(v)`.
    - `q` is a rational homeomorphism with `q^2 = 1`, and `q(0^∞) = 1^∞`.
    - It sends depth `2m` along `1^∞` to depth `m` along `0^∞`.
  - **Its effect on `a`.** Take `a ∈ F` from R2.
    - `a` is the canonical shift near `1^∞`, so `e_(1^∞)(a) = 1`.
    - On `C_0`, `(q a q)^2 = q a^2 q` is `x ↦ 0x`: for `m ≥ 1`,
      `q(0^m ω) = 1^(2m) q(ω)`, then `a^2` gives `1^(2m+2) q(ω)`, and `q` returns
      `0^(m+1) ω`.
    - `q a q` itself is not a similarity near `0^∞`. It sends `0^m 10ω` to
      `0^(m+1) 11 q(ω)` and `0^m 11ω` to `0^m 10 q(ω)`.
    - So `e_(0^∞)(q a q) = 1/2`.
  - **Consequence.** In any rational group containing `F` and `q`, the exponent
    normalized by canonical shifts is not a conjugacy invariant.
  - **Not checked.** Whether some finite-nucleus RSG contains `q`.
    - `Nuc_q = {1, q, s}`, with `s(0v) = 10v` and `s(1v) = 0 q(v)`.
    - ProdNuc then forces `s∘q` into the nucleus. That is
      `v ↦ …` with `(s∘q)(0v) = 0 (s∘q)(v)`, `(s∘q)(10v) = 011 q(v)` and
      `(s∘q)(11v) = 10 q(v)`.
    - The closure was not computed.
- **Item 4: the fixed point from a contraction.** `w ↦ c h(w)` is a `2^-|c|`
  contraction only because `h` is an isometry. Nuclear maps such as `P` expand
  distances near their singular points.

## 2. What transfers

BBMZ `prop:CyclicStabilizers`: at a rational point, the group of germs of an RSG
with finite nucleus is virtually infinite cyclic.
- **An algebraic fact.** In a virtually infinite cyclic group, if `x` has infinite
  order and `y x^A y^-1 = x^B`, then `|A| = |B|`.
- **R1.** Combining the two gives R1.
- **R2.** R1 applies to the affine dyadic model at `1^∞`. There `b` squares the
  shift germ of `a`, so the model has no finite-nucleus host.
- **A related remark.** BBMZ also remark (after `prop:CyclicStabilizers`) that
  germ groups at irrational points are finite. They give no proof, and it is not
  used here.

## 3. Toward O (sketches; not landed, may contain errors)

- **Rates.**
  - Let `h ∈ G` and let `z = σ τ^∞` be rational. The local actions of `h` along
    `σ τ^i` are eventually nuclear and eventually periodic in `i`.
  - This gives a rate `r_h(z)`, the output length per input length along the
    tail. It lies in a finite set that depends only on `τ` and `Nuc`.
  - At a fixed point, a rate other than `1` would conjugate the canonical shift
    germ to a power of absolute value other than `1`, which §2 forbids. So rates
    define a coboundary on each orbit of rational points.
  - The eventual periodic states also show that a `G`-orbit of rational points
    has finitely many tail classes.
- **Normalized exponent.**
  - Put `ê_z(x) = e_z(x)/φ(tail of z)`, where `φ` is the potential of the rate
    coboundary. `ê` is conjugation invariant and homogeneous.
  - If `f g^k f^-1 = g^l` and `z` is `g`-periodic with infinite-order germ, then
    the per-iterate `ê` at `f^-n z` grows like `|l/k|^n`.
  - So O at rational points follows from one input: `ê` is bounded over the
    periodic points of a fixed element.
- **Obstacle 1: normalized shifts are unbounded.**
  - A single step can have unbounded normalized shift. For `q` at the point
    `0^m 1 1^∞`, with `φ(0) = 1` and `φ(1) = 2`, it is `3m/2`.
  - A weighted letter metric fixes this example. With `w(0) = 1` and
    `w(1) = 1/2`, `q` and `s` change weighted depth by at most `1/2`.
  - Conjecture, untested: every finite nucleus of injections admits edge weights
    with bounded weighted lag.
- **Obstacle 2: pumping.**
  - A non-equicontinuous `g` may separate points along thin clopen sets rather
    than cones.
  - A composite of `m` nuclear maps has nuclear local actions only below depth
    about `log m`.
  - So the record-time pigeonhole of Item 4 does not directly give a rational
    periodic point with infinite-order germ.
  - A proof of O needs a pumping lemma for finite nuclei of injections.

## 4. Constructions tried

- **Dyadic affine model of `BS(1,2)`.** Rational, non-equicontinuous `a`. Dead
  for finite nuclei (R2).
- **Affine ternary model in `V_3(G)`.** `a` is equicontinuous, so it is dead for
  `BG` by `baumslag-gersten-embeds-in-no-rover-nekrashevych-group`.
- **Required shape of a finite-nucleus host for `BG`.**
  - The image of `a` is not equicontinuous.
  - Every rational periodic point of `a` with infinite-order germ has an infinite
    `b`-orbit (R1).
  - Conjugation by `b` must rescale the normalized exponent along that orbit, or
    the points must be irrational.
  - No candidate was found.

## 5. Exact gap

- Either prove O for finite-nucleus RSGs, which needs the two inputs of §3, or
  build a finite-nucleus RSG containing `BS(1,2)` whose `a` has infinitely many
  hyperbolic rational periodic points permuted by `b` with rescaling.
- Brin--Thompson `nV`, twisted Brin--Thompson `SV_G`, non-expansive groupoids and
  infinite-nucleus RSGs are not addressed here.
