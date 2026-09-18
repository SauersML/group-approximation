# Referee report (gq-referee-a, proof-gap lens): the finitely presented ring R_Q

**Reviewed:** `finitely-presented-harmonic-cuntz-ring-contains-q` and its route
`finitely-presented-harmonic-cuntz-ring-proof` (lane gq-cuntz-cstar, f07d0119c), read on origin/main.

**Verdict: PASS.** No gaps found.

- **Compressions.** `φ(a) = t_1 a s_1` and `ψ(a) = t_0 a s_0` are unital ring maps on the centralizer
  `C` of `p = s_0 t_0`. The cross terms vanish because `t_1 p = 0` and `t_0(1−p) = 0`.
- **`h, g ∈ C`.** From (D). The relation (I) makes `g` and `h` commute, and inverses of elements of
  `C` stay in `C`.
- **Induction.** `φ(1+kh) = 1 + k·hg` by (E1), and `φ(u)` is its two-sided inverse. Then
  `(1 + khg)(1 + h) = 1 + (k+1)h`, using `hg(1+h) = h`. So every `1 + kh` is a unit whose inverse
  lies in `C`.
- **Part 1.** `ψ(1 + kh) = 1 + k` by (E0), so every integer `k+1 ≥ 2` is invertible. `R_Q ≠ 0`
  because it maps onto `C_h`.
- **Part 3.** Each relation checks pointwise in `C_h`: `ζ(1+η) = 1`, `η(0z) = 1`, and
  `η(1z) = η(z)ζ(z)`, including at `1^∞`.
- **Part 4.** The involution descends: the image of (E1) is `t_1 h s_1 = gh`, and `gh = hg` by (I).
- **Consequences.** `R_Q` is a finitely presented ring with `Q` central and a Leavitt pair. So both
  reviewed Steinberg lemmas apply to it: fbbb1c736 and 0b381f2c1, the latter conditional on the
  C1–C4 citations. `St_4(R_Q)` and `St_{6n+7}(R_Q)` are further finitely presented overgroups of
  `GL_n(Q)`.
- **What the obstruction gives here.** By 58d536cf7, `E_N(R_Q)` modulo its centre is not finitely
  presented.
