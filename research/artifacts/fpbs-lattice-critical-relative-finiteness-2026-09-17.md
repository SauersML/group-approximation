# Calibration world W1: critical relative finiteness on Z^d along a sublattice

Worker `b-t-wqsub`, wave `swarm-0917`, 2026-09-17. The target hole is
`fpbs-amenable-wq-normal-relative-subcriticality`, toward
`fpbs-benjamini-schramm-universal`.

## 1. Question calibrated

Section 4.4 of `research/artifacts/fpbs/docs/relative-susceptibility-reduction.md`
proposes a two-step plan:

* (A) critical relative finiteness `chi^H_(p_c) < infinity`, predicted by mean
  field in Section 4.2;
* (B) openness of `{p : chi^H_p < infinity}`.

The question is which inputs can prove (B). World W1 has (A), and more: a
power-law fibre profile that is square summable. Yet (B) fails. So (B) must use
something W1 lacks.

## 2. The world

* **Graph and subgroup.** `G = Cay(Z^d, ±e_i)` with `d >= 11`, and
  `H = Z^k x {0}`. `H` is normal and amenable, with quotient `Q = Z^m`,
  `m = d - k`.
* **Imported input.** Fitzner--van der Hofstad (arXiv:1506.07977) Theorem 1.4:
  `tau_(p_c)(x) = a_d A(d) |x|^(-(d-2)) (1+O(|x|^(-2/d)))`. It is quoted verbatim
  in the route file.
* **The same paper's Theorem 1.1** gives the uniform infrared bound
  `tau^_p(k) <= A_2(d)/(1 - D^(k))` for `p <= p_c`, which is (1.12) there. It
  gives items 1–2 of the claim by Fourier integration over the `H`-directions, for
  `m >= 3` and `m >= 5` respectively. The route uses the x-space bound instead,
  because it is shorter.

| quantity at `p_c` | W1 value | reason |
|---|---|---|
| `chi^H_(p_c) = sigma_(p_c)(0)` | finite iff `m >= 3` | the sum over nonzero `h` in `Z^k` of `norm(h)^(-(d-2))` |
| `sigma_(p_c)(q)` | `<= C (1+norm(q))^(-(m-2))` | sum over the fibre |
| `l^r` norm of `sigma_(p_c)` | finite for `r > m/(m-2)` (so `r = 2` when `m >= 5`) | power law on `Z^m` |
| `l^1` norm of `sigma_(p_c)`, which is `chi_(p_c)` | infinite | standard |
| operator norm of `lambda_Q(sigma_(p_c))` | equals the `l^1` norm, so infinite | `Q` amenable, kernel nonnegative (Følner) |
| `chi^H_p`, `p > p_c` | infinite | Burton--Keane plus Harris: `tau_p >= theta^2` |

## 3. What dies

* **Mean-field prediction as evidence (Section 4.2).** That section derives
  `chi^H_(p_c) < infinity` from `sum_l q_l(e,e) <= 1/(1-rho(Q))`. In W1,
  `rho(Q) = 1` and the conclusion still holds, because `Z^m` is transient for
  `m >= 3`. So the prediction measures transience of the quotient, not
  nonamenability. Verifying it for a nonamenable `Gamma` is no evidence for (B).
* **Openness from rearrangement-invariant critical data.** Suppose a method
  concludes (B) from finiteness of `chi^H_(p_c)`, from an `l^r` bound on the
  critical fibre profile, or from mean-field two-point exponents, and uses
  nonamenability of `Q` nowhere else. Then it proves (B) in W1, which is false.
  **The step where every such method dies** is the passage from `p_c` to some
  `p > p_c`. W1 shows that this passage needs a non-rearrangement-invariant
  input. The natural one is the operator norm `||lambda_Q(sigma_(p_c))||` on
  `l^2(Q)`, which is critical L2 for the fibre operator.
* **What survives.** Methods that use `rho(Q) < 1` quantitatively, for example
  through Kesten's theorem applied to `sigma_p`, are untouched. The Kesten barrier
  of `ps-averaged-tilt-relative-susceptibility.md` says any multiplicative
  closure of the sprinkling recursion dominates `||lambda_Q(sigma_p)||`. W1
  confirms from the other side that nothing weaker separates.

## 4. Sprinkling reach (heuristic, constants unverified)

The sprinkling majorant quoted in Section 4.4 is
`T_(p') <= sum_k [((p'-p)/(1-p)) T_p A]^k T_p`. Summed along `H`, its `k`-th term is
`sigma * (delta a * sigma)^(*k)(e)`, with `a = pi_* 1_S` and
`delta = (p'-p)/(1-p)`. By Harris, `a * sigma <= (|S|/p) sigma`. So the majorant
certifies `chi^H_(p') < infinity` roughly when
`delta (|S|/p) ||lambda_Q(sigma_p)|| < 1`. Reaching past `p_c` from `p < p_c`
therefore asks for

```text
||lambda_Q(sigma_p)|| <~ p (1-p) / (|S| (p_c - p))    as p ↑ p_c,
```

a spectral spreading rate. The constants in Lemma 2.4 of arXiv:1804.10191 were
not re-read here, because no PDF extractor was available. This section is a
sketch and supports no claim.

## 5. Status

* `fpbs-lattice-amenable-subgroup-critical-finiteness-no-gap`: ESTABLISHED via
  its `-proof` route, which requires `fpbs-hp-relative-burton-keane` and the
  verbatim Fitzner--van der Hofstad Theorem 1.4.
* Target `fpbs-amenable-wq-normal-relative-subcriticality`: remains OPEN.
