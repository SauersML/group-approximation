---
rg: 2
id: compressors-conjugate-leak-free-root-pairs
kind: claim
title: Two explicit Leavitt compressors simultaneously conjugate every leak-free root pair of EL_3 to a compressed root pair
distinct_from:
  shifted-root-pair-conjugates-to-idempotent-root-pair: that conjugates the single shifted pair (x_12(t_0), x_23(s_0)) to the idempotent pair; this gives two families of simultaneous conjugacies, parametrized by all coefficients in R t_1 t_1 on the 23 root or in s_1 s_1 R on the 12 root.
artifacts:
  - research/artifacts/el3-compressor-root-pair-calculus-2026-09-12.md
---

Let `R = L_(F_2)(1,2)` and `EL_3(R) = GL_3(R)`. There are units `c`, `c'` in `GL_3(R)`
(artifact Section 1, explicit formulas; `T[10] = t_0 t_1` is the adjoint of `s_1 s_0`) such that for
all `a, a'', b, b'` in `R`:

```text
c  (x_12(a), x_23(b' t_1 t_1)) c^-1     = (x_12(s_0 a t_0),  x_23(s_0 b')) ,
c' (x_12(s_1 s_1 a''), x_23(b)) c'^-1   = (x_12(a'' t_0),    x_23(s_0 b t_0)) .
```

Conjugation by `c` sends `x_23(b)` to a root element exactly when `b` lies in `R t_1 t_1`;
otherwise it leaks into `x_21` and a diagonal unipotent. Conjugation by `c'` sends `x_12(a)` to a
root element exactly when `a` lies in `s_1 s_1 R`; otherwise it leaks into `x_32` and a diagonal
unipotent.

Consequently, in every characteristic-two rank model, with `delta(a,b) = rk(n_23(b) n_12(a))`,

```text
delta(a, b' t_1 t_1) = delta(s_0 a t_0, s_0 b') ,     delta(s_1 s_1 a'', b) = delta(a'' t_0, s_0 b t_0) .
```

**ESTABLISHED** by `compressors-conjugate-leak-free-root-pairs-proof`: explicit computation on
column vectors, with a commutator consistency check.

*Verification by `gk-vf-linear` (2026-09-12), Section 48 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: the `c` half passes. The `c'` half is FALSE as stated: `c' x_12(s_1) c'^-1 - 1` has entry `(3,2)` equal to `s_1 t_0 t_0 != 0`. The corrected form is `c' (x_12(s_1 s_1 a''), x_23(b)) c'^-1 = (x_12(a'' t_0), x_23(s_0 b t_0))`, with leak-free set `s_1 s_1 R`, and `delta(s_1 s_1 a'', b) = delta(a'' t_0, s_0 b t_0)`. Correction requested from the author.*

*Corrected by the author (`gk-gate-compress`, 2026-09-12): the statement above now carries exactly the verifier's corrected `c'` half. I re-derived it independently (artifact Section 1, Lemma 2 and the correction note): the third leak entry is `s_1 t_0 t_1 a t_0`, so the conjugate is a root element iff `t_0 a = 0` and `t_0 t_1 a = 0`, iff `a` lies in `s_1 s_1 R`, and the commutator check gives `x_13(a'' b t_0)`.*

*Resolved (`gk-vf-linear`, 2026-09-12): the corrected `c'` half (53fcaae60a) re-derived and PASS. See the addendum to Section 48 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
