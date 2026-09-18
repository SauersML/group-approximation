# Seward's approximate Bernoulli models put every finite-alphabet free action at the uniform Bernoulli point, and lower semicontinuity there is the Bernoulli cost bound

*Attempt artifact (2026-09-17), formerly route `fpbs-fixed-price-iff-cost-lsc-at-bernoulli-proof` into `fpbs-fixed-price-iff-cost-lsc-at-bernoulli`, requires [fpbs-finite-alphabet-models-suffice-for-fixed-price, seward-approximate-bernoulli-models-and-semicontinuity, abert-weiss-free-actions-weakly-contain-bernoulli, cost-is-constant-on-weak-equivalence-classes, fpbs-clopen-certificate-cost-transfer]. Demoted from the graph because the referee vote of lens 1 was lost for this result; lenses 2 and 3 returned *survives* (verdicts 0fcd9e35 and 3e997aca). No mathematical error has been reported. Restore it as a route once a full referee pass survives.*

Full written proof.

**Bernoulli maximality.** For free `a`, `lambda^G ≺ a` by
`abert-weiss-free-actions-weakly-contain-bernoulli`, so `C(a) <= C(lambda^G)` by
`cost-is-constant-on-weak-equivalence-classes`. Any two nontrivial Bernoulli shifts weakly
contain each other, so `C(lambda^G) = C(b)` for every nontrivial Bernoulli `b`. This gives the
remark that upper semicontinuity at `lambda^G` is automatic, so 2 is equivalent to 3.

**1 implies 2.** Under fixed price, `C` is constant on `F_G(L) ∪ {lambda^G}`.

**2 implies 1.** By `fpbs-finite-alphabet-models-suffice-for-fixed-price` it suffices to show
`C(nu_0) >= C(b)` for every finite `K` and every essentially free ergodic `nu_0` on `K^G`. The
time-zero partition of `K^G` generates, so the Rokhlin entropy of `a' = G ↷ (K^G, nu_0)` is at
most its Shannon entropy, which is at most `log |K|`. Take `L` with `|L| = |K| + 1` and `lambda`
uniform, so `h^Rok(a') <= log|K| < log|L| = H(lambda)`. `G` is countably infinite and `a'` is
free and ergodic, so item 1 of `seward-approximate-bernoulli-models-and-semicontinuity`
(Corollary 6.1) applies. Every weak* neighbourhood of `lambda^G` in `E_G(L^G)` contains a measure
`nu` with `G ↷ (L^G, nu)` isomorphic to `a'`. `E_G(L^G)` is metrizable, so there is a sequence
`nu_n -> lambda^G` of such models. Each `nu_n` lies in `F_G(L)`, since freeness and ergodicity are
isomorphism invariants, and each has cost `C(nu_0)`, since cost is an isomorphism invariant.
Lower semicontinuity gives `C(b) = C(lambda^G) <= liminf C(nu_n) = C(nu_0)`.

**Counterexample normal form.** If fixed price fails, the finite-alphabet reduction gives a
free ergodic `nu_0` on some `K^G` with `C(nu_0) < C(b)`, and the paragraph above gives the models
`nu_n`. If `(Phi, l)` has `c_l(Phi, nu_n) <= C(b) - eta/2` and
`(M + |S|) TV_W(nu_n, lambda^G) < eta/2`, item 3 of `fpbs-clopen-certificate-cost-transfer` gives
`C(lambda^G) < C(b)`, a contradiction. This is the race inequality.
