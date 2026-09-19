---
rg: 2
id: stw99-lxxvi-cutoff-density-local-control-proof
kind: route
title: Approximate polar transitivity proves density while a CAR phase family forbids small corrections
target: stw99-lxxvi-cutoff-density-without-local-openness
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-dense-cutoff-restriction-and-local-control-2026-09-05.md
---

For target frames v_0,v with equal Gram b, x=v v_0* belongs to
Her(d) and |x|=v_0v_0*. Approximate x by invertibles and take polar
unitaries u. A spectral split gives
||u v_0-v||<=3 sqrt(||u|x|-x||). Acting on an existing larger
frame therefore gives restrictions approaching every prescribed
cutoff frame. This is the frame form of CEI's prior-art theorem.

For the local obstruction use the CAR diagonal, c=sum 2^(-n)e_n,
a=(c-1/4)_+, b=(c-1/2)_+, and w_0=sqrt(a). Let chi equal 1 on
(-infinity,1] and 0 on [2,infinity), continuously between, and set
v_t=sqrt(b) exp(i pi chi((c-1/2)/t)). The frames have exact lifts
sqrt(a) exp(i pi chi((c-1/2)/t)), while
||v_t-sqrt(b)||<=2 sqrt(2t).

If a restriction approximates v_t to sqrt(t)/2, apply the diagonal
conditional expectation and evaluate at a point where c=1/2+t.
The target frame there is -sqrt(t), whereas the restriction of w_0
is sqrt(t). Dividing their forced separation by sqrt(t)/sqrt(1/4+t)
gives ||w-w_0||>=(3/2)sqrt(1/4+t)>=3/4. This excludes a target
neighborhood from the closure of every small source-ball image.

All definitions, the primary CEI reference, and the expectation
calculation are given in the shared artifact. The argument makes
no inference from pointwise density to continuous parameterized lifts.
