---
rg: 2
id: stw64-supersoft-gap-proof
kind: route
title: Weak cancellation and compact uniform rank cuts compute the supersoft gap
target: stw64-supersoft-gap-is-comparison-radius
requires: [stw64-supersoft-calculus]
artifacts:
  - research/artifacts/stw64-supersoft-comparison-gap-2026-09-04.md
---

If s_a<<s_b and x-hat+(b-a)*u-hat<=y-hat, the absorption identity gives
x+s_b<=y+s_a. Weak cancellation gives x<=y, so rc(A)<=b-a.

Conversely, choose an admissible comparison constant R<b-a and a rapidly
increasing sequence z_n with supremum s_b. The increasing open subsets
{tau:tau(z_n)>a+R} cover the compact normalized quasitrace space, since
tau(s_b)=b. One z_n therefore has this inequality uniformly. Comparison
gives s_a<=z_n<<s_b. Taking infima proves the formula, including infinite
radius. The artifact supplies the complete argument.
