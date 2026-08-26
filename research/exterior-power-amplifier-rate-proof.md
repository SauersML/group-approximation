---
rg: 2
id: exterior-power-amplifier-rate-proof
kind: route
title: Determinant character of the exterior algebra and the scalar-phase computation
target: exterior-power-amplifier-needs-dimension-defect-rate
requires: []
---

`Tr(Lambda^k U)` is the `k`-th elementary symmetric function of the
eigenvalues, so `Tr(Lambda^* U) = prod_j (1 + lambda_j) = det(1 + U)` and the
normalized character is `2^(-d) det(1 + U)`.  For `|lambda| = 1`,
`|(1 + lambda)/2|^2 = 1 - |lambda - 1|^2/4`, giving (1) since every other factor
has modulus at most `1`.  For `W = e^(i epsilon) 1`, `Lambda^k W` is the scalar
`e^(i k epsilon)`, so `chi_F(W) = ((1 + e^(i epsilon))/2)^d` and
`chi_R(W) = |chi_F(W)|^2 = cos(epsilon/2)^(2d)`; for a unitary `X`,
`||X - 1||_2^2 = 2 - 2 Re tr(X)`, which gives (2), and
`cos(epsilon/2)^(2d) = exp(2d log cos(epsilon/2)) = exp(-(1 + o(1)) d epsilon^2/4)`.
(3) is immediate.
