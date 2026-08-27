---
rg: 2
id: square-free-iwahori-presentation-proof
kind: route
title: Recover the half parabolic as r inverse t squared r
target: iwahori-square-free-bs14-presentation
requires:
  - iwahori-square-root-presentation-is-bs14-plus-one-involution
---

Start from `(B2)` in
`iwahori-square-root-presentation-is-bs14-plus-one-involution`:

```text
x^2=1, (xr)^2=1, (xs^2)^3=1,
r s r^(-1)=s^4, (xrs)^3=1.                            (SFE1)
```

Set `t=s^2`.  Squaring the BS row gives `r t r^(-1)=t^4`.  The
unsquared row gives `r s r^(-1)=s^4=t^2`, hence
`s=r^(-1)t^2r`.  Thus

```text
xrs=x r(r^(-1)t^2r)=x t^2r.                          (SFE2)
```

Substitution proves every relation in `(SFP1)`.

Conversely, assume `(SFP1)` and define `s=r^(-1)t^2r`.  The BS row gives

```text
s^2=r^(-1)t^4r=t.                                     (SFE3)
```

Therefore `r s r^(-1)=t^2=s^4`, `(xt)^3=(xs^2)^3`, and
`(xt^2r)^3=(xrs)^3` by `(SFE2)`.  This proves the reversible exact Tietze
move.

For the quantitative old-to-new statement, put
`e=r s r^(-1)-s^4`.  Since multiplication is isometric and squares
telescope,

```text
||r t r^(-1)-t^4||_2
 =||(r s r^(-1))^2-s^8||_2<=2||e||_2.                 (SFE4)
```

Moreover `||rs-s^4r||_2=||e||_2`, so

```text
||x t^2r-xrs||_2=||x(s^4r-rs)||_2<=||e||_2.           (SFE5)
```

Telescoping a cube costs a factor at most three, proving the claimed second
cubic loss.  The first cubic is literally unchanged.

For the new-to-old statement, put `e=r t r^(-1)-t^4` and
`s=r^(-1)t^2r`.  Then

```text
||s^2-t||_2=||r^(-1)t^4r-t||_2=||e||_2.               (SFE6)
```

Since `rsr^(-1)=t^2` and squares again telescope,

```text
||r s r^(-1)-s^4||_2=||t^2-s^4||_2<=2||t-s^2||_2.    (SFE7)
```

The second cubic is literally unchanged by `(SFE2)`, while replacing `t`
by `s^2` in the first cubic and telescoping its cube costs at most
`3||t-s^2||_2`.  This proves all fixed-constant defect bounds.

