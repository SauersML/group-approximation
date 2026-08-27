---
rg: 2
id: odd-leavitt-prefix-whitehead-proof
kind: route
title: Insert the odd-characteristic sign in the coarse-to-fine Whitehead word
target: odd-leavitt-prefix-whitehead-transport
requires:
  - affine-active-corner-has-faithful-binary-leavitt-envelope
---

The relative prefix table gives `(OLW2)`.  Direct multiplication yields

```text
E_12(x)E_21(-y)
 =[[1-xy,x],[-y,1]],
```

and multiplying by `E_12(x)` on the right gives

```text
[[1-f,(1-f)x+x],[-y,1-yx]]
 =[[1-f,x],[-y,1-e]].
```

The inverse and the corner conjugacy then follow by the displayed block
products in the claim.  All signs are valid over the native field of
characteristic `p>=5`.
