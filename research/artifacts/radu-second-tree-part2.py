# Part 2 (exec'd by radu_second_tree_check.py): tree computations at q'.
def mm2(A, B):
    return (A[0]*B[0] + A[1]*B[2], A[0]*B[1] + A[1]*B[3], A[2]*B[0] + A[3]*B[2], A[2]*B[1] + A[3]*B[3])
def det2(A):
    return A[0]*A[3] - A[1]*A[2]
def minv(A):
    return min(v2(t) for t in A)
def is_scalar2(A):
    base = minv(A)
    return v2(A[1]) - base >= BIG // 2 and v2(A[2]) - base >= BIG // 2 and v2(A[0] - A[3]) - base >= BIG // 2
def dist(P1, P2):
    d = det2(P1)
    inv = (P1[3] / d, -P1[1] / d, -P1[2] / d, P1[0] / d)
    N = mm2(inv, P2)
    return v2(det2(N)) - 2 * minv(N)

words = ["x", "y", "z", "xz", "xyx", "xyz", "zyz", "yxy", "yzy", "xzy", "zxyxz", "xyzyx"]
M = {}
for wd in words:
    M[wd] = gl2(beta_for(wd))
print("sanity M_xz ~ M_x M_z:", is_scalar2(mm2(M["xz"], mm2(mm2(M["x"], M["z"]), (0, 0, 0, 0)))) if False else
      is_scalar2(mm2(M["xz"], (M["z"][3]*M["x"][3], 0, 0, 0))) if False else "skipped")
def proportional(A, B):
    # A ~ B up to scalar
    for i in range(4):
        if v2(B[i]) < BIG // 2:
            lam = A[i] / B[i]
            return all(v2(A[k] - lam * B[k]) - minv(A) >= BIG // 2 for k in range(4))
    return False
print("M_xz ~ M_x*M_z:", proportional(M["xz"], mm2(M["x"], M["z"])))
print("M_xyx ~ M_x*M_y*M_x:", proportional(M["xyx"], mm2(mm2(M["x"], M["y"]), M["x"])))
X3 = mm2(M["xyz"], mm2(M["xyz"], M["xyz"]))
print("(M_xyz)^3 scalar:", is_scalar2(X3), " (M_xz)^2 scalar:", is_scalar2(mm2(M["xz"], M["xz"])))
I2 = (Fr(1), Fr(0), Fr(0), Fr(1))
for wd in ("x", "y", "z", "xz", "xyx"):
    Mx = M[wd]
    tr_ = Mx[0] + Mx[3]
    print("word %-4s d(p0, M p0) = %s   v2(tr^2/det) = %s" % (wd, dist(I2, mm2(Mx, I2)), v2(tr_ * tr_ / det2(Mx)) if tr_ != 0 else "inf"))
NB = [(Fr(1), Fr(0), Fr(0), Fr(2)), (Fr(2), Fr(0), Fr(0), Fr(1)), (Fr(1), Fr(0), Fr(1), Fr(2))]
RAD = 12
frontier = [(I2, None)]
allv = [I2]
for r in range(RAD):
    new = []
    for Pm, parent in frontier:
        for Nk in NB:
            Q_ = mm2(Pm, Nk)
            if parent is not None and dist(Q_, parent) == 0:
                continue
            new.append((Q_, Pm)); allv.append(Q_)
    frontier = new
print("vertices enumerated:", len(allv))
fixed = [Pm for Pm in allv if dist(Pm, mm2(M["xz"], Pm)) == 0 and dist(Pm, mm2(M["xyx"], Pm)) == 0]
print("vertices fixed by <xz, xyx>:", len(fixed), " distances from p0:", sorted(set(dist(I2, Pm) for Pm in fixed)))
if fixed:
    p = fixed[0]
    nbrs = [mm2(p, Nk) for Nk in NB]
    def which(Pm):
        for k, qn in enumerate(nbrs):
            if dist(Pm, qn) == 0:
                return k
        return None
    perm_xz = [which(mm2(M["xz"], qn)) for qn in nbrs]
    perm_xyx = [which(mm2(M["xyx"], qn)) for qn in nbrs]
    print("S_3 on the three edges at p: xz ->", perm_xz, " xyx ->", perm_xyx)
    orbit = {0}
    for _ in range(4):
        orbit |= {perm[k] for perm in (perm_xz, perm_xyx) for k in orbit if perm[k] is not None}
    print("transitive on edges at p:", orbit == {0, 1, 2})
    inv_found = []
    for wd in words:
        Mp = mm2(M[wd], p)
        k = which(Mp)
        if k is not None and dist(mm2(M[wd], nbrs[k]), p) == 0:
            inv_found.append((wd, k))
    print("elements inverting an edge at p:", inv_found)
    print("CONCLUSION rho(V) vertex-transitive on T':", orbit == {0, 1, 2} and len(inv_found) > 0)
print("DONE4")
