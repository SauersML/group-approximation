# Variant of part 2 (exec'd by radu-second-tree-check.py): does C = <a,b,c> fix the S_3-vertex p of T',
# and how does it permute the three edges at p?  Prediction (lane ex2-radu-superstrong-negative, (H4)):
# a, b, c fix p; a, b fix all three edges; c fixes edge E0 = [p, x p] and swaps E1 = [p, xy p], E2 = [p, zy p].
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
def proportional(A, B):
    for i in range(4):
        if v2(B[i]) < BIG // 2:
            lam = A[i] / B[i]
            return all(v2(A[k] - lam * B[k]) - minv(A) >= BIG // 2 for k in range(4))
    return False

words = ["a", "b", "c", "x", "y", "z", "xz", "xyx", "xy", "zy"]
M = {wd: gl2(beta_for(wd)) for wd in words}
print("M_c ~ M_y M_b M_y:", proportional(M["c"], mm2(mm2(M["y"], M["b"]), M["y"])))
print("involutions a,b,c:", [is_scalar2(mm2(M[h], M[h])) for h in "abc"])
print("M_xy ~ M_x M_y:", proportional(M["xy"], mm2(M["x"], M["y"])), " M_zy ~ M_z M_y:", proportional(M["zy"], mm2(M["z"], M["y"])))
for h in ("ab", "bc", "ca"):
    Mh = mm2(M[h[0]], M[h[1]]); t = Mh[0] + Mh[3]
    print("v2(tr^2/det) of", h, "=", v2(t * t / det2(Mh)))
I2 = (Fr(1), Fr(0), Fr(0), Fr(1))
NB = [(Fr(1), Fr(0), Fr(0), Fr(2)), (Fr(2), Fr(0), Fr(0), Fr(1)), (Fr(1), Fr(0), Fr(1), Fr(2))]
RAD = 5
frontier = [(I2, None)]; allv = [I2]
for r in range(RAD):
    new = []
    for Pm, parent in frontier:
        for Nk in NB:
            Q_ = mm2(Pm, Nk)
            if parent is not None and dist(Q_, parent) == 0:
                continue
            new.append((Q_, Pm)); allv.append(Q_)
    frontier = new
fixed = [Pm for Pm in allv if dist(Pm, mm2(M["xz"], Pm)) == 0 and dist(Pm, mm2(M["xyx"], Pm)) == 0]
print("vertices within radius", RAD, ":", len(allv), " fixed by <xz,xyx>:", len(fixed))
p = fixed[0]
nbrs = [mm2(p, Nk) for Nk in NB]
def which(Pm):
    ks = [k for k, qn in enumerate(nbrs) if dist(Pm, qn) == 0]
    return ks[0] if len(ks) == 1 else None
E = {"E0": which(mm2(M["x"], p)), "E0'": which(mm2(M["z"], p)), "E1": which(mm2(M["xy"], p)), "E2": which(mm2(M["zy"], p))}
print("edge labels at p (neighbour index):", E)
for h in ("a", "b", "c"):
    Mh = M[h]
    print("letter", h, " d(p, M p) =", dist(p, mm2(Mh, p)), " perm of neighbours:", [which(mm2(Mh, qn)) for qn in nbrs])
fixC = [Pm for Pm in allv if all(dist(Pm, mm2(M[h], Pm)) == 0 for h in "abc")]
print("vertices within radius", RAD, "fixed by a,b,c:", len(fixC), " contains p:", any(dist(Pm, p) == 0 for Pm in fixC),
      " distances from p:", sorted(dist(p, Pm) for Pm in fixC))
print("DONE_H4")
