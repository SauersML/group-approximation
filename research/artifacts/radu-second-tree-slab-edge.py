# Part 3 (exec'd after radu-second-tree-check.py, reusing its globals p, nbrs, which, gl2, beta_for, dist, mm2).
# Which of a, b, c, x, z fix the edge e' = {p, nbrs[0]} of T', and which invert it?
# Expectation under psi' = orientation character of e': a, b fix both endpoints; c, x, z swap them.
print("== slab edge check at q': e' = {p, nbrs[0]}")
M3 = {wd: gl2(beta_for(wd)) for wd in ("a", "b", "c", "x", "z", "xz", "ab", "bc", "ca")}
report = {}
for wd, Mx in M3.items():
    fp = dist(p, mm2(Mx, p)) == 0
    fq = dist(nbrs[0], mm2(Mx, nbrs[0])) == 0
    sw = dist(mm2(Mx, p), nbrs[0]) == 0 and dist(mm2(Mx, nbrs[0]), p) == 0
    status = "fixes endpoints" if (fp and fq) else ("inverts e'" if sw else "moves e'")
    report[wd] = status
    print("word %-3s  fixes p: %-5s fixes q: %-5s swaps p,q: %-5s  => %s" % (wd, fp, fq, sw, status))
psi = {"a": 1, "b": 1, "c": -1, "x": -1, "z": -1}
agree = all((report[w] == "fixes endpoints") == (psi[w] == 1) and report[w] != "moves e'" for w in psi)
print("psi' equals the orientation character of e' on a,b,c,x,z:", agree)
print("DONE5")
