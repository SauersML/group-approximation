"""Completeness certificate for an orbit list produced by enumerate_pg2.py.
Rebuilds the same CNF (lambda bijection + exact cover by cyclic triangle classes + lambda(0) in {L_flag, L_anti}),
blocks every PGL(3,q)-image of every listed presentation, and then proves UNSAT cube by cube:
cube = (lambda(0) = L0, lambda(1) = L1, ..., lambda(depth-1) = L_{depth-1}); these cubes cover every assignment
satisfying the breaking clause.  UNSAT on every cube => the list contains every PGL(3,q)-orbit.
Resumable: finished cubes are appended to <progress file>.  Usage: Q=q complete_pg2.py orbits.json progress.txt [depth]"""
import json, os, sys, time, itertools
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "enumerate_pg2.py")).read().split("OUT = sys.argv[1]")[0]
exec(src)
ORB, PROG = sys.argv[1], sys.argv[2]
depth = int(sys.argv[3]) if len(sys.argv) > 3 else 2

def block_orbit(T):
    seen = set()
    for g in G:
        img = frozenset(cls((g[a], g[b], g[c])) for (a, b, c) in T)
        if img in seen: continue
        seen.add(img)
        if lam0(img) in (Lflag, Lanti):
            S.add_clause([-tv[cid[c]] for c in img])
reps = [[tuple(t) for t in T] for T in json.load(open(ORB))]
t0 = time.time()
for T in reps: block_orbit(T)
print(f"blocked {len(reps)} orbits ({time.time()-t0:.0f}s)", flush=True)
done = set()
if os.path.exists(PROG):
    for line in open(PROG):
        c, r = line.split()
        done.add(c)
        if r != "UNSAT": sys.exit("non-UNSAT cube recorded: " + line)
for L0 in (Lflag, Lanti):
    for rest in itertools.product(range(n), repeat=depth - 1):
        cube = (L0,) + rest
        if len(set(cube)) < len(cube): continue          # lambda injective: cube trivially UNSAT
        key = "-".join(map(str, cube))
        if key in done: continue
        t1 = time.time()
        r = S.solve(assumptions=[lam[x][L] for x, L in enumerate(cube)])
        res = "SAT" if r else "UNSAT"
        with open(PROG, "a") as f: f.write(f"{key} {res}\n")
        print(f"cube {key}: {res} ({time.time()-t1:.0f}s)", flush=True)
        if r:
            m = set(l for l in S.get_model() if l > 0)
            print("NEW ORBIT:", json.dumps([classes[i] for i, v in enumerate(tv) if v in m]))
            sys.exit(1)
print(f"COMPLETE: all cubes UNSAT; the {len(reps)} listed orbits are all PGL(3,q)-orbits")
