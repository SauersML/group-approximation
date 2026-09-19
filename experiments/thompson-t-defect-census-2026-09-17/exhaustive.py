"""Exhaustive profile sweep in dimension n: every spectral profile (m, k) of an
exact pair, modulo complex conjugation (m1<->m3, k1<->k2), except the trivial
one, with several random eigenbases each; fixed-profile L-BFGS (lbfgs.optimise)
with Schatten schedule ending at p = 96.  One JSON line per run.

usage: python3 exhaustive.py n seeds out.jsonl [workers]
"""
import itertools, json, sys, time
import multiprocessing as mp


def comps(n, parts):
    for c in itertools.combinations(range(n + parts - 1), parts - 1):
        b = [-1] + list(c) + [n + parts - 1]
        yield tuple(b[i + 1] - b[i] - 1 for i in range(parts))


def job(args):
    import torch
    torch.set_num_threads(1)
    from lbfgs import optimise
    n, m, k, seed = args
    t = time.time()
    try:
        D, d, K, A, B = optimise(m, k, seed, ("r1", "r2", "rP"), ps=(2, 8, 32, 96), iters=150, rounds=3)
    except Exception as e:
        return {"n": n, "m": m, "k": k, "seed": seed, "error": repr(e)}
    return {"n": n, "m": m, "k": k, "seed": seed, "D": D, "parts": d, "sec": round(time.time() - t, 1)}


if __name__ == "__main__":
    n, seeds, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    workers = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    seen = set()
    tasks = []
    for m in comps(n, 4):
        for k in comps(n, 3):
            if m[0] == n and k[0] == n:
                continue
            key = (m, k)
            conj = ((m[0], m[3], m[2], m[1]), (k[0], k[2], k[1]))
            if conj in seen:
                continue
            seen.add(key)
            for s in range(seeds):
                tasks.append((n, m, k, 1000 * s + 7))
    print(len(tasks), "tasks", flush=True)
    with mp.Pool(workers) as pool, open(out, "a") as f:
        for res in pool.imap_unordered(job, tasks):
            f.write(json.dumps(res) + "\n")
            f.flush()
