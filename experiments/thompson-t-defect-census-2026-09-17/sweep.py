"""Random-restart sweep over dimensions and spectral profiles.

For each dimension n in the range, sample profiles (m, k) (A multiplicities over
4th roots, B multiplicities over cube roots), excluding the trivial pair, and run
lbfgs.optimise from a random eigenbasis.  One JSON line per run.

usage: python3 sweep.py nmin nmax runs_per_n out.jsonl [workers] [profile_mode]
profile_mode: 'random' (uniform compositions) or 'balanced' (near n/4, n/3).
"""
import json, math, random, sys, time
import multiprocessing as mp


def compositions(n, parts, rng, mode):
    if mode == "balanced":
        base = [n // parts] * parts
        for i in rng.sample(range(parts), n - sum(base)):
            base[i] += 1
        # small random shuffle of mass
        for _ in range(rng.randint(0, 2)):
            i, j = rng.sample(range(parts), 2)
            if base[i] > 0:
                base[i] -= 1
                base[j] += 1
        return tuple(base)
    cuts = sorted(rng.randint(0, n) for _ in range(parts - 1))
    return tuple(b - a for a, b in zip([0] + cuts, cuts + [n]))


def job(args):
    import torch
    torch.set_num_threads(1)
    from lbfgs import optimise
    n, m, k, seed = args
    t = time.time()
    try:
        D, d, K, A, B = optimise(m, k, seed, ("r1", "r2", "rP"), ps=(2, 8, 32, 96), iters=150, rounds=3)
    except Exception as e:  # numerical failure: record and continue
        return {"n": n, "m": m, "k": k, "seed": seed, "error": repr(e)}
    return {"n": n, "m": m, "k": k, "seed": seed, "D": D, "parts": d, "sec": round(time.time() - t, 1)}


if __name__ == "__main__":
    nmin, nmax, runs, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    mode = sys.argv[6] if len(sys.argv) > 6 else "random"
    rng = random.Random(20260917 + nmin * 1000 + nmax)
    tasks = []
    for n in range(nmin, nmax + 1):
        for r in range(runs):
            while True:
                m = compositions(n, 4, rng, mode)
                k = compositions(n, 3, rng, mode)
                if not (m[0] == n and k[0] == n):
                    break
            tasks.append((n, m, k, rng.randint(0, 10 ** 6)))
    with mp.Pool(workers) as pool, open(out, "a") as f:
        for res in pool.imap_unordered(job, tasks):
            f.write(json.dumps(res) + "\n")
            f.flush()
