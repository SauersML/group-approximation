#!/usr/bin/env python3
"""Batched Torch optimizer for Cairn's two-chart Leavitt-atlas diagnostics.

Discovery tool, not a proof.  It vectorizes many independent relative-unitary
starts on GPU and optimizes a smooth max of normalized HS relation defects.
Promising numerical behavior must be converted into an exact certificate.

Examples:
  python atlas_gpu_batched_search.py --problem complete --radius 2 --starts 64 --iters 500
  python atlas_gpu_batched_search.py --problem necessary --k 2 --starts 32 --iters 1000

On CUDA the expensive matrix products are batched across starts.  On CPU this
serves as a correctness/smoke-test fallback.
"""

import argparse
import json
import math
import os
import sys
import time
from typing import List, Tuple

import numpy as np
import torch

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from atlas_two_chart_search import Problem, matrix_key  # noqa: E402
from atlas_complete_window_search import CompleteWindowProblem  # noqa: E402


def complex_dtype(name: str):
    if name == "complex64":
        return torch.complex64
    if name == "complex128":
        return torch.complex128
    raise ValueError(name)


def haar_batch(batch: int, n: int, device, dtype, seed: int):
    gen = torch.Generator(device=device)
    gen.manual_seed(seed)
    real_dtype = torch.float32 if dtype == torch.complex64 else torch.float64
    z = torch.randn((batch, n, n), device=device, dtype=real_dtype, generator=gen)
    z = z + 1j * torch.randn((batch, n, n), device=device, dtype=real_dtype, generator=gen)
    z = z.to(dtype)
    q, r = torch.linalg.qr(z)
    diag = torch.diagonal(r, dim1=-2, dim2=-1)
    phase = diag / torch.where(diag.abs() == 0, torch.ones_like(diag.abs()), diag.abs())
    return q @ torch.diag_embed(phase.conj())


def project_unitary(u: torch.Tensor):
    q, r = torch.linalg.qr(u)
    diag = torch.diagonal(r, dim1=-2, dim2=-1)
    phase = diag / torch.where(diag.abs() == 0, torch.ones_like(diag.abs()), diag.abs())
    return q @ torch.diag_embed(phase.conj())


class TorchAtlasProblem:
    def __init__(self, problem, device, dtype):
        self.problem = problem
        self.n = problem.n
        self.device = device
        self.dtype = dtype

        keys = list(problem.reps.keys())
        self.key_to_index = {k: i for i, k in enumerate(keys)}
        reps_np = np.stack([problem.reps[k] for k in keys], axis=0)
        self.reps = torch.as_tensor(reps_np, device=device, dtype=dtype)
        self.words: List[List[Tuple[int, int]]] = []
        for word in problem.words:
            encoded = []
            for factor, g in word:
                encoded.append((factor, self.key_to_index[matrix_key(g)]))
            self.words.append(encoded)
        self.names = list(problem.names)

    def word_trace(self, u: torch.Tensor, encoded_word):
        # u: [B,n,n], result: [B]
        uh = u.mH
        value = torch.eye(self.n, dtype=self.dtype, device=self.device)
        value = value.expand(u.shape[0], -1, -1)
        for factor, rep_idx in encoded_word:
            a = self.reps[rep_idx]
            f = a.expand(u.shape[0], -1, -1) if factor == 1 else u @ a @ uh
            value = value @ f
        return torch.diagonal(value, dim1=-2, dim2=-1).sum(-1).real / self.n

    def traces(self, u: torch.Tensor, indices=None):
        if indices is None:
            indices = range(len(self.words))
        return torch.stack([self.word_trace(u, self.words[int(i)]) for i in indices], dim=1)


def smooth_max_defect_sq(traces: torch.Tensor, beta: float):
    # defect^2 = 2 - 2 Re tau(word).  Smooth max separately for every start.
    dsq = 2.0 - 2.0 * traces
    return torch.logsumexp(beta * dsq, dim=1) / beta


def diagnostics(tp: TorchAtlasProblem, u: torch.Tensor, chunk: int = 0):
    with torch.no_grad():
        if not chunk or chunk >= len(tp.words):
            t = tp.traces(u)
        else:
            parts = []
            for lo in range(0, len(tp.words), chunk):
                parts.append(tp.traces(u, range(lo, min(lo + chunk, len(tp.words)))))
            t = torch.cat(parts, dim=1)
        dsq = torch.clamp(2.0 - 2.0 * t, min=0.0)
        d = torch.sqrt(dsq)
        rms = torch.sqrt(dsq.mean(dim=1))
        mx, idx = d.max(dim=1)
        best = torch.argmin(mx)
        b = int(best.item())
        worst_idx = torch.topk(d[b], k=min(5, d.shape[1]), largest=True).indices.tolist()
        return {
            "best_start": b,
            "best_max_defect": float(mx[b].cpu()),
            "best_rms_defect": float(rms[b].cpu()),
            "best_mean_trace": float(t[b].mean().cpu()),
            "worst": [[tp.names[i], float(d[b, i].cpu())] for i in worst_idx],
            "median_max_defect": float(mx.median().cpu()),
        }, b


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem", choices=["necessary", "complete"], default="complete")
    ap.add_argument("--radius", type=int, default=2)
    ap.add_argument("--k", type=int, default=1)
    ap.add_argument("--starts", type=int, default=16)
    ap.add_argument("--iters", type=int, default=100)
    ap.add_argument("--lr", type=float, default=0.03)
    ap.add_argument("--beta", type=float, default=12.0)
    ap.add_argument("--constraint-batch", type=int, default=0,
                    help="random constraint minibatch per step; 0 means all")
    ap.add_argument("--seed", type=int, default=1729)
    ap.add_argument("--report-every", type=int, default=20)
    ap.add_argument("--dtype", choices=["complex64", "complex128"], default="complex64")
    ap.add_argument("--device", default="auto")
    ap.add_argument("--save", type=str)
    args = ap.parse_args()

    if args.problem == "necessary":
        p = Problem(args.k)
        window = {"problem": "necessary", "constraints": len(p.words)}
    else:
        p = CompleteWindowProblem(args.radius, args.k)
        window = {"problem": "complete", **p.window_summary}

    if args.device == "auto":
        device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    else:
        device = torch.device(args.device)
    dtype = complex_dtype(args.dtype)
    if device.type == "cpu" and dtype == torch.complex64:
        # complex128 is generally more trustworthy for CPU diagnostics.
        dtype = torch.complex128

    tp = TorchAtlasProblem(p, device, dtype)
    u0 = haar_batch(args.starts, p.n, device, dtype, args.seed)
    # Projected Adam: optimize ambient matrices, QR-project after every step.
    u = torch.nn.Parameter(u0.clone())
    opt = torch.optim.Adam([u], lr=args.lr)

    started = time.time()
    diag, _ = diagnostics(tp, u)
    print(json.dumps({"event": "start", "device": str(device), "dtype": str(dtype),
                      "starts": args.starts, "dimension": p.n, **window, **diag}), flush=True)

    best_u = None
    best_diag = diag
    for it in range(1, args.iters + 1):
        opt.zero_grad(set_to_none=True)
        if args.constraint_batch and args.constraint_batch < len(tp.words):
            # A shared random minibatch keeps the batch dimension contiguous on GPU.
            # Full max-defect diagnostics are still recomputed at report points.
            idx = torch.randperm(len(tp.words), device=device)[:args.constraint_batch].cpu().tolist()
            traces = tp.traces(u, idx)
        else:
            traces = tp.traces(u)
        per_start = smooth_max_defect_sq(traces, args.beta)
        loss = per_start.mean()
        loss.backward()
        opt.step()
        with torch.no_grad():
            u.copy_(project_unitary(u))
        if it % args.report_every == 0 or it == args.iters:
            diag, best_index = diagnostics(tp, u)
            if diag["best_max_defect"] < best_diag["best_max_defect"]:
                best_diag = diag
                best_u = u[best_index].detach().cpu().numpy().copy()
            print(json.dumps({"event": "progress", "iteration": it,
                              "elapsed_s": round(time.time() - started, 3),
                              "loss": float(loss.detach().cpu()), **diag}), flush=True)

    if best_u is None:
        _, best_index = diagnostics(tp, u)
        best_u = u[best_index].detach().cpu().numpy().copy()
    if args.save:
        np.save(args.save, best_u)
    print(json.dumps({"event": "final", "elapsed_s": round(time.time() - started, 3),
                      **window, **best_diag}), flush=True)


if __name__ == "__main__":
    main()
