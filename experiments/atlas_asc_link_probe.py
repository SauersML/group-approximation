"""Is the linearized defect controlled by the true defect?  The only gap left.

Two exact facts, for every unitary `U in U(20160k)` and every fold-trivial
atlas word `s` (all 234 first-boundary words are fold-trivial):

  (E1)  pi_U(s) = prod_j rho(u_j)( f(g_j) ),   f(g) = [U, lambda(g)],
        rho(x)Y = lambda(x) Y lambda(x)^(-1),  u_j the prefix before the j-th
        K2 syllable.  Exact, not a linearization: each factor is
        V_(u_j) V_(v_j)^(-1) with V_x = rho(x)U, and fold-triviality
        (`prod of all syllables = 1`) is what closes the telescope.

  (E2)  a^2+b^2 = <U, rho(W_cov) U>  and  sum_s l_s^2 = <U, rho(W_pkt) U>,
        where l_s = ||rho(z_s)U||_2 and W_cov, W_pkt are the two integral
        group-algebra elements of `atlas_asc_tangent_exact.py`.  Both sides
        are quadratic FORMS in U, so the generalized eigenvalue bound

            a^2 + b^2 <= (1/14) * sum_s l_s^2

        holds for every matrix U at every multiplicity -- it was never a
        first-order statement.  What is first order is only the comparison of
        l_s with the true defect ||pi_U(s)-1||_2.

So the whole remaining gap in the local half of (ASC) is one inequality:

            sum_s l_s^2  <=  C' * sum_s ||pi_U(s)-1||_2^2   ?          (LINK)

This script (i) checks (E1) and (E2) numerically, and (ii) searches for the
worst ratio in (LINK).  If the ratio is unbounded the route dies here and we
learn it cheaply; if it saturates, (LINK) with that constant plus the exact
1/14 closes the local half globally.

Note where the difficulty must live: pi_U(s)-1 = sum_j (W_j-1) + cross terms,
and in normalized HS the cross terms are NOT second order -- ||(A-1)(B-1)||_2
only gives ||A-1||_op ||B-1||_2.  That is exactly the operator-norm-versus-HS
gap that makes hyperlinearity harder than MF, so a positive answer to (LINK)
cannot come from a Taylor estimate.
"""

import argparse
import json
import math
import time

import numpy as np
import torch

from atlas_asc_covariance_gpu import (Packet, chunk_defects, geodesic_step,
                                      polar_retract, probes_of)
from atlas_asc_tangent_ratio import word_forms


def measure(packet, theta, probe, body_chunks, cov_chunks):
    """(sum true defect^2, sum linearized l^2, cov^2) over the whole packet."""
    true_sq = 0.0
    linear_sq = 0.0
    worst = ("", 0.0, 0.0)
    for index in body_chunks:
        chunk = packet.chunks[index]
        true_values = chunk_defects(packet, chunk, theta, probe)
        linear_values = word_forms(packet, chunk, theta, probe)
        true_sq += float(true_values.sum())
        linear_sq += float(linear_values.sum())
        position = int(linear_values.argmax())
        if float(linear_values[position]) > worst[1]:
            worst = (packet.names[chunk[0][position]],
                     float(linear_values[position]),
                     float(true_values[position]))
    cov = sum(float(chunk_defects(packet, packet.chunks[which], theta,
                                  probe).sum()) for which in cov_chunks)
    return true_sq, linear_sq, cov, worst


def run(args):
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    torch.manual_seed(args.seed)
    generator = torch.Generator(device=device)
    generator.manual_seed(args.seed)
    torch.backends.cuda.matmul.allow_tf32 = bool(args.tf32)

    packet = Packet(args.npz, args.k, device,
                    {"certified", "boundary", "phase"}, args.word_batch)
    n = packet.n
    cov_chunks = sorted({packet.by_position[packet.names.index("cov:a")],
                         packet.by_position[packet.names.index("cov:b")]})
    body_chunks = [index for index, chunk in enumerate(packet.chunks)
                   if all(position < packet.packet_words
                          for position in chunk[0])]

    started = time.time()
    log = open(args.out, "a", buffering=1) if args.out else None

    def emit(record):
        record["elapsed_s"] = round(time.time() - started, 1)
        line = json.dumps(record, sort_keys=True)
        print(line, flush=True)
        if log:
            log.write(line + "\n")

    emit({"event": "start", "n": n, "k": args.k, "mode": args.mode,
          "probes": args.probes, "seed": args.seed,
          "device": torch.cuda.get_device_name(0)
          if device.type == "cuda" else "cpu"})

    def unitary(scale):
        block = torch.randn(n, n, dtype=torch.complex64, device=device,
                            generator=generator) / math.sqrt(n)
        if scale is not None:               # exp-like perturbation of the fold
            block = torch.eye(n, dtype=torch.complex64, device=device) + (
                scale * (block - block.conj().t()) * 0.5)
        factor, upper = torch.linalg.qr(block)
        phase = torch.diagonal(upper)
        factor = factor * (phase / phase.abs()).conj().unsqueeze(0)
        return torch.stack((factor.real.contiguous(),
                            factor.imag.contiguous()))

    # ---- (E2) the exact inequality, at several distances from the fold ----
    if args.mode in ("check", "both"):
        for scale in (None, 1.0, 0.3, 0.1, 0.03):
            theta = unitary(scale)
            probe = probes_of(n, args.eval_probes, device, generator)
            true_sq, linear_sq, cov, worst = measure(
                packet, theta, probe, body_chunks, cov_chunks)
            emit({"event": "check", "init": "haar" if scale is None
                  else "fold+%.2f" % scale,
                  "cov_sq": cov, "linear_sq": linear_sq, "true_sq": true_sq,
                  "cov_over_linear": cov / linear_sq if linear_sq else None,
                  "bound_1_over_14": 1.0 / 14.0,
                  "exact_bound_holds": bool(cov <= linear_sq / 14.0 + 1e-6),
                  "link_ratio_linear_over_true":
                      linear_sq / true_sq if true_sq else None,
                  "worst_word": worst[0], "worst_linear": worst[1],
                  "worst_true": worst[2]})

    # ---- (LINK) adversarial search: push linear up, true defect down ----
    if args.mode in ("search", "both"):
        theta = unitary(args.init_scale if args.init_scale > 0 else None)
        theta.requires_grad_(True)
        velocity = None
        best = 0.0
        for step in range(1, args.iterations + 1):
            theta.grad = None
            probe = probes_of(n, args.probes, device, generator)
            index = body_chunks[np.random.RandomState(
                args.seed + step).randint(len(body_chunks))]
            chunk = packet.chunks[index]
            true_values = chunk_defects(packet, chunk, theta, probe)
            linear_values = word_forms(packet, chunk, theta, probe)
            loss = (torch.log(true_values.sum() + args.floor)
                    - torch.log(linear_values.sum() + args.floor))
            loss.backward()
            with torch.no_grad():
                if velocity is None:
                    velocity = torch.zeros_like(theta)
                velocity.mul_(args.momentum).add_(theta.grad)
            # exactly unitary step: a projected one collapses U toward 0,
            # where a = ||U lambda(h) U^* - lambda(h)||_2 stops equalling
            # ||U - rho(h)U||_2 and every reported ratio is meaningless
            geodesic_step(theta.detach(), velocity, args.rank, args.lr,
                          generator)
            if step % args.retract_every == 0:
                polar_retract(theta.detach(), 1)
            if step % args.report_every == 0:
                probe = probes_of(n, args.eval_probes, device, generator)
                polar_retract(theta.detach(), 1)
                true_sq, linear_sq, cov, worst = measure(
                    packet, theta.detach(), probe, body_chunks, cov_chunks)
                ratio = linear_sq / true_sq if true_sq else float("inf")
                best = max(best, ratio)
                emit({"event": "search", "step": step, "true_sq": true_sq,
                      "linear_sq": linear_sq, "cov_sq": cov,
                      "link_ratio_linear_over_true": ratio, "best": best,
                      "exact_bound_holds":
                          bool(cov <= linear_sq / 14.0 + 1e-6)})
    if log:
        log.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--npz", default="experiments/atlas-asc-packet.npz")
    parser.add_argument("--mode", default="both",
                        choices=("check", "search", "both"))
    parser.add_argument("--k", type=int, default=1)
    parser.add_argument("--probes", type=int, default=16)
    parser.add_argument("--eval-probes", type=int, default=128)
    parser.add_argument("--word-batch", type=int, default=48)
    parser.add_argument("--iterations", type=int, default=400)
    parser.add_argument("--lr", type=float, default=0.05)
    parser.add_argument("--momentum", type=float, default=0.9)
    parser.add_argument("--rank", type=int, default=64)
    parser.add_argument("--init-scale", type=float, default=0.0)
    parser.add_argument("--floor", type=float, default=1e-12)
    parser.add_argument("--retract-every", type=int, default=10)
    parser.add_argument("--report-every", type=int, default=50)
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--tf32", type=int, default=1)
    parser.add_argument("--out", default="")
    run(parser.parse_args())


if __name__ == "__main__":
    main()
