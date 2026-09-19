"""The local constant of (ASCq): a Rayleigh quotient, not a search.

At the certified classical fold `U = I` every one of the 234 first-boundary
words of the atlas packet is *exactly* trivial (verified by the U = I gate of
`atlas_asc_covariance_gpu.py`), so along `U = exp(eps A)` both sides of

    a^2+b^2 <= C * sum_(s in S_0) ||pi_U(s)-1||_2^2                  (ASCq)

start at order eps^2 with explicit quadratic forms.  Writing a word as
`s = ... g_j ...` with the K2 syllables at positions j, prefix `p_j` and
suffix `q_j` in A_8,

    d/deps pi_s(exp(eps A))|_0 = sum_j lambda(p_j) [A, lambda(g_j)] lambda(q_j),
    d/deps (U lambda(h) U^* ) |_0 = [A, lambda(h)],

so with

    D(A)    = sum_s || sum_j lambda(p_j)[A,lambda(g_j)]lambda(q_j) ||_2^2,
    Ncov(A) = ||[A,lambda(h_a)]||_2^2 + ||[A,lambda(h_b)]||_2^2,

the sharp local constant is

    C_loc = sup { Ncov(A) / D(A) : A skew-Hermitian, D(A) > 0 }.

C_loc finite is exactly the first-order half of the collapse claim, and is
the quantitative form of the tangent certificate recorded in
`research/atlas-two-s3-covariance-collapse` (whose kernel statement is
qualitative: the common derivative kernel of five boundary words is the
H-fixed space).  C_loc infinite -- a skew A killing every packet word to
first order while moving the two S_3 covariances -- would refute the claim
outright at first order.

Reporting both `--packet certified,boundary,phase` and the same plus
`interior` measures precisely what the one interior separator buys, which is
item 5 of the node's attempt list.

The quotient is maximized by normalized gradient ascent on the sphere
||A||_F^2 = N; every quadratic form is estimated with fresh Rademacher
probes, so the reported value is a stochastic lower bound on C_loc that
rises monotonically as the iteration converges.  Evidence, not proof: a
converged Rayleigh quotient is a lower bound on the supremum, and the
supremum itself is only the FIRST-ORDER constant.
"""

import argparse
import json
import math
import time

import numpy as np
import torch

from atlas_asc_covariance_gpu import (ORDER, Packet, apply_u, apply_u_h,
                                      probes_of)


def commutator(theta, index, state, n, width, b):
    """[A, lambda(g)] applied to a state, lambda(g) given as a gather."""
    left = apply_u(theta, state.view(2, n, width * b)).view(2, n * width, b)
    left = left.index_select(1, index)
    right = state.index_select(1, index)
    right = apply_u(theta, right.view(2, n, width * b)).view(2, n * width, b)
    return right - left


def word_forms(packet, chunk, theta, probe):
    """|| sum_j lambda(p_j)[A,lambda(g_j)]lambda(q_j) ||_2^2 per word.

    Applied to probes right to left: carrying the running suffix product as a
    gather keeps every K1 syllable free, and each K2 syllable costs the two
    GEMMs of one commutator.
    """
    group, pattern, index = chunk
    width, n, b = len(group), packet.n, probe.shape[2]
    base = probe.unsqueeze(2).expand(2, n, width, b).reshape(2, n * width, b)
    suffix = base                      # lambda(q_j) v, built up from the right
    total = torch.zeros_like(base)
    for depth in reversed(range(len(pattern))):
        if pattern[depth] == 1:
            suffix = suffix.index_select(1, index[depth])
            total = total.index_select(1, index[depth])
        else:
            total = total.index_select(1, index[depth])
            total = total + commutator(theta, index[depth], suffix, n, width, b)
            suffix = suffix.index_select(1, index[depth])
    total = total.view(2, n, width, b)
    return (total * total).sum(dim=(0, 1, 3)) / (n * b)


def run(args):
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    torch.manual_seed(args.seed)
    generator = torch.Generator(device=device)
    generator.manual_seed(args.seed)
    torch.backends.cuda.matmul.allow_tf32 = bool(args.tf32)

    packet = Packet(args.npz, args.k, device, set(args.packet.split(",")),
                    args.word_batch)
    n = packet.n
    # A word that is NOT already trivial at U = I contributes an O(1) term to
    # its own defect, not an O(eps^2) one, so it has no quadratic form at the
    # fold and must not sit in the denominator.  The interior separator
    # c_19243 is exactly such a word (defect sqrt(2) at U = I), which is why
    # the local constant below is a statement about the boundary sub-packet.
    trivial = {str(name) for name, flag
               in zip(np.load(args.npz, allow_pickle=True)["names"],
                      np.load(args.npz, allow_pickle=True)["fold_trivial"])
               if bool(flag)}
    dropped = [name for name in packet.names[:packet.packet_words]
               if name not in trivial]
    cov_chunks = sorted({packet.by_position[packet.names.index("cov:a")],
                         packet.by_position[packet.names.index("cov:b")]})
    body_chunks = [index for index, chunk in enumerate(packet.chunks)
                   if all(position < packet.packet_words
                          and packet.names[position] in trivial
                          for position in chunk[0])]

    if args.load_direction:
        theta = torch.load(args.load_direction, map_location=device).float()
    else:
        theta = torch.randn(2, n, n, device=device, generator=generator)
    theta = torch.stack((theta[0] - theta[0].t(), theta[1] + theta[1].t()))
    theta = theta * (math.sqrt(n) / theta.norm())
    theta.requires_grad_(True)

    started = time.time()
    log = open(args.out, "a", buffering=1) if args.out else None

    def emit(record):
        record["elapsed_s"] = round(time.time() - started, 1)
        line = json.dumps(record, sort_keys=True)
        print(line, flush=True)
        if log:
            log.write(line + "\n")

    emit({"event": "start", "n": n, "k": args.k, "packet": args.packet,
          "words": packet.packet_words, "dropped_nontrivial_at_fold": dropped,
          "probes": args.probes,
          "word_batch": args.word_batch, "lr": args.lr,
          "iterations": args.iterations,
          "device": torch.cuda.get_device_name(0)
          if device.type == "cuda" else "cpu"})

    def exact_ratio(probes):
        with torch.no_grad():
            probe = probes_of(n, probes, device, generator)
            body = 0.0
            worst = ("", 0.0)
            count = 0
            for index in body_chunks:
                values = word_forms(packet, packet.chunks[index], theta, probe)
                body += float(values.sum())
                count += int(values.numel())
                position = int(values.argmax())
                if float(values[position]) > worst[1]:
                    worst = (packet.names[packet.chunks[index][0][position]],
                             float(values[position]))
            cov = sum(float(word_forms(packet, packet.chunks[which], theta,
                                       probe).sum()) for which in cov_chunks)
        return body, cov, worst, count

    velocity = None
    picker = np.random.RandomState(args.seed)
    for step in range(1, args.iterations + 1):
        theta.grad = None
        probe = probes_of(n, args.probes, device, generator)
        # several chunks per step: the quotient is a ratio of SUMS over the
        # whole packet, and a one-chunk estimate of a log-ratio is biased
        # toward directions that only one chunk happens to annihilate
        count = min(args.chunks_per_step, len(body_chunks))
        picked = picker.permutation(len(body_chunks))[:count]
        body = sum(word_forms(packet, packet.chunks[body_chunks[which]],
                              theta, probe).sum() for which in picked)
        cov = sum(word_forms(packet, packet.chunks[which], theta, probe).sum()
                  for which in cov_chunks)
        # scale free: log of the quotient, so ||A|| never matters
        loss = torch.log(body + args.floor) - torch.log(cov + args.floor)
        loss.backward()
        with torch.no_grad():
            if velocity is None:
                velocity = torch.zeros_like(theta)
            velocity.mul_(args.momentum).add_(theta.grad)
            size = float(velocity.norm())
            if size > 0.0:
                theta.detach().add_(velocity,
                                    alpha=-args.lr * math.sqrt(n) / size)
            # back to the sphere, and back to skew-Hermitian
            data = theta.detach()
            data.copy_(torch.stack((data[0] - data[0].t(),
                                    data[1] + data[1].t())) * 0.5)
            data.mul_(math.sqrt(n) / float(data.norm()))

        if step % args.report_every == 0:
            emit({"event": "progress", "step": step,
                  "batch_body": float(body.detach()),
                  "batch_cov": float(cov.detach())})
        if args.eval_every and step % args.eval_every == 0:
            body_all, cov_all, worst, count = exact_ratio(args.eval_probes)
            emit({"event": "eval", "step": step, "packet_energy": body_all,
                  "cov_energy": cov_all, "words_in_form": count,
                  "ratio_sum": cov_all / body_all if body_all else float("inf"),
                  "ratio_max": cov_all / worst[1] if worst[1] else float("inf"),
                  "worst_word": worst[0], "worst_word_energy": worst[1]})

    body_all, cov_all, worst, count = exact_ratio(args.final_probes)
    emit({"event": "final", "packet_energy": body_all, "cov_energy": cov_all,
          "words_in_form": count,
          "ratio_sum": cov_all / body_all if body_all else float("inf"),
          "ratio_max": cov_all / worst[1] if worst[1] else float("inf"),
          "worst_word": worst[0], "worst_word_energy": worst[1]})
    if args.save_direction:
        torch.save(theta.detach().cpu().clone(), args.save_direction)
    if log:
        log.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--npz", default="experiments/atlas-asc-packet.npz")
    parser.add_argument("--packet",
                        default="certified,boundary,phase,interior")
    parser.add_argument("--k", type=int, default=1)
    parser.add_argument("--probes", type=int, default=16)
    parser.add_argument("--chunks-per-step", type=int, default=3)
    parser.add_argument("--eval-probes", type=int, default=64)
    parser.add_argument("--final-probes", type=int, default=256)
    parser.add_argument("--word-batch", type=int, default=48)
    parser.add_argument("--iterations", type=int, default=600)
    parser.add_argument("--lr", type=float, default=0.05)
    parser.add_argument("--momentum", type=float, default=0.9)
    parser.add_argument("--floor", type=float, default=1e-12)
    parser.add_argument("--report-every", type=int, default=100)
    parser.add_argument("--eval-every", type=int, default=100)
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--tf32", type=int, default=1)
    parser.add_argument("--out", default="")
    parser.add_argument("--save-direction", default="")
    parser.add_argument("--load-direction", default="")
    run(parser.parse_args())


if __name__ == "__main__":
    main()
