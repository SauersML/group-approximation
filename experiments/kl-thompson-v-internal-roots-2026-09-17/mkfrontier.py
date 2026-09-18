import sys
REPO = "/home/user/group-approximation/.claude/worktrees/wf_3d1462e3-356-7/"
retract = {l.split()[0] for l in open(REPO + "experiments/kl-thompson-v-census/retract_certificates.txt")}
weight = {l.split()[0] for l in open(REPO + "experiments/kl-violating-equation-over-thompson-v-2026-09-16/weight_certificates.txt") if l.strip()}
meta = {}
for l in open("survivors67.txt"):
    p = l.split()
    meta[p[0]] = (p[2], p[3])
f1 = open("frontier.txt", "w")
f2 = open("frontier_after_weight.txt", "w")
n1 = n2 = 0
for l in open("theorems_out.txt"):
    p = l.split()
    if p[2] != "FRONTIER" or p[0] in retract:
        continue
    f1.write("%s %s %s %s\n" % (p[0], p[1], *meta[p[0]]))
    n1 += 1
    if p[0] not in weight:
        f2.write("%s %s %s %s\n" % (p[0], p[1], *meta[p[0]]))
        n2 += 1
print(n1, n2, len(weight))
