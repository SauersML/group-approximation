#!/usr/bin/env python3
"""worklist.py <NON_MF_SENTENCE_CENSUS.tsv> <out WORKLIST.md> <tag> <rows tex> <current tex>

Runs ON MSI (census lane).  Every sentence whose status is not formalized /
definition / structural / attribution / provenance, grouped by owner lane.
Owner = label / section / text rules for the 2026-09-11 swarm roster.
"""
import re, sys
from collections import defaultdict
from census_linemap import load

if len(sys.argv) != 6:
    raise SystemExit("usage: worklist.py <census tsv> <out WORKLIST.md> <tag> <rows tex> <current tex>")
src, out, tag, rows_tex, cur_tex = sys.argv[1:6]
lines = load(rows_tex, cur_tex)
DONE = {"formalized", "definition", "structural", "attribution", "provenance"}
rows = []
for line in open(src, encoding="utf-8"):
    if line.startswith("#") or line.startswith("key\t"):
        continue
    p = line.rstrip("\n").split("\t")
    if len(p) < 8:
        continue
    key, ln, section, env, label, status, decls, sentence = p[:8]
    rows.append(dict(key=key, line=int(ln), old=lines.to_old(int(ln)), section=section, env=env, label=label,
                     status=status, decls=decls, sentence=sentence))

# sec:chain-core and Introduction 249-258, new since 45483f699: owners by key, from the lane reports
# notes/nm-swarm/reports/chain-*.md (09-13): chain-core.md S1, chain-words.md, chain-subshift.md S3b, chain-itinerary.md,
# chain-matricial.md, chain-reflection.md, chain-radical.md's key map.  chain-core.md's S2 recurrence goes to hull-euler
# and the section preamble to chain-core (lead ruling 09-13 16:00, roster c48855016).
CHAIN_OWNERS = {k: lane for lane, keys in (
    ("chain-core", "1a88ddc187c0 1d0bcc92a75f 275bedb28f9f 2d1ca8689ac6 549aa93e832f 6011dc411b20 6e533530564d "
                   "752564275a33 8a557cb954fb a1bda19b475a aa429ec8d623 b1a4887c5412 bba38420cf8b d1c3c7f0f3a9 "
                   "d59fc0887768 753b90beed12"),
    ("hull-euler", "49f76a64907a d5af28721656 3ebdab1c418b 0ae6fc9e199c 73bd8ac910aa 3ef2a7cdb9bd c99bf0bdb029"),
    ("chain-words", "078684fc2a60 0941296cf395 2ed7f807a3a6 4aede6d48b4d 533771f4f22d 53fd5ea7d3d0 56b6a80cc911 "
                    "57cd1b63930c 8bf7f40918d5 9bc3873fb872 b94a006ee638 dfc6d4510272"),
    ("chain-subshift", "048953d87f92 1d52a79f1fef 4fc54b29a740 647f44a95b8a 758517bf8d56 854ec7cb0423 9c49a2efb0ca "
                       "9ea50b0ff631 a08f25fce44c ae9c3d8b9922 b39310f67614 cbf45b0e1c51 d8f8d764406c ded9e9646e4b "
                       "f7c8d8aab016 ffa61d258258"),
    ("chain-itinerary", "042966c81c7e 2583cbd0c0f2 2df08eeac3cb 3b218f92cd81 3d8a2204752a 4bb19e581840 807793f12a5e "
                        "8921296d639a b180421b55ab c825bc73828a d8e1a694d87c e6626f95fede ed348643e2ad fb195144e5c2 "
                        "fe2bd83087c0"),
    ("chain-matricial", "1687471008a1 1d0f9a56866c 2546c17d9884 2a63696d979b 34e1eeff13be 4244fb3c658b 46f3810145ee "
                        "5079b22a3633 741b64286b55 7ff20576d4cf 910136e6e66d 97e43ae93d14 a3598c08b42c c05b0ec8b821 "
                        "cd20a742dd3c d01cbef361ce e55132ef58f5 e60c16639f70 eda117e756e6 f0c16e5c8519 f5264e48f943 "
                        "fd026a61f84f ff376e50f433"),
    ("chain-reflection", "30a44485e5e8 400dde0dbd9d 42c043ef7ab5 43afa4ee3f10 5a62e295ac1a 715cbd0f3410 8981cd70915a "
                         "9dae685e37b9 b23e0f5197b5 cfbacaa0fffa d74779471003 f2baa4a46f78 350e53c0b888"),
    ("chain-radical", "0b84b12a0927 1dcedf0a7a5c 2416b0e3e06b 380bfb5990c5 3a5ab131efde 3b9dae111508 4c62dd1963db "
                      "5ab74e7c4576 5bdc96184b03 684721560ced 71da342a2cec 87cd8b50757e 8ada929ece30 8ffeafc81808 "
                      "a47d16c7fbe5 aac4a95b387b aef6776a7348 be106727feb1 c13ca7c28028 c6f8fb6abe29 d2d559dae75f "
                      "d6d4c3f1cdb5 fd54e2645afe ffcebac26044"),
    # Introduction 249 and tex 1541-1807, new since 73a84cd9c: ct-sentences.md's ledger (fa3546db4), key -> owner.
    ("chain-core", "307b3272f639"),
    ("chain-radical", "7cb6740cda5d 518c40eb5865 ccfc792cc48b 521214409259 e94a545b030a 84bacecbfa4c cc05d5f6226c "
                      "0c22aa9f1005 2b6b9904f2d6 a1d5cde2c840 7e27335fac44 646debe8463c"),
    ("chain-reflection+ct-bilateral-mf", "c890294ad9b0"),
    ("ct-bilateral-cell", "331807e9e898 b98536a82318 30e2f83b735e 8a69e48d6382 7753d17ede98 9a398d134788 732be542bd63 "
                          "f60fa6d3b787 4a343ef108b1 0fa967251251 4a0223a24da4 4f649a2dcbfa 15fba9954989 10fe7a237145"),
    ("ct-bilateral-mf", "1baaaaa0fb29 69ef136d809a ca8edac58ba3 cd7908a482b5 e94a87793eb1 3550126258fb 8985ec7b13b2 "
                        "7f55f9a11e5a 512b53c80bd2 0f83142a750a 2016c672dd6a d812630a48ab"),
    ("ct-involution", "a3bd73fe42e9 9eb0c9e85459 d04eb3acd5c8 b13eccd8f0ec c869a1161522 7bfb9f44e634 a434801aeca5 "
                      "ad9e7459d990 07ab0fbe6cfc 3468c60b2946 05241abb9a90 4e4b1729199c 6baf73489057 f7ca9d694948 "
                      "50c5dd41dff4 5c06eec5555b 1c114e2c4209"),
    ("ct-rank-budget", "58fcf9019fc9 34c348ec46b9 36ddcaf60cbb 3ea1fdec31e9 3e7b0d067ef3 6b63a354455d 1cddd9e4b7ba "
                       "7da9f1c6076f 8f8f0c7b59fa d5dcf496d149 e7f732e9cb78 197439992d5d 4c1aa0bcba19 ded50f77e36b "
                       "01623e90c350 7596b825ecdb 49b5df732076"),
    ("ct-rank-two-limit", "f31fa0413ffd 2d5721555dfe dd5ef3eafd48 5e4354e1556b"),
    ("ct-return-tower", "d44d8916b7e9 18794db09df6 0c51973a1e22 6594ce123649 c3d333b41241 32b097ac7fe8 5d45868395fb "
                        "709190a010a1 5a2063e21671 48a7b49cd9cc 215bfbb4bef3 60708f733247 d29d95ef4834 9e22ceae062f "
                        "f1769ba5e51c"),
    ("ct-two-ended", "ce4eb6ceb71b 54044aad03be 9fdbaf282687 fbee156f2d6d 5c75b0bf2db4 9c225384feb2 a7eb8076fde4 "
                     "9ac1eedef5a7 02525ddc3aa4 c8c11f6bb25a dba179ef6f13 fb84c069f1fe"),
) for k in keys.split()}

def owner(r):
    # 2026-09-13 roster ($NM/ROSTER.md).  The roster's L-numbers are lines of the tex before 45483f699, so the rules read
    # r["old"], the census paragraph line (the TSV's line column) carried back by census_linemap; a paragraph only the
    # current tex has is unowned unless CHAIN_OWNERS names its key.  Specific rows first, then the audit lane of the range.
    s, ln, sec, env, lab = r["sentence"], r["old"], r["section"], r["env"], r["label"]
    if r["key"] in CHAIN_OWNERS:
        return CHAIN_OWNERS[r["key"]]
    if ln is None:
        return "unowned (new since 45483f699)"
    if ln < 85 and re.search(r"torsion-free", s):
        return "nm-endpoints"
    if ln < 85:
        return "audit-intro"
    if 185 <= ln <= 189:
        return "sec2-sentences+hs-vanishes"
    if ln in (285, 291):
        return "nm-endpoints"
    if 85 <= ln <= 345:
        return "sec2-sentences"
    if 1120 <= ln <= 1124:
        return "jacobson"
    if 1144 <= ln <= 1148:
        return "jacobson" if re.search(r"complementary", s) else "ghw-assembly"
    if 1250 <= ln <= 1323 or lab == "cor:leavitt-mf-quotient":
        return "leavitt-units"
    if ln in (1629, 1644, 1659):
        return "cite-hull"
    if 1674 <= ln <= 1676:
        return "cite-hull+kh-ejz+nm-endpoints"
    if sec.startswith("A torsion-free") and re.search(r"Fournier-Facio constructs|\[\\S2\]|\{FFF\}|finitely presented infinite simple", s):
        return "simple-group+nm-endpoints"
    if 1637 <= ln <= 1719 and env != "proof":
        return "nm-endpoints"
    if 1621 <= ln <= 1737:
        return "sec5-sentences"
    if sec in ("Origin and authorship", "Acknowledgments"):
        return "census"
    if ln <= 784:
        return "audit-intro"
    if ln <= 1620:
        return "audit-sec3"
    return "audit-sec5"

groups = defaultdict(list)
counts = defaultdict(int)
for r in rows:
    counts[r["status"]] += 1
    if r["status"] not in DONE:
        groups[owner(r)].append(r)
with open(out, "w", encoding="utf-8") as fh:
    fh.write(f"# Non-MF census worklist {tag}\n\n")
    fh.write("Generated by the census lane from the regenerated census join (current tex). ")
    fh.write("Every sentence not graded formalized/definition/structural/attribution/provenance, by owner lane. ")
    fh.write("Owner rules are mechanical (label/section/text; sec:chain-core and its Introduction sentences by key, from the "
             "chain-* lane reports); a lane that finds a row is not its own tells the lead.\n\n")
    fh.write("Line numbers below are lines of the current tex. Row keys: prefer the 12-hex key shown first; a `LINE:<n>` "
             "key numbers the tex before 45483f699 (at a8cc132c8), and the merge carries it to the current tex.\n\n")
    fh.write("| status | sentences |\n| --- | --- |\n")
    for k in sorted(counts, key=lambda k: -counts[k]):
        fh.write(f"| `{k}` | {counts[k]} |\n")
    fh.write(f"| **total** | {len(rows)} |\n\n")
    for lane in sorted(groups):
        fh.write(f"## {lane} ({len(groups[lane])})\n\n")
        for r in sorted(groups[lane], key=lambda r: r["line"]):
            dec = r["decls"] if r["decls"] else "—"
            fh.write(f"* `{r['key']}` line {r['line']} `{r['status']}` {r['label'] or r['env'] or r['section']}: "
                     f"{r['sentence'][:260]}\n  * decls: {dec}\n")
        fh.write("\n")
print("wrote", out, dict(counts))
