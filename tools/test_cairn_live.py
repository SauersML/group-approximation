"""Tests for tools/cairn_live.py: the log, the fold, the diversity rule and merging.

Run: python3 -m unittest tools/test_cairn_live.py
"""

import contextlib
import io
import json
import multiprocessing
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cairn_live as live  # noqa: E402

NODE = "some-test-node"


def run(agent, *argv):
    os.environ["CAIRN_AGENT"] = agent
    err, out = io.StringIO(), io.StringIO()
    with contextlib.redirect_stderr(err), contextlib.redirect_stdout(out):
        try:
            code = live.main(list(argv))
        except SystemExit as e:
            code = e.code if isinstance(e.code, int) else 1
    return code, out.getvalue() + err.getvalue()


def _claim_worker(args):
    live_dir, i = args
    os.environ["CAIRN_LIVE"] = live_dir
    os.environ["CAIRN_WAVE"] = "t"
    code, _ = run(f"w{i}", "claim", NODE, "--new", "--family", "local-designs",
                  "--sig", "spare track annulus gadget")
    return code


class LiveTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        os.environ["CAIRN_LIVE"] = self.tmp.name
        os.environ["CAIRN_WAVE"] = "t"

    def tearDown(self):
        self.tmp.cleanup()

    def claim(self, agent, sig, family="local-designs", *extra):
        return run(agent, "claim", NODE, "--new", "--family", family, "--sig", sig, *extra)

    def test_same_idea_is_blocked(self):
        self.assertEqual(self.claim("a", "spare track annulus gadget")[0], 0)
        code, text = self.claim("b", "annulus gadget with spare track", "census-computation")
        self.assertEqual(code, live.EXIT_BLOCKED)
        self.assertIn("same idea", text)

    def test_same_family_needs_a_reason(self):
        self.claim("a", "spare track annulus gadget")
        self.assertEqual(self.claim("b", "shear swindle band")[0], live.EXIT_BLOCKED)
        self.assertEqual(self.claim("b", "shear swindle band", "local-designs",
                                    "--same-family", "different gadget")[0], 0)
        self.assertEqual(self.claim("c", "entropy compression", "entropy-measure")[0], 0)

    def test_dead_idea_needs_revive(self):
        self.claim("a", "spare track annulus gadget")
        self.assertEqual(run("a", "dead", NODE, "--text", "one track short")[0], 0)
        state = live.fold(live.read_events())
        self.assertEqual(len(state["leases"]), 0)
        self.assertEqual(state["dead"][0]["sig"], "spare track annulus gadget")
        self.assertEqual(self.claim("b", "spare track annulus gadget")[0], live.EXIT_BLOCKED)
        self.assertEqual(self.claim("b", "spare track annulus gadget", "local-designs",
                                    "--revive", "new count")[0], 0)

    def test_release_frees_the_approach(self):
        self.claim("a", "spare track annulus gadget")
        run("a", "release", NODE)
        state = live.fold(live.read_events())
        self.assertEqual(len(state["leases"]), 0)
        self.assertEqual(len(state["done"]), 1)
        self.assertEqual(self.claim("b", "spare track annulus gadget")[0], 0)

    def test_expiry_and_heartbeat(self):
        self.claim("a", "spare track annulus gadget", "local-designs", "--ttl", "100")
        events = live.read_events()
        t0 = events[0]["ts"]
        self.assertEqual(len(live.fold(events, now=t0 + 150)["leases"]), 0)
        run("a", "heartbeat", "--node", NODE, "--text", "counted the annulus")
        events = live.read_events()
        beat = events[-1]["ts"]
        state = live.fold(events, now=beat + 50)
        self.assertEqual(len(state["leases"]), 1)
        self.assertEqual(next(iter(state["leases"].values()))["progress"], "counted the annulus")

    def test_feed_new_skips_own_and_advances(self):
        self.claim("a", "spare track annulus gadget")
        run("b", "spark", "--text", "groupoid version")
        code, text = run("a", "feed", "--new")
        self.assertIn("groupoid version", text)
        self.assertNotIn("CLAIM", text)
        self.assertIn("nothing new", run("a", "feed", "--new")[1])

    def test_adopting_a_spark_closes_it(self):
        run("b", "spark", "--text", "groupoid version")
        spark = live.read_events()[-1]["id"]
        self.assertEqual(len(live.fold(live.read_events())["sparks"]), 1)
        self.claim("a", "groupoid reframing", "local-designs", "--adopt", spark)
        self.assertEqual(len(live.fold(live.read_events())["sparks"]), 0)

    def test_merge_is_a_union_by_id(self):
        run("a", "note", "--text", "one")
        run("a", "note", "--text", "two")
        path = os.path.join(self.tmp.name, "x.jsonl")
        run("a", "export", path)
        with open(path, "a") as f:
            f.write('{"torn": \n')
            f.write(json.dumps({"id": "ext1", "ts": 1.0, "agent": "z", "wave": "t",
                                "kind": "note", "text": "remote"}) + "\n")
        self.assertIn("imported 1 new", run("a", "import", path)[1])
        self.assertIn("imported 0 new", run("a", "import", path)[1])
        self.assertEqual(len(live.read_events()), 3)

    def test_usage_errors_exit_64(self):
        self.assertEqual(run("a", "no-such-command")[0], live.EXIT_USAGE)
        self.assertEqual(run("", "claim", NODE, "--new", "--family", "local-designs",
                             "--sig", "x y z")[0], live.EXIT_USAGE)

    def test_concurrent_claims_in_two_containers_fold_to_one_winner(self):
        a, b = os.path.join(self.tmp.name, "a"), os.path.join(self.tmp.name, "b")
        os.environ["CAIRN_LIVE"] = a
        self.claim("w1", "spare track annulus gadget")
        os.environ["CAIRN_LIVE"] = b
        self.claim("w2", "annulus gadget spare track")  # admitted locally: b has not seen a
        first = live.read_events(os.path.join(a, "events.jsonl"))
        second = live.read_events(os.path.join(b, "events.jsonl"))
        live.merge_events(first)
        os.environ["CAIRN_LIVE"] = a
        live.merge_events(second)
        for d in (a, b):
            state = live.fold(live.read_events(os.path.join(d, "events.jsonl")))
            self.assertEqual([x["agent"] for x in state["leases"].values()], ["w1"])
            self.assertEqual([x["agent"] for x in state["rejected"].values()], ["w2"])

    def test_auto_sync_through_a_git_ref(self):
        import subprocess
        bare, repo = os.path.join(self.tmp.name, "bare.git"), os.path.join(self.tmp.name, "repo")
        subprocess.run(["git", "init", "-q", "--bare", bare], check=True)
        subprocess.run(["git", "init", "-q", repo], check=True)
        old_root = live.ROOT
        live.ROOT = repo
        os.environ.update(CAIRN_LIVE_SYNC=bare, CAIRN_LIVE_PULL_EVERY="0",
                          GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
                          GIT_COMMITTER_EMAIL="t@t")
        try:
            os.environ["CAIRN_LIVE"] = os.path.join(self.tmp.name, "a")
            self.assertEqual(self.claim("w1", "spare track annulus gadget")[0], 0)
            os.environ["CAIRN_LIVE"] = os.path.join(self.tmp.name, "b")
            code, text = self.claim("w2", "annulus gadget spare track")
            self.assertEqual(code, live.EXIT_BLOCKED)
            self.assertIn("same idea", text)
            run("w2", "spark", "--text", "groupoid version")
            os.environ["CAIRN_LIVE"] = os.path.join(self.tmp.name, "a")
            self.assertIn("groupoid version", run("w1", "feed", "--new")[1])
        finally:
            live.ROOT = old_root
            for k in ("CAIRN_LIVE_SYNC", "CAIRN_LIVE_PULL_EVERY"):
                os.environ.pop(k, None)

    def test_concurrent_claims_admit_one(self):
        with multiprocessing.get_context("fork").Pool(8) as pool:
            codes = pool.map(_claim_worker, [(self.tmp.name, i) for i in range(16)])
        self.assertEqual(codes.count(0), 1, codes)
        self.assertEqual(codes.count(live.EXIT_BLOCKED), 15, codes)
        self.assertEqual(len(live.read_events()), 1)


if __name__ == "__main__":
    unittest.main()
