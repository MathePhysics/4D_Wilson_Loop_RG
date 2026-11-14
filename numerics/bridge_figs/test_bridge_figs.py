"""Checks for spectre_contour_corners.py, lift_to_z4.py and scope_map.py.

    python3 test_bridge_figs.py               about 1 minute (the energies of lift_to_z4 take most of it)
    python3 test_bridge_figs.py --no-energy   geometry and parsing only, a few seconds

Needs the clone of spectre-monotile-py (`make install` in the repository root).  Tolerances were set after seeing the numbers where noted.
"""
import collections
import sys

import numpy as np

import lift_to_z4 as lz
import scope_map as sm
import spectre_contour_corners as sc


def run(energy=True):
    ok = True

    def check(name, cond, extra=""):
        nonlocal ok
        ok &= bool(cond)
        print("  %-4s %s %s" % ("ok" if cond else "FAIL", name, extra))

    tiles = sc.patch_tiles(2)
    cs = [sc.classify(t) for t in tiles]
    want = collections.Counter({60: 7, 90: 6, 0: 1})
    check("all %d tiles of the level-2 patch have 14 edges and corners 7 x 60 deg, 6 x 90 deg, 1 straight" % len(tiles),
          len(tiles) == 71 and all(len(c["pts"]) == 14 and c["by_turn"] == want for c in cs))
    split = collections.Counter((c["n_red"], c["n_green"]) for c in cs)
    check("edge colours: 8 red + 6 green for 63 tiles, 6 red + 8 green for the other 8", dict(split) == {(8, 6): 63, (6, 8): 8}, "(%s)" % dict(split))
    mixed = collections.Counter()
    for c in cs:
        for (m, t), k in c["mixed_and_turn"].items():
            mixed[(m, t)] += k
    check("a red-green corner is always a 90 degree turn; a same-colour corner is 60 degrees or straight",
          all((t == 90) == m for (m, t) in mixed) and mixed[(True, 90)] == 6 * 71, "(%s)" % dict(mixed))
    check("negative control: a regular hexagon of the red lattice is classified as six turns of 60 degrees, not as a Spectre outline",
          sc.classify(_hexagon())["by_turn"] == collections.Counter({60: 6}) and sc.classify(_hexagon())["by_turn"] != want)
    st1, st2 = lz.steps(1, "first"), lz.steps(1, "second")
    check("lifted outline: both orderings are closed loops of 18 links in Z^4",
          len(st1) == len(st2) == 18 and not np.any(lz.vertices(st1)[-1]) and not np.any(lz.vertices(st2)[-1]))
    check("the two orderings give different loops with 13 and 17 corners", lz.counts(st1)[1] == 13 and lz.counts(st2)[1] == 17,
          "(%d, %d)" % (lz.counts(st1)[1], lz.counts(st2)[1]))
    rows = sm.label_counts()
    check("STATUS_MAP.md label table parses: at least 5 labels, positive counts, in non-increasing order",
          len(rows) >= 5 and all(c > 0 for _, c in rows) and all(rows[i][1] >= rows[i + 1][1] for i in range(len(rows) - 1)),
          "(%d labels, %d rows)" % (len(rows), sum(c for _, c in rows)))
    if energy:
        res, (a, b) = lz.run()
        dev = {n: r["dev"] for n, r in res.items()}
        check("energy: the lifted outline is above the additive prediction by more than 0.2 for every dilation and ordering", all(d > 0.2 for d in dev.values()),
              "(%s)" % ", ".join("%s %+.2f" % kv for kv in dev.items()))
        check("energy: the two orderings of the same outline differ in E_f by more than 0.1", abs(res["n=1 first"]["E"] - res["n=1 second"]["E"]) > 0.1,
              "(%.3f vs %.3f)" % (res["n=1 first"]["E"], res["n=1 second"]["E"]))
    return ok


def _hexagon():
    """A regular hexagon of the red lattice (unit edges at 0, 60, ..., 300 degrees) as a vertex list in the format lift4d produces."""
    return [(0, 0, 0, 0), (1, 0, 0, 0), (1, 1, 0, 0), (0, 2, 0, 0), (-1, 2, 0, 0), (-1, 1, 0, 0)]


if __name__ == "__main__":
    print("tests:")
    good = run("--no-energy" not in sys.argv)
    print("all tests passed" if good else "TESTS FAILED")
    sys.exit(0 if good else 1)
