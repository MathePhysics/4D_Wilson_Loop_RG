"""Checks for corner_locality.py, width_scan.py, offset_average.py, contour_map.py, gauge_compare.py and L_dependence.py.

    python3 test_corner_locality.py            about 8 minutes (K = 6 torus, 18^4 fine sites)
    python3 test_corner_locality.py --full     adds the full 81-offset study of offset_average.py (about 3 more minutes)

Tolerances were set after seeing the numbers, as noted next to each check.  Needs ../abelian_first_step.
"""
import sys

import numpy as np

import contour_map as cm
import corner_locality as cl
import gauge_compare as gc
import L_dependence as ld
import offset_average as oa
import width_scan as ws
from loop_energy import fit, loo_errors, counts, rect, lshape

PUBLISHED = {"sq3": 1.855780, "sq6": 3.924427, "sq9": 5.970860}      # ../abelian_first_step, landau, K = 10


def run(full=False):
    ok = True

    def check(name, cond, extra=""):
        nonlocal ok
        ok &= bool(cond)
        print("  %-4s %s %s" % ("ok" if cond else "FAIL", name, extra))

    info = cl.run(6)
    E = {n: v["E"] for n, v in info.items()}
    check("squares of side 3, 6, 9 reproduce the published landau values (K = 10) to 2e-3",
          all(abs(E[n] - v) < 2e-3 for n, v in PUBLISHED.items()), "(K = 6: %.5f %.5f %.5f)" % (E["sq3"], E["sq6"], E["sq9"]))
    check("symmetry: the same square in planes (0,1), (0,2), (2,3) has the same energy to 1e-9",
          abs(E["sq3"] - E["sq3_p02"]) < 1e-9 and abs(E["sq3"] - E["sq3_p23"]) < 1e-9)
    check("symmetry: reversing, permuting the axes of, or translating by L = 3 a loop changes nothing (1e-9)",
          max(abs(E["sq6"] - E[k]) for k in ("sq6_rev", "sq6_shiftL", "sq6_perm")) < 1e-9)
    names = list(cl.THICK)
    P = [info[n]["P"] for n in names]
    c = [info[n]["c"] for n in names]
    Ev = [info[n]["E"] for n in names]
    a, b = fit(P, c, Ev)
    loo = abs(loo_errors(P, c, Ev)).max()
    check("locality at offset (0,0,0,0): E = alpha P + b c over 7 loops with every feature >= 6, leave-one-out error below 0.01",
          loo < 0.01, "(max %.4f; alpha %.4f, b %.4f, 4b %.3f)" % (loo, a, b, 4 * b))
    check("alpha and 4b agree with the published square fit (alpha 0.1707 +- 0.001, beta between -0.18 and -0.16)",
          abs(a - 0.1707) < 0.001 and -0.18 < 4 * b < -0.16)
    c_bad = list(c)
    i, j = names.index("sq6"), names.index("L9_6")
    c_bad[i], c_bad[j] = c_bad[j], c_bad[i]
    loo_bad = abs(loo_errors(P, c_bad, Ev)).max()
    check("negative control: giving two loops each other's corner counts breaks the fit (leave-one-out above 0.02)", loo_bad > 0.02,
          "(%.3f)" % loo_bad)
    thin = {n: E[n] - (a * info[n]["P"] + b * info[n]["c"]) for n in cl.THIN}
    thin["sq3"] = E["sq3"] - (a * 12 + b * 4)
    check("a feature one block wide (3 units) sits 0.01 or more below the fit at offset (0,0,0,0)", all(d < -0.01 for d in thin.values()),
          "(%s)" % ", ".join("%s %+.3f" % kv for kv in thin.items()))
    r = ws.run(6)
    dev = {x["w"]: x["dev"] for x in r["rows"]}
    check("width scan, length 12: w = 3 is 0.03 or more below the fit, w = 6 and 9 are within 0.006 of it",
          dev[3] < -0.03 and abs(dev[6]) < 0.006 and abs(dev[9]) < 0.006, "(%s)" % ", ".join("w=%d %+.4f" % kv for kv in dev.items()))
    sub = oa.run(6, ("sq3", "sq6"))["E"]
    sp = {n: (g.max() - g.min(), g.min() == g[0, 0, 0, 0]) for n, g in sub.items()}
    check("position against the blocks: for the squares of side 3 and 6, the offset (0,0,0,0) is the lowest of the 81 and the spread exceeds 0.2",
          all(s > 0.2 and lo for s, lo in sp.values()), "(spread %s)" % ", ".join("%s %.3f" % (n, s) for n, (s, _) in sp.items()))
    check("consistency: the offset-(0,0,0,0) energies agree between the two scripts to 1e-9",
          abs(sub["sq3"][0, 0, 0, 0] - E["sq3"]) < 1e-9 and abs(sub["sq6"][0, 0, 0, 0] - E["sq6"]) < 1e-9)
    a_cm, b_cm, res = cm.run()
    check("link contributions sum to E_f: sum of J_l (Gamma J)_l over the loop equals the energy of corner_locality.py to 1e-9 (square of side 9)",
          abs(res["sq9"]["c"].sum() - E["sq9"]) < 1e-9 and abs(res["sq9"]["E"] - E["sq9"]) < 1e-9)
    check("the mean corner excess over alpha is exactly (E_f - alpha P) / c, for every loop (1e-9)",
          all(abs(np.mean([e for _, _, e in r["corners"]]) - (r["E"] - a_cm * len(r["steps"])) / len(r["corners"])) < 1e-9 for r in res.values()))
    ex = [e for _, _, e in res["sq9"]["corners_own"]]
    check("aligned square of side 9: the four corners have the same excess over the edge value to 0.001", max(ex) - min(ex) < 0.001,
          "(%s)" % ", ".join("%+.4f" % e for e in ex))
    cc = res["L9_6"]["corners"]
    convex = np.mean([e for _, t, e in cc if t > 0])
    concave = [e for _, t, e in cc if t < 0]
    check("L-shape: the concave corner's excess is within 0.005 of the mean convex corner's (one constant for both turns)",
          len(concave) == 1 and abs(concave[0] - convex) < 0.005, "(concave %+.4f, convex mean %+.4f)" % (concave[0], convex))
    sh = res["sq9 shifted (1,1)"]
    exs = [e for _, _, e in sh["corners_own"]]
    check("square shifted by (1,1): its edge value is higher by more than 0.005, and its per-corner excess over that edge value is smaller in size by more than 0.005",
          sh["plateau"] - res["sq9"]["plateau"] > 0.005 and abs(np.mean(ex)) - abs(np.mean(exs)) > 0.005,
          "(edge %.4f vs %.4f; corner %+.4f vs %+.4f)" % (sh["plateau"], res["sq9"]["plateau"], np.mean(exs), np.mean(ex)))
    gi = gc.run(6)
    d_al = max(abs(r["xi1"] - r["landau"]) for n, r in gi.items() if n != "sq9_shift")
    d_sh = abs(gi["sq9_shift"]["xi1"] - gi["sq9_shift"]["landau"])
    check("gauge: xi1 and landau differ by less than 0.001 for every loop at the aligned placement (the published squares: below 6e-4)",
          d_al < 0.001, "(max %.5f)" % d_al)
    check("gauge: the shifted square differs by more than 0.005 (and more than five times the aligned maximum), still below 0.02",
          0.005 < d_sh < 0.02 and d_sh > 5 * d_al, "(%.5f)" % d_sh)
    fg = gc.fits(gi)
    check("gauge: the fitted alpha and b agree between the two gauges to 0.0005",
          abs(fg["landau"]["alpha"] - fg["xi1"]["alpha"]) < 5e-4 and abs(fg["landau"]["b"] - fg["xi1"]["b"]) < 5e-4,
          "(alpha %.4f / %.4f, b %.4f / %.4f)" % (fg["landau"]["alpha"], fg["xi1"]["alpha"], fg["landau"]["b"], fg["xi1"]["b"]))
    tb = ld.table()
    a3, a5 = tb["L3"]["alpha"], tb["L5"]["alpha"]
    check("L dependence (stored L = 5 run, same pair n = 1, 2 at both L): alpha(L=5) exceeds alpha(L=3) by more than 0.02, and |beta| is larger too",
          a5 - a3 > 0.02 and abs(tb["L5"]["beta"]) > abs(tb["L3"]["beta"]), "(alpha %.4f vs %.4f; beta %.3f vs %.3f)" % (a5, a3, tb["L5"]["beta"], tb["L3"]["beta"]))
    check("L dependence: the stored L = 5 energies reproduce alpha, beta by hand (1e-12)",
          abs(a5 - (tb["L5"]["E"][2] - tb["L5"]["E"][1]) / 20) < 1e-12 and abs(tb["L5"]["beta"] - (tb["L5"]["E"][1] - a5 * 20)) < 1e-12)
    if full:
        rows, fits = oa.summary(6)
        f0, fm = fits["at0"], fits["mean"]
        a6, b6 = fit([info[n]["P"] for n in oa.FITSET], [info[n]["c"] for n in oa.FITSET], [info[n]["E"] for n in oa.FITSET])
        check("full study, offset (0,0,0,0): the fit over its six loops equals the one from corner_locality.py over the same six (1e-9)",
              abs(f0["alpha"] - a6) < 1e-9 and abs(f0["b"] - b6) < 1e-9, "(alpha %.4f, b %.4f; the seven-loop fit above is %.4f, %.4f)" % (a6, b6, a, b))
        check("full study, average over 81 offsets: alpha 0.185 to 0.196, 4b between -0.27 and -0.22, leave-one-out below 0.03",
              0.185 < fm["alpha"] < 0.196 and -0.27 < 4 * fm["b"] < -0.22 and fm["loo"] < 0.03,
              "(alpha %.4f, 4b %.3f, loo %.4f)" % (fm["alpha"], 4 * fm["b"], fm["loo"]))
        check("full study: the one-block-wide loops are not below the averaged fit (deviations above -0.005)",
              all(d > -0.005 for d in fm["thin"].values()), "(%s)" % ", ".join("%s %+.3f" % kv for kv in fm["thin"].items()))
        check("full study: the offset (0,0,0,0) is the lowest of the 81 for every loop",
              all(x["at0"] == x["lo"] for x in rows.values()))
    return ok


if __name__ == "__main__":
    print("tests:")
    good = run("--full" in sys.argv)
    print("all tests passed" if good else "TESTS FAILED")
    sys.exit(0 if good else 1)
