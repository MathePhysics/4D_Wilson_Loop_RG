"""Where along a loop does the fluctuation energy sit?  Link-by-link E_f and the energy excess at each corner.

E_f = J^T Gamma J is a sum over the links of the loop of c_l = J_l (Gamma J)_l.  Far from a corner c_l approaches a plateau
(about alpha = 0.17), and near a corner it is lower.  With alpha taken from the fit of `corner_locality.py`, the excess
e_l = c_l - alpha summed over the links nearest to a corner is that corner's contribution, and the mean over the corners of a loop
is exactly b (because E_f - alpha P = b c).  Splitting by corner shows whether the corners of one loop contribute equally, and whether a
convex corner (left turn on a counter-clockwise loop) differs from a concave one.  Loops (K = 6, landau):

  sq9      square of side 9 at offset (0,0,0,0) and at (1,1,0,0)
  L9_6     the 9x9 square with a 6x6 corner removed: five convex corners and one concave
  rec6x12  a 6x12 rectangle

A shifted loop has a different edge value (the plateau moves from 0.170 to 0.180), so its corner excess is also given relative to its own edge
value, the mean of c over the links at least three from every corner.  That needs a side longer than six, so it is defined for the squares only.

Numeric only, U(1) analogue, no bound or proof is tested.  Each loop takes about 40 s.

    python3 contour_map.py
    python3 contour_map.py --no-show --save-dir figures
"""
import os
import sys

import numpy as np

import corner_locality as cl
from loop_energy import link_contributions, counts, rect, lshape

LOOPS = {"sq9": (rect(9, 9), (0, 0, 0, 0)), "sq9 shifted (1,1)": (rect(9, 9), (1, 1, 0, 0)),
         "L9_6": (lshape(9, 9, 6, 6), (0, 0, 0, 0)), "rec6x12": (rect(6, 12), (0, 0, 0, 0))}
_CACHE = {}


def corners(steps):
    """Indices i (link i is the first after the turn) of the corners, and the turn direction (+1 left, -1 right) in the plane of axes 0, 1."""
    P = len(steps)
    out = []
    for i in range(P):
        a, b = steps[i - 1], steps[i]
        if a != b:
            va = np.zeros(2); va[a[0]] = a[1]
            vb = np.zeros(2); vb[b[0]] = b[1]
            out.append((i, int(np.sign(va[0] * vb[1] - va[1] * vb[0]))))
    return out


def own_plateau(steps, c, margin=3):
    """Mean of c over the links at least `margin` links from every corner: the loop's own edge value (one period of the block ripple for margin = 3)."""
    P = len(steps)
    idx = np.array([i for i, _ in corners(steps)])
    keep = [l for l in range(P) if np.min(np.abs(((l + 0.5 - idx + P / 2) % P) - P / 2)) >= margin + 0.5]
    return float(np.mean([c[l] for l in keep])) if keep else None


def corner_excess(steps, c, alpha):
    """Excess c_l - alpha summed over the links whose nearest corner (along the loop) is each corner.  Returns [(corner index, turn, excess)].
    alpha is the edge value to subtract: the fitted alpha, or the loop's own plateau (`own_plateau`) when the placement shifts it."""
    P = len(steps)
    cs = corners(steps)
    idx = np.array([i for i, _ in cs])
    ex = np.zeros(len(cs))
    for l in range(P):
        # distance along the loop from link l (centre l + 1/2) to the corner point i (between links i-1 and i)
        d = np.abs(((l + 0.5 - idx + P / 2) % P) - P / 2)
        ex[np.argmin(d)] += c[l] - alpha
    return [(i, t, float(e)) for (i, t), e in zip(cs, ex)]


def run():
    if "r" not in _CACHE:
        info = cl.run(6)
        a, b, _ = cl.thick_fit(info)
        res = {}
        for name, (steps, start) in LOOPS.items():
            E, c = link_contributions((steps, start), 6)
            pl = own_plateau(steps, c)
            res[name] = dict(E=E, c=c, steps=steps, start=start, corners=corner_excess(steps, c, a), plateau=pl,
                             corners_own=corner_excess(steps, c, pl) if pl is not None else None)
        _CACHE["r"] = (a, b, res)
    return _CACHE["r"]


def path(steps, start=(0, 0, 0, 0)):
    """Mid-points (in the plane of axes 0, 1) of the links of a planar loop, in order."""
    p = np.array(start[:2], dtype=float)
    mids = []
    for ax, sg in steps:
        q = p.copy()
        q[ax] += sg
        mids.append((p + q) / 2)
        p = q
    return np.array(mids)


def figure(save=None, show=True):
    import matplotlib
    if not show:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    a, b, res = run()
    fig, ax = plt.subplots(1, 3, figsize=(15, 4.6))
    for name, col in (("sq9", "tab:blue"), ("sq9 shifted (1,1)", "tab:red")):
        ax[0].plot(res[name]["c"], "o-", ms=3, color=col, label=name)
    ax[0].axhline(a, color="k", ls="--", lw=0.8, label="alpha = %.4f" % a)
    ax[0].set_xlabel("link along the loop (counter-clockwise from the origin)")
    ax[0].set_ylabel("c_l = J_l (Gamma J)_l")
    ax[0].set_title("square of side 9: contribution of each link", fontsize=9)
    ax[0].legend(fontsize=7)
    r = res["L9_6"]
    m = path(r["steps"])
    segs = []
    for i, (axn, sg) in enumerate(r["steps"]):
        p0 = m[i].copy(); p0[axn] -= 0.5; p1 = m[i].copy(); p1[axn] += 0.5
        segs.append([p0, p1])
    from matplotlib.collections import LineCollection
    lc = LineCollection(segs, array=r["c"] - a, cmap="coolwarm", linewidths=5)
    lc.set_clim(-0.03, 0.03)
    ax[1].add_collection(lc)
    ax[1].autoscale()
    ax[1].set_aspect("equal")
    for i, t, e in r["corners"]:
        ax[1].annotate("%+.3f" % e, m[i] + (0.0, 0.0), fontsize=8, ha="center", va="center", color="k",
                       bbox=dict(boxstyle="round", fc="w", ec="0.5", alpha=0.8))
    fig.colorbar(lc, ax=ax[1], label="c_l - alpha")
    ax[1].set_title("L9_6: excess near each corner (convex: %d, concave: %d)" % (
        sum(1 for _, t, _ in r["corners"] if t > 0), sum(1 for _, t, _ in r["corners"] if t < 0)), fontsize=9)
    xs, vals, cols, labs = [], [], [], []
    for name, rr in res.items():
        for i, t, e in (rr["corners_own"] if "shifted" in name else rr["corners"]):
            vals.append(e); cols.append("tab:blue" if t > 0 else "tab:orange"); labs.append(name)
    ax[2].scatter(range(len(vals)), vals, c=cols)
    ax[2].axhline(b, color="k", ls="--", lw=0.8, label="b = %.4f (mean per corner in the fit)" % b)
    ax[2].set_xticks([sum(len(rr["corners"]) for rr in list(res.values())[:k]) + len(rr["corners"]) / 2 - 0.5 for k, rr in enumerate(res.values())])
    ax[2].set_xticklabels(list(res), fontsize=7, rotation=20)
    ax[2].set_ylabel("excess energy per corner")
    ax[2].set_title("excess per corner (blue convex, orange concave); the shifted square is measured from its own edge value", fontsize=7)
    ax[2].legend(fontsize=7)
    fig.tight_layout()
    if save:
        os.makedirs(os.path.dirname(save) or ".", exist_ok=True)
        fig.savefig(save, dpi=150)
        print("saved", save)
    if show:
        plt.show()
    plt.close(fig)


def main(argv):
    a, b, res = run()
    print("alpha = %.4f, b = %.4f" % (a, b))
    for name, r in res.items():
        P, c = counts(r["steps"])
        print("%-18s E = %.5f  (alpha P + b c = %.5f)  plateau (middle link of the longest side) %.4f" % (name, r["E"], a * P + b * c, r["c"][len(r["c"]) // 8]))
        print("   corner excess over alpha (link index, turn, excess): " + ", ".join("(%d,%+d,%+.4f)" % x for x in r["corners"]))
        if r["corners_own"] is not None:
            print("   own edge value %.4f; excess over it: " % r["plateau"] + ", ".join("(%d,%+d,%+.4f)" % x for x in r["corners_own"]))
    d = argv[argv.index("--save-dir") + 1] if "--save-dir" in argv else None
    figure(os.path.join(d, "contour_map.png") if d else None, "--no-show" not in argv)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
