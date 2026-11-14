"""How much of E_f is the position of the loop against the L = 3 blocks?  (plan item P3)

The coarse lattice has period L = 3, so a loop translated by 3 has the same energy (tested), but a translation by 1 or 2 does not
in general.  Each loop is placed at all 81 offsets (dx, dy, dz, dw) in {0,1,2}^4, in-plane and transverse, and the energy is computed
for each.  Printed: the spread over offsets for each loop, the offset-averaged energy, and the refit E = alpha P + b c over the loops with
every feature >= 6, once for the offset (0,0,0,0) used by the published square fits and once for the average over all 81.

Reading the result.  The spread is the block-periodic ripple that the published square fits (alpha = 0.1707, beta between -0.17 and -0.18)
carry as their uncertainty; the offset average removes it, and the refitted b says how much of the corner constant it moved.  Numeric,
U(1) analogue, K = 6, landau gauge.  No bound or proof is tested.

    python3 offset_average.py                  a few minutes
    python3 offset_average.py --no-show --save-dir figures
"""
import itertools
import os
import sys

import numpy as np

from loop_energy import energies, fit, loo_errors, counts, rect, lshape, skew

LOOPS = {"sq3": rect(3, 3), "rec3x9": rect(3, 9), "sq6": rect(6, 6), "sq9": rect(9, 9), "rec6x9": rect(6, 9), "rec6x12": rect(6, 12),
         "L9_6": lshape(9, 9, 6, 6), "skew666": skew(6, 6, 6)}
FITSET = ["sq6", "sq9", "rec6x9", "rec6x12", "L9_6", "skew666"]      # every feature >= 6, as in corner_locality.THICK
THINSET = ["sq3", "rec3x9"]
OFFS = list(itertools.product(range(3), repeat=4))      # all 81 positions modulo the block period in every direction
_CACHE = {}


def run(K=6, names=None):
    """{'E': {name: array of shape (3,3,3,3) over the offset (dx, dy, dz, dw)}}."""
    names = tuple(LOOPS if names is None else names)
    if (K, names) not in _CACHE:
        items, keys = [], []
        for n in names:
            s = LOOPS[n]
            for o in OFFS:
                items.append((s, o))
                keys.append((n, o))
        E = energies(items, K)
        grid = {n: np.zeros((3, 3, 3, 3)) for n in names}
        for (n, o), e in zip(keys, E):
            grid[n][o] = e
        _CACHE[(K, names)] = dict(E=grid)
    return _CACHE[(K, names)]


def summary(K=6):
    r = run(K)
    rows = {}
    for n, g in r["E"].items():
        P, c = counts(LOOPS[n])
        rows[n] = dict(P=P, c=c, mean=float(g.mean()), lo=float(g.min()), hi=float(g.max()), at0=float(g[0, 0, 0, 0]))
    out = {}
    for tag in ("at0", "mean"):
        P = [rows[n]["P"] for n in FITSET]
        c = [rows[n]["c"] for n in FITSET]
        E = [rows[n][tag] for n in FITSET]
        a, b = fit(P, c, E)
        out[tag] = dict(alpha=a, b=b, loo=float(abs(loo_errors(P, c, E)).max()),
                        thin={n: rows[n][tag] - (a * rows[n]["P"] + b * rows[n]["c"]) for n in THINSET})
    return rows, out


def figure(save=None, show=True, K=6):
    import matplotlib
    if not show:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    r = run(K)
    rows, fits = summary(K)
    a_av, b_av, a_0, b_0 = fits['mean']['alpha'], fits['mean']['b'], fits['at0']['alpha'], fits['at0']['b']
    fig, ax = plt.subplots(1, 2, figsize=(12, 4.6))
    names = list(LOOPS)
    for i, n in enumerate(names):
        ax[0].scatter([i] * 81, (r["E"][n] - rows[n]["mean"]).ravel(), color="tab:blue", s=18)
        ax[0].scatter([i], [r["E"][n][0, 0, 0, 0] - rows[n]["mean"]], color="tab:red", s=40, marker="D", zorder=3)
    ax[0].axhline(0, color="k", lw=0.7)
    ax[0].set_xticks(range(len(names)))
    ax[0].set_xticklabels(names)
    ax[0].set_ylabel("E_f at offset - mean over the 81 offsets")
    ax[0].set_title("ripple from the position against the blocks (red: offset (0,0,0,0))", fontsize=9)
    thick = FITSET
    pp = np.linspace(10, 40, 50)
    ax[1].scatter([rows[n]["P"] for n in names], [rows[n]["mean"] for n in names], color="tab:blue", label="offset average")
    ax[1].scatter([rows[n]["P"] for n in names], [rows[n]["at0"] for n in names], color="tab:red", marker="D", s=22, label="offset (0,0,0,0)")
    ax[1].plot(pp, a_av * pp + 4 * b_av, "b--", lw=0.8, label="fit to averages: alpha %.4f, b %.4f" % (a_av, b_av))
    ax[1].plot(pp, a_0 * pp + 4 * b_0, "r:", lw=0.8, label="fit to (0,0): alpha %.4f, b %.4f" % (a_0, b_0))
    ax[1].set_xlabel("number of links P")
    ax[1].set_ylabel("E_f")
    ax[1].set_title("fit set: %s; dashed lines drawn for four corners" % ", ".join(thick), fontsize=7)
    ax[1].legend(fontsize=7)
    fig.tight_layout()
    if save:
        os.makedirs(os.path.dirname(save) or ".", exist_ok=True)
        fig.savefig(save, dpi=150)
        print("saved", save)
    if show:
        plt.show()
    plt.close(fig)


def main(argv):
    rows, fits = summary()
    r = run()
    print("%-8s %3s %2s %9s %9s %9s %9s" % ("loop", "P", "c", "E(0,0)", "mean", "min", "max"))
    for n, x in rows.items():
        print("%-8s %3d %2d %9.5f %9.5f %9.5f %9.5f   spread %.4f" % (n, x["P"], x["c"], x["at0"], x["mean"], x["lo"], x["hi"], x["hi"] - x["lo"]))
    for tag, name in (("at0", "offset (0,0)"), ("mean", "offset average")):
        f = fits[tag]
        print("fit on %d loops, %-14s alpha %.4f  b %.4f (4b %.3f)  max leave-one-out %.4f   one-block-wide loops: %s"
              % (len(FITSET), name, f["alpha"], f["b"], 4 * f["b"], f["loo"], ", ".join("%s %+.3f" % kv for kv in f["thin"].items())))
        d = argv[argv.index("--save-dir") + 1] if "--save-dir" in argv else None
    figure(os.path.join(d, "offset_average.png") if d else None, "--no-show" not in argv)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
