"""How much do the coefficients depend on the gauge condition?  Landau against xi = 1, for loops other than squares and for a shifted loop.

`../abelian_first_step` reports that the xi1 condition changes the energy of squares by less than 6e-4 at the usual placement.  This
script repeats the comparison for the loops of `corner_locality` (rectangles, L-shapes, loops spanning three directions, thin loops)
and for the square of side 9 shifted by (1,1,0,0), where the placement moved the energy by 0.4, and refits (alpha, b) in each gauge.
Numeric, U(1) analogue, K = 6.  No bound or proof is tested.

    python3 gauge_compare.py             about 2 minutes
    python3 gauge_compare.py --no-show --save-dir figures
"""
import os
import sys

import numpy as np

import corner_locality as cl
from loop_energy import energies, fit, loo_errors, counts, rect

SHIFTED = (rect(9, 9), (1, 1, 0, 0))
_CACHE = {}


def run(K=6):
    if K not in _CACHE:
        names = list(cl.THICK) + list(cl.THIN) + ["sq9_shift"]
        loops = [cl.THICK[n] for n in cl.THICK] + [cl.THIN[n] for n in cl.THIN] + [SHIFTED]
        out = {}
        for g in ("landau", "xi1"):
            out[g] = dict(zip(names, energies(loops, K, g)))
        info = {}
        for n, lp in zip(names, loops):
            steps = lp[0] if isinstance(lp[0], list) else lp
            P, c = counts(steps)
            info[n] = dict(P=P, c=c, landau=float(out["landau"][n]), xi1=float(out["xi1"][n]))
        _CACHE[K] = info
    return _CACHE[K]


def fits(info):
    res = {}
    names = list(cl.THICK)
    for g in ("landau", "xi1"):
        P = [info[n]["P"] for n in names]
        c = [info[n]["c"] for n in names]
        E = [info[n][g] for n in names]
        a, b = fit(P, c, E)
        res[g] = dict(alpha=a, b=b, loo=float(abs(loo_errors(P, c, E)).max()))
    return res


def figure(save=None, show=True):
    import matplotlib
    if not show:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    info = run()
    names = list(info)
    d = [info[n]["xi1"] - info[n]["landau"] for n in names]
    fig, ax = plt.subplots(figsize=(8, 4.2))
    ax.bar(range(len(names)), d, color=["tab:blue" if n in cl.THICK else "tab:orange" if n in cl.THIN else "tab:red" for n in names])
    ax.set_xticks(range(len(names)))
    ax.set_xticklabels(names, rotation=75, fontsize=7)
    ax.axhline(0, color="k", lw=0.7)
    ax.set_ylabel("E_f(xi1) - E_f(landau)")
    ax.set_title("gauge dependence of E_f (K = 6; the published squares: below 6e-4)", fontsize=9)
    fig.tight_layout()
    if save:
        os.makedirs(os.path.dirname(save) or ".", exist_ok=True)
        fig.savefig(save, dpi=150)
        print("saved", save)
    if show:
        plt.show()
    plt.close(fig)


def main(argv):
    info = run()
    print("%-10s %4s %2s %10s %10s %10s" % ("loop", "P", "c", "landau", "xi1", "xi1-landau"))
    for n, r in info.items():
        print("%-10s %4d %2d %10.5f %10.5f %+10.5f" % (n, r["P"], r["c"], r["landau"], r["xi1"], r["xi1"] - r["landau"]))
    for g, f in fits(info).items():
        print("%-7s fit on the seven thick loops: alpha %.4f  b %.4f  4b %.3f  max leave-one-out %.4f" % (g, f["alpha"], f["b"], 4 * f["b"], f["loo"]))
    d = argv[argv.index("--save-dir") + 1] if "--save-dir" in argv else None
    figure(os.path.join(d, "gauge_compare.png") if d else None, "--no-show" not in argv)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
