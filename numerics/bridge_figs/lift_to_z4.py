"""A Spectre outline written as links of the hypercubic lattice Z^4, and what the abelian first-step energy makes of it.

The lift of `lift4d.py` (spectre-monotile-py) gives each Spectre edge as a step of the red lattice (p, q) or the green lattice (r, s) of Z^4.
Edges along the lattice axes are single links; the other edges of the hexagonal lattice, (1,-1) and (-1,1), need two links (a "diagonal"), which
can be written in two orders.  The tile outline of dilation n is walked n times along each edge.  `../corner_locality` then gives its energy
E_f = J^T Gamma J (K = 6, L = 3, landau, aligned placement) and the energy predicted by perimeter plus corners, alpha P + b c, with (alpha, b)
fitted on the seven thick loops of `corner_locality.THICK`.

  Exact    the two orderings of the diagonals give different closed loops of the same length with different numbers of corners (a corner is a place
           where consecutive links differ).
  Numeric  the lifted outline's energy lies above the additive prediction for every dilation and both orderings, and the two orderings of the same
           outline differ in energy (the numbers are printed; tested).

The reason in each case is that the diagonals become staircases whose corners are one link apart, so corner terms that the fit treats as independent
overlap (the loops of `corner_locality` have corners at least 3 links apart).  This says nothing about a hexagonal action, which the hypercubic
one only imitates; it shows that the hypercubic action cannot be used to read off a corner constant for a Spectre-shaped contour.

    python3 lift_to_z4.py                  about 1 minute (energies)
    python3 lift_to_z4.py --no-energy --no-show --save-dir figures      the geometry only
"""
import os
import sys

import numpy as np

import spectre_path

spectre_path.use()
import lift4d  # noqa: E402

sys.path.insert(0, os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "corner_locality"))
import corner_locality as cl  # noqa: E402
from loop_energy import energies, fit, counts  # noqa: E402

LOOPS = [("n=1 first", 1, "first"), ("n=1 second", 1, "second"), ("n=2 first", 2, "first"), ("n=2 second", 2, "second"), ("n=3 first", 3, "first")]


def steps(n=1, order="first", tile=0):
    """Unit steps (axis, sign) of the lifted outline of one tile, each edge walked n times.  A diagonal edge (two non-zero coordinates) is two links,
    in order of increasing axis ('first') or decreasing ('second')."""
    t = lift4d.lift_patch(0)[0][tile]
    out = []
    for i in range(len(t)):
        d = np.array(t[(i + 1) % len(t)]) - np.array(t[i])
        ax = [(k, int(np.sign(d[k]))) for k in range(4) if d[k] != 0]
        if order == "second":
            ax = ax[::-1]
        for _ in range(n):
            out += ax
    return out


def vertices(st):
    """Positions (in Z^4) visited by a loop of steps, starting at the origin."""
    p = np.zeros(4, dtype=int)
    out = [p.copy()]
    for ax, sg in st:
        p[ax] += sg
        out.append(p.copy())
    return np.array(out)


_CACHE = {}


def run():
    """({name: dict(P, c, E, pred, dev)}, (alpha, b)); computed once (about 40 s)."""
    if "r" in _CACHE:
        return _CACHE["r"]
    names = list(cl.THICK)
    items = [cl.THICK[n] for n in names] + [steps(n, o) for _, n, o in LOOPS]
    E = energies(items, 6)
    P = [counts(cl.THICK[n])[0] for n in names]
    c = [counts(cl.THICK[n])[1] for n in names]
    a, b = fit(P, c, E[:len(names)])
    res = {}
    for (name, n, o), e in zip(LOOPS, E[len(names):]):
        Pn, cn = counts(steps(n, o))
        res[name] = dict(P=Pn, c=cn, E=float(e), pred=float(a * Pn + b * cn), dev=float(e - (a * Pn + b * cn)))
    _CACHE["r"] = (res, (a, b))
    return _CACHE["r"]


def figure(save=None, show=True, energy=True):
    import matplotlib
    if not show:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    ncol = 3 if energy else 2
    fig, ax = plt.subplots(1, ncol, figsize=(5 * ncol, 4.8))
    for k, (order, col) in enumerate((("first", "tab:blue"), ("second", "tab:red"))):
        st = steps(1, order)
        v = vertices(st)
        off = 0.04 * (k - 0.5)
        ax[0].plot(v[:, 0] + off, v[:, 1] + off, "-o", color=col, ms=3, lw=1.2,
                   label="%s order: %d links, %d corners" % (order, *counts(st)))
        ax[1].plot(v[:, 2] + off, v[:, 3] + off, "-o", color=col, ms=3, lw=1.2)
    ax[0].set_title("red part: projection to (p, q)", fontsize=9)
    ax[1].set_title("green part: projection to (r, s)", fontsize=9)
    for a_ in ax[:2]:
        a_.set_aspect("equal")
        a_.grid(alpha=0.3)
    ax[0].legend(fontsize=7, loc="upper center", bbox_to_anchor=(0.5, -0.08))
    if energy:
        res, (a, b) = run()
        names = list(res)
        ax[2].bar(range(len(names)), [res[n]["dev"] for n in names], color=["tab:blue" if "first" in n else "tab:red" for n in names])
        ax[2].set_xticks(range(len(names)))
        ax[2].set_xticklabels(names, rotation=30, fontsize=8)
        ax[2].axhspan(-0.006, 0.006, color="0.85")
        ax[2].axhline(0, color="k", lw=0.7)
        ax[2].set_ylabel("E_f - (alpha P + b c)")
        ax[2].set_title("above the additive prediction (alpha %.4f, b %.4f); grey: fit scatter" % (a, b), fontsize=8)
    fig.tight_layout()
    if save:
        os.makedirs(os.path.dirname(save) or ".", exist_ok=True)
        fig.savefig(save, dpi=150)
        print("saved", save)
    if show:
        plt.show()
    plt.close(fig)


def main(argv):
    energy = "--no-energy" not in argv
    for order in ("first", "second"):
        st = steps(1, order)
        print("n=1 %-6s P = %d, corners = %d" % (order, *counts(st)))
    if energy:
        res, (a, b) = run()
        print("fit on the thick loops: alpha %.4f, b %.4f" % (a, b))
        for n, r in res.items():
            print("%-11s P %3d c %2d  E_f %.4f  predicted %.4f  deviation %+.3f" % (n, r["P"], r["c"], r["E"], r["pred"], r["dev"]))
    d = argv[argv.index("--save-dir") + 1] if "--save-dir" in argv else None
    figure(os.path.join(d, "lift_to_z4.png") if d else None, "--no-show" not in argv, energy)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
