"""The corner types of a Spectre outline, on the hexagonal lattice.

Every edge of the Spectre is a unit vector at a multiple of 30 degrees; `lift4d.py` of spectre-monotile-py writes each as a step of a red
hexagonal lattice (even multiples) or a green one (odd multiples).  This script reads one tile and a patch from that module and classifies
the corners of each outline by the geometric turn between consecutive edges:

  Exact   every tile outline has 14 edges and its corners are 7 turns of 60 degrees, 6 of 90 degrees and 1 straight pass: the same for all 71 tiles of
          the patch of level 2 (tested).  The edge colours are 8 red and 6 green for 63 tiles and 6 red and 8 green for the other 8 (a tile turned by an
          odd multiple of 30 degrees swaps the colours), so the colour split is not the same for every tile.
  Exact   a corner between a red and a green edge is always a 90 degree turn; between two edges of the same colour it is 60 degrees or straight.

In the E8 embedding of spectre-monotile-py (`models/spectre_in_e8.py`) the edges are roots and the red-green corners are the pairs with inner
product 0, the same-colour 60 degree corners those with inner product 1; that is not recomputed here.  What matters for the Wilson-loop
programme is the list of corner types a Spectre-shaped contour would have: it contains 60 degree corners, which the hypercubic action of
`../corner_locality` cannot represent (every turn between different axes is 90 degrees there).

    python3 spectre_contour_corners.py
    python3 spectre_contour_corners.py --no-show --save-dir figures
"""
import collections
import math
import os
import sys

import numpy as np

import spectre_path

spectre_path.use()
import lift4d  # noqa: E402


def outline(tile):
    """Corner coordinates (complex), edge directions (multiples of 30 degrees, mod 12), and the turn at each corner in degrees (left positive)."""
    pts = [complex(lift4d.project(np.array(v))) for v in tile]
    n = len(pts)
    dirs = []
    for i in range(n):
        d = pts[(i + 1) % n] - pts[i]
        k = math.degrees(math.atan2(d.imag, d.real)) / 30
        assert abs(k - round(k)) < 1e-6 and abs(abs(d) - 1) < 1e-6
        dirs.append(int(round(k)) % 12)
    turns = [(((dirs[i] - dirs[i - 1] + 6) % 12) - 6) * 30 for i in range(n)]       # turn at corner i, between edge i-1 and edge i
    return pts, dirs, turns


def signed_area(pts):
    return 0.5 * sum((pts[i].conjugate() * pts[(i + 1) % len(pts)]).imag for i in range(len(pts)))


def classify(tile):
    """dict with the edge colours, the corner turn counts by absolute value, and the colour pairs at the corners."""
    pts, dirs, turns = outline(tile)
    red = [d % 2 == 0 for d in dirs]
    pairs = collections.Counter((red[i - 1] != red[i], abs(turns[i])) for i in range(len(pts)))
    return dict(pts=pts, dirs=dirs, turns=turns, red=red, n_red=sum(red), n_green=len(red) - sum(red),
                by_turn=collections.Counter(abs(t) for t in turns), mixed_and_turn=pairs)


def patch_tiles(levels=2):
    return lift4d.lift_patch(levels)[0]


def figure(save=None, show=True):
    import matplotlib
    if not show:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    tiles = patch_tiles(2)
    c = classify(tiles[0])
    pts = c["pts"]
    orient = 1 if signed_area(pts) > 0 else -1
    fig, ax = plt.subplots(1, 2, figsize=(12.5, 5.6), gridspec_kw=dict(width_ratios=[1, 1.15]))
    a = ax[0]
    n = len(pts)
    for i in range(n):
        p, q = pts[i], pts[(i + 1) % n]
        a.plot([p.real, q.real], [p.imag, q.imag], color="tab:red" if c["red"][i] else "tab:green", lw=3)
    for i in range(n):
        t = c["turns"][i]
        if t == 0:
            a.plot(pts[i].real, pts[i].imag, "x", color="k", ms=9, mew=2)
            continue
        convex = t * orient > 0
        col = "tab:blue" if abs(t) == 60 else "tab:orange"
        a.plot(pts[i].real, pts[i].imag, "o" if abs(t) == 60 else "s", mfc=col if convex else "w", mec=col, mew=2, ms=11)
    a.set_aspect("equal")
    a.set_title("tile 0: %d red and %d green edges\n%d x 60 deg, %d x 90 deg, %d straight (filled: convex, open: concave)"
                % (c["n_red"], c["n_green"], c["by_turn"][60], c["by_turn"][90], c["by_turn"][0]), fontsize=9)
    a.legend(handles=[Line2D([0], [0], color="tab:red", lw=3, label="red edge (even multiple of 30 deg)"),
                      Line2D([0], [0], color="tab:green", lw=3, label="green edge (odd multiple)"),
                      Line2D([0], [0], marker="o", color="w", mfc="tab:blue", mec="tab:blue", ms=9, label="60 deg corner"),
                      Line2D([0], [0], marker="s", color="w", mfc="tab:orange", mec="tab:orange", ms=9, label="90 deg corner (always red-green)"),
                      Line2D([0], [0], marker="x", color="k", ms=8, mew=2, ls="", label="straight pass")], fontsize=7, loc="upper center",
              bbox_to_anchor=(0.5, -0.08), ncol=2)
    b = ax[1]
    for t in tiles:
        cc = classify(t)
        pp = cc["pts"]
        for i in range(len(pp)):
            p, q = pp[i], pp[(i + 1) % len(pp)]
            b.plot([p.real, q.real], [p.imag, q.imag], color="tab:red" if cc["red"][i] else "tab:green", lw=1)
    b.set_aspect("equal")
    b.set_title("the patch of level 2 (%d tiles): every tile has the same corner counts" % len(tiles), fontsize=9)
    fig.tight_layout()
    if save:
        os.makedirs(os.path.dirname(save) or ".", exist_ok=True)
        fig.savefig(save, dpi=150)
        print("saved", save)
    if show:
        plt.show()
    plt.close(fig)


def main(argv):
    tiles = patch_tiles(2)
    cs = [classify(t) for t in tiles]
    print("%d tiles; corner counts (|turn|: number) of tile 0: %s; edges %d red, %d green" % (len(tiles), dict(cs[0]["by_turn"]), cs[0]["n_red"], cs[0]["n_green"]))
    print("corner counts the same for all tiles: %s;  colour splits (red, green): %s" % (
        all(c["by_turn"] == cs[0]["by_turn"] for c in cs), dict(collections.Counter((c["n_red"], c["n_green"]) for c in cs))))
    d = argv[argv.index("--save-dir") + 1] if "--save-dir" in argv else None
    figure(os.path.join(d, "spectre_contour_corners.png") if d else None, "--no-show" not in argv)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
