"""Locate the `spectre-monotile-py` clone and put it on sys.path.

The bridge figures use `lift4d.py` and `spectre_patch.py` of https://github.com/brentharts/spectre-monotile-py.  Nothing from it is copied
here.  The clone is looked for in $SPECTRE_DIR, then in `../spectre-monotile-py` next to this repository (where `make install` puts it).
"""
import os
import sys

_HERE = os.path.dirname(os.path.realpath(__file__))
_REPO = os.path.dirname(os.path.dirname(_HERE))


def spectre_dir():
    for d in (os.environ.get("SPECTRE_DIR", ""), os.path.join(_REPO, "..", "spectre-monotile-py")):
        if d and os.path.isfile(os.path.join(d, "lift4d.py")):
            return os.path.realpath(d)
    return None


def use():
    """Add the clone to sys.path and return its path; exit with a message if it is missing."""
    d = spectre_dir()
    if d is None:
        sys.exit("spectre-monotile-py not found: run `make install` in the repository root (clones it next to this repository), or set SPECTRE_DIR.")
    if d not in sys.path:
        sys.path.insert(0, d)
    return d
