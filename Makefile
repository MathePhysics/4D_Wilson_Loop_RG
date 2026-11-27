# Makefile for the numerics of this repository.  Nothing here is needed to read the manuscripts.
#
#   make install   clone spectre-monotile-py next to this repository (needed by numerics/bridge_figs only)
#   make test-quick  the fast checks only (about 2 minutes)
#   make test      all checks (about 10 minutes: numerics/corner_locality is the slow part)
#   make figures   regenerate every figure into the figures/ folder of its directory
#   make clean     remove __pycache__ folders
#
# Needs python3 with numpy, scipy and matplotlib.

PYTHON ?= python3
SPECTRE_REPO = https://github.com/brentharts/spectre-monotile-py.git

.PHONY: help install test test-quick figures clean

help:
	@sed -n "1,9p" Makefile

install:
	@if [ -d ../spectre-monotile-py ]; then \
		echo "../spectre-monotile-py already exists; update it with: git -C ../spectre-monotile-py pull"; \
	else \
		cd .. && git clone $(SPECTRE_REPO); \
	fi

test-quick:
	cd numerics/abelian_first_step && $(PYTHON) test_abelian_first_step.py
	cd numerics/bridge_figs && $(PYTHON) test_bridge_figs.py --no-energy

test: test-quick
	cd numerics/corner_locality && $(PYTHON) test_corner_locality.py
	cd numerics/bridge_figs && $(PYTHON) test_bridge_figs.py

figures:
	cd numerics/corner_locality && $(PYTHON) corner_locality.py --no-show --save-dir figures
	cd numerics/corner_locality && $(PYTHON) width_scan.py --no-show --save-dir figures
	cd numerics/corner_locality && $(PYTHON) offset_average.py --no-show --save-dir figures
	cd numerics/corner_locality && $(PYTHON) contour_map.py --no-show --save-dir figures
	cd numerics/corner_locality && $(PYTHON) gauge_compare.py --no-show --save-dir figures
	cd numerics/corner_locality && $(PYTHON) L_dependence.py --no-show --save-dir figures
	cd numerics/bridge_figs && $(PYTHON) spectre_contour_corners.py --no-show --save-dir figures
	cd numerics/bridge_figs && $(PYTHON) lift_to_z4.py --no-show --save-dir figures
	cd numerics/bridge_figs && $(PYTHON) scope_map.py --no-show --save-dir figures

clean:
	find numerics -name __pycache__ -type d -prune -exec rm -rf {} +
