# Triage of lf-p13b-20261108-r14

## Verdict

- r14 was a narrow round of 13b at LF 0dfaf73c3db4, table 6d09b1b5054d, and labels 971e7d7d5325.
  - Under review: #4.52-1–#4.52-1-2, #4.561.1-1.3-1.0–#4.561.1-1.3-1.0-1, and #4.567–#4.568.
  - Named steps: #4.52-1-1.1-1, #4.52-1-1.1-2, #4.52-1-2, and #4.561.1-1.3-1.0.
- **Fatal:** none. **Serious:** none. **Minor:** none.
- **The round is clean.** 13b's clean count is 1. Its next round must be full; a narrow round cannot be the second clean one.
- **Observations:**
  - o1 (trivial): #4.52-1-1.1-1 left implicit the induction hypothesis, the identification of Ū_{b′} with (Q^{s*}_{k−n−1}V_Λ)(b′), and "inside Λ".
  - o2: carried housekeeping (LABELS, #T11.33's qualifier), which is the table fork's.
- Round 13's m1 and o1–o3 were confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| o1 | #4.52-1-1.1-1 | Induction hypothesis, the closing identification, and "inside Λ" implicit | Reworded in place: "So M^j(U_{REG}) = Q^{s*}_{k−j}V_Λ inside Λ, l.10's reference term (derived, by induction on j: given it at j = n, at a level-(n+1) bond b′, … so (15) gives Ū_{b′} = 1 or V_Λ(c), which is (Q^{s*}_{k−n−1}V_Λ)(b′), whatever its factor U(b′))." 594 characters |
| o2 | the table, LABELS | #T11.33 lacks "for a general base U₀"; LABELS lacks the new tags and has stale line numbers | The table fork's. It was re-sent at 07:02 and 07:05 with the SHAs and the new tags, and has not replied |

## Checks

- The referee re-derived the induction independently. Its argument matches the 13b r13 triage:
  - In level-n units, the segment [x, x + Le_μ] of a bond b′ crossing a k-face crosses the face in exactly one bond.
  - That bond keeps x's transverse coordinates, so it lies in B(c).
- The reworded line changes no mathematics. The full 13b round will review it.
- No CRLF.

## Rounds

- **Next: 13a1 r10, full.** 13a1's clean count is 0, so r10 can be at most its first clean round.
- **Then 13b r15, full.** If clean, 13b is done.
- **Then 13a1 r11, full,** if r10 is clean.

## Reading of 13b before its full round, and the split

- I read #4.52-1–#4.52-1-2 and #4.556–#4.568 in full while 13a1 r10 ran. The re-derivations:
  - **Lemma (Two Constants), #4.558–#4.558-1.1.** 𝔴 maps D₊ onto the first quadrant. Re 𝔥 is 1 on the segment and 0 on the semicircle. abs((𝔳² − z²)/(4𝔳²)) ≤ ½. The constant is 1 − (4/π)arcsin(1/24) ≈ 0.947 > 15/16.
  - **The lines, #4.559.** abs(A′_R) ≤ abs(A′) from A′_R = (A′ + A′*)/2 in the operator norm.
  - **C_c, #4.560.** α₀ + 50α₁ + 9(α₀ + α₁) ≤ 60(α₀ + α₁).
  - **#4.561.1-0.** e^t − 1 ≤ 2t for t ≤ 1, and C_{V′}ε₁′ ≥ 240c_avα̂₁ and ≥ 16c_avε′_k.
  - **#4.561.1-1.3-2.** The factor 2(1 + 48c_GdB₁B₃).
  - **#4.561-1-2.** C_{AL}ε′_k ≤ ¼C_{V′}ε₁′ and ε₂^{AL} ≤ ε₂/4.
  - **#4.563-1.1.** 16c_avε′_k + c_{rp}ε′_k < 20C_{V′}ε₁′.
  - **#4.563-2.1.** The plaquette move (2 + 16C₀^{ms}ε₁′ + 16ε₂)ε₂L^{−2j}, and c_pl.
  - **#4.563-3.** 1 − ½tr(X + X^{−1}) = −½tr((X − 1)²X^{−1}), and abs(X^{−1}) ≤ 2.
  - **#4.565–#4.565-1.** 15/16 · (1 − ε₀)/3 = 5(1 − ε₀)/16, and the disc bound 2C_act, since the a_y(MU^B) terms cancel along the line.
- No gap was found.
- **Forward pointers.** Three were replaced by tags: #4.556 ("Lemma (Two Constants) (#4.557, derived)"), #4.560-2 ("under (T-c) (#4.561)"), and #4.564 ("the bounds of #4.565–#4.568"). These are bookkeeping. LF 613cc9ffae31.
- **The split.** The full packet's argument measures 25,319 characters (computed as build_packet.py composes it), over 25k. It is split at the heading of (T-c):
  - **13b1:** #4.52-1–#4.52-1-2 and #4.556–#4.560-2, 9.9k, with #4.561 as context.
  - **13b2:** #4.561–#4.565-1 and #4.567–#4.568, 14.8k, with #4.559–#4.560-0 as context.
- **Clean counts.** r14 covered changed lines in both halves and was clean, so each part has a clean count of 1, as with 12a1 after 12a's split. Each needs one full clean round.
- **Specs.** specs\spec_p13b1_r15.json and spec_p13b2_r15.json at LF 613cc9ffae31. --check gives 0 conflicts each. The whole-packet spec_p13b_r15.json was removed unused.

## Pre-check of lf-p13a1-20261108-r10 (full)

- **Spec.** specs\spec_p13a1_r10.json at LF 9cc6351681fb, prior r9, with one extract, #4.43–#4.50-2, all under review. --check gives 0 conflicts (7 allowed).
- **Size.** Built: 21,805 characters of argument, under 25k. The part was 22,883 characters at r9, which included the 13a1 lines as context in a focused packet. The lines grew by the N clause and the (3.133) reading only.
- **Reading.** I read the whole part myself before this full round, as recorded in WILSON_IT1_LF_TRIAGE_P13A1_R9_2026_11_08.md (*Reading of 13a1 before its full round*). The re-derivations there found no gap, and the eleven forward pointers were replaced by tags.
- **Changed since r9:**
  - #4.44-2 and #4.44-2-1 (r9's m1);
  - #4.46-0 and #4.46-0-1 (t-a);
  - #4.47-0 (re-point);
  - #4.50-2 (t-b, t-c);
  - the pointers of #4.43-1.2, #4.44-2, #4.45-1, #4.46, #4.46-1.1, #4.48.0, #4.48.0-2, #4.48-4, #4.50-1.1.0-0, and #4.50-1.2.
- **Symbols.** Every N in the part is #T6.23's representation dimension. Δ_𝔛 lies outside the part (13a2). n_tr, C_bd, C_Φ(M), C_{1−ζ₀}(M), C₁, C_𝔛(M), and α₁^{CMP} are each defined once (definition check).
- No known weak point and no OPEN is in these lines.

## SHAs

LF 0dfaf73c3db4 (r14's snapshot) → 5c005225d6a9 (13a1's pointers) → 9cc6351681fb (o1). Table 6d09b1b5054d (unchanged).
