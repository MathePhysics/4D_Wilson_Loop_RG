# Triage: LF part 13a1, round 5 (lf-p13a1-20261107-r5), 7 Nov 2026

## Verdict

Not clean: one serious finding (S1), one minor (m1), and four trivial (t1–t4). No fatal finding. The clean count of 13a1 stays 0.

LF reviewed at 49628896d858; repaired LF 22a21c559148. Table c6beb03f3952 and LABELS f93fef03e92d, before the fork's #T12.9 edit and relabel (requested 21:06).

## Repairs

| Finding | Where | Repair |
|---|---|---|
| S1 (serious): the layers of 𝐁_k(Z) inside Λ were unsourced. #4.48.1 identified 𝐁_k(Z) with CRE (2.2) restricted to Z, which would put layers j ≤ k₀ in Λ and break c′_Λ's uniformity | #4.44-0–#4.44-0.2 (new), #4.46-0, #4.46-2, #4.48, #4.48.1, #4.48.1-1 (new), #4.48-3.0.1 | Sourced identification. 𝐁_k(Z) is CRE's minimal determining set of Z (CRE p.256 l.58–p.257 l.3, LFR I (1.74)); its top domain, of k-blocks, contains Z^{∼−2} for M₁-cubes (#3.84-1). Its layers below the top are ≥ LM₁ wide, and only adjacent layers meet (BP_LAYER_WIDTHS #4.11). Λ is at sup-distance ≥ 8MR_k from Z^c (old #4.48-3.0/#4.48-3.0.0, moved unchanged to #4.44-0/#4.44-0.0, since the fact is now used before the weight 1 − ζ₀). So every block within 6MR_k of Λ is a scale-k block, and the data V′ are top-layer data (M^k(Q_k^{s*}V_k) = V_k, #3.84-1.1). N_bl: adjacent layers only, which gives 3^d + 2^d + (L + 2)^d ≤ N_bl. c′_Λ: (b)'s count with RM replaced by LM₁ under (J-W) (BP_LAYER_WIDTHS #4.16, #4.18-2). The reviewer's alternative reading (Λ adjacent to a layer k₀ of CRE's global set) does not arise: the global layers are not layers of 𝐁_k(Z) |
| m1 (minor): operator norm e^{√Nη abs(ℋ)} | #4.48.0, #4.48.0-2, #4.50-1.0 | Condition abs(ℋ)_y ≤ (log 2)/(8√N), G ⊂ U(N) (#T10.18), since ‖X‖_op ≤ √N abs(X); the transports have operator norms ≤ e^{√N abs(ℋ)_y} ≤ 2^{1/8}; the (T-Λ) entry is changed to match |
| t1: C(M) was completed by reference to later sections | #4.43-1.2 | C(M) is now the explicit maximum of every lower bound the note places on it (grep of "C(M) ≥": #3.96-1-1, #4.51-1.1, #4.116-1, #4.152, #4.177, #4.560-1.1.1, #4.560-1.1.2), the redundant 4C_𝔛 and 8(1 + κ_s)M₀ being covered by 8(1 + κ_s)max(M₀, C_𝔛(M)) |
| t2: the bonds of Λ under RG I p.251 | #4.48.1, #4.48-3.0.3; table #T12.9 | c′_Λ := 2d(100M + 1)^dc_tot(1/16) and N_Λ := 2d(100M + 1)^d, for the bonds that meet Λ; table row update sent to the fork |
| t3: U_0's curvature was credited to (b)'s lines | #4.48.0-0 (new; #4.48.0 split at ~600 characters) | U_0: abs(F) ≤ 2abs(∇^η𝔸_Z) + O(ε₁²) < 3ε₁ by #4.43-1 and C(M) ≥ O(1)M⁶, a_j ≤ 1, C₀^{ms} = 2L⁴C₀ ≥ 2 (#T4.4, B₃ ≥ 1 by #T3.13); ε₁'s smallness for it is added to (T-Λ) |
| t4: the factor 2 for 1 + O(η⁴abs(F)²), and the covariance of ∇ | #4.48.0, #4.48.0-1, #4.50-1.0 | Threshold O(1)(C₀^{ms}ε_r)² ≤ 1 added to #4.48.0 and (T-Λ), with η⁴abs(F)² ≤ (2C₀^{ms}ε_r)²; ∇ in ‖·‖_y is PBG's covariant derivative at U (PBG p.397 l.5–7), so Dℋ is its antisymmetrisation |

The weighted clause of #4.48.0 is now #4.48.0-3 (tag #D.w_y.c unchanged), with its consumers re-pointed: #4.48-3.0.2 and #4.54-0.1; #4.51-2.1 is re-pointed to #4.48.0-1.

## Consumers outside 13a1

- 13a2: #4.51-2.1 and #4.54-0.1 now carry citation changes only. C_Δ, C_pr and C_A use c′_Λ, N_bl and C_bd symbolically, so their formulas are unchanged; c′_Λ gains the factor 2 (t2).
- BP_LFR2_REPLACEMENT.md #160.7 (two-loops session's file) cites LF #4.48-3.0. A re-point to #4.44-0 was requested by message at 21:06.
- No live note cites #4.48.0's weighted clause or the (log 2)/8 condition outside the LF.
- The table cites "#4.48.0" for ε_r only, which is unchanged.

## Pre-check, lf-p13a1-20261107-r6

- Changed lines re-read: #4.43-1.2, #4.44-0–#4.44-0.2, #4.46-0, #4.46-2, #4.48, #4.48.0, #4.48.0-0, #4.48.0-1, #4.48.0-2, #4.48.0-3, #4.48.1, #4.48.1-1, #4.48-3.0.1, #4.48-3.0.2, #4.48-3.0.3, #4.50-1, #4.50-1.0, #4.50-1.1.0-1, and in 13a2 #4.51-2.1 and #4.54-0.1. #4.43-1.2's term (1 + β₀)(1 + A₁/A₀)C and #4.50-1.1.0-1's (1 + β₀)²γ < e^{−p₀} come from 13a2 r5's m3 (WILSON_IT1_LF_TRIAGE_P13A2_R5_2026_11_07.md); they were re-read against #1.3, #1.6, #1.7, CRE (2.6) and the Cauchy note's #C5.7-5.
- Cited displays re-read in the transcriptions:
  - CRE p.254 (2.1), p.255 (2.2)–(2.3), and p.256 l.20–22, l.56–63;
  - CRE p.257 (2.13)–(2.14);
  - LFR I p.177 l.17–40, p.179 (1.10), p.180 (1.19)–(1.20), and p.192–193 (1.73)–(1.75);
  - LFR II p.357 (1.3)–(1.6);
  - PRT2 p.224 (2.1)–(2.2);
  - PBG p.397 l.5–7 and p.422 (3.133);
  - VAR p.279.
- Grepped:
  - every use of 𝐁_k(Z), 𝔹_k(Z), (log 2)/8, 2^{1/8}, "C(M) ≥", #4.48.0, #4.48.1, #4.48-3.0 and #4.48-3.0.0, c′_Λ, N_Λ and N_bl, in the LF, the Cauchy note, the table and balaban_proofs;
  - §3's spelling 𝔹_k(Z), now tied to 𝐁_k(Z) at #4.44-0.1.
- Lines: the new and changed lines are ≤ ~615 characters. The pre-existing long lines (#4.43-1.1, #4.45, #4.46-1, #4.47) are unchanged.
- No forward tag citations: #4.46-0 and #4.46-2 cite #4.44-0.2, and #4.48 and #4.48.1-1 cite #4.44-0.1.
- Part size: 13a1's reviewed blocks are 20,252 characters at r6 (≤ 25k). The growth over r5 is the new mathematics of S1 (the layers of 𝐁_k(Z)), m1, t3 and t4. The moved lines #4.44-0/0.0 replace #4.48-3.0/3.0.0.
- Second whole-part read at the frozen r6 extract (22:15), with every bound's arithmetic redone (#4.46-0, #4.47-0–#4.47-2, #4.48 N_bl, #4.48.0-1, #4.48-1–#4.48-2, #4.48-3.0.2–#4.48-3.1, #4.49, #4.50, #4.50-0, #4.50-1.1.1-1, #4.50-1.2). Two unstated reasons were found and are now stated in place:
  - #4.48-3.0.3: c_tot(1/32) ≤ c_tot(1/128), since c_tot(α) = 26c₀^d(½α) decreases in α (#T4.23);
  - #4.46-1: |e^{iY} − 1| ≤ |Y| < 2C₁ε₁ ≤ C₁′ε₁, as c_tot(1/128) ≥ 26 (#T4.23), in place of "for ε₁ small". The line (638 characters) is split at its remark on VAR's C₁, now #4.46-1.1, and #4.561.1-2 is re-pointed to it.
  - LF 3bc0f6261a26.
- Whole part re-read for gaps, #4.43–#4.50-2: (T-Λ)'s entries #4.50-1.1.0 ("#4.48.0's conditions, also at …") cover the new conditions at every ε_r used, and each is of the form cC₁ε₁ ≤ c′ (#4.50-1.0).
- Table and labels:
  - the fork entered #T12.9 (c′_Λ and N_Λ with 2d), re-derived and verified, and relabelled: table 9e1dbb8c8284, LABELS bfdc1e21d136;
  - it then changed one word in BETA's #T12.24-1 (table 67c31cf2ca2d, LABELS 7ae7b12dea0c), which neither part cites;
  - after the 13a2 r5 and 13b r2 repairs it entered #T3.33, #T12.9, #T12.9-1 and #T12.12 (verified) and relabelled: table d3fd1c0fcdf7, LABELS 80e6a1bdf9e4.
- Built: reviews\lf-p13a1-20261107-r6 at LF 3bc0f6261a26, table 7a009cefc43a, LABELS 69fc7acb91d1, with 0 definition conflicts (7 allowed); the earlier r6 builds, at LF 22a21c559148, 400c5fa76246 and ff32ad403ddb, were never launched and were removed. The fork checked the two new reasons against #T4.23. The spec's (T-Λ) question now names (1 + β₀)²γ < e^{−p₀} in place of 4Lδ′_k ≤ ε_k, and its stale 𝔯 and ε₂ entries were updated.

## Pre-check, lf-p13a2-20261107-r5 (rebuild)

- The first build (folder without review.md) was removed and rebuilt at LF 22a21c559148: 10,841 characters, 0 definition conflicts.
- Changes in the part since the first build are citations only:
  - #4.51-2.1 cites #4.48.0-1;
  - #4.54-0.1 cites #4.48.0-1 and #4.48.0-3.
- c′_Λ's factor 2 enters C_Δ only through the symbol.
- The spec's w_y entry points to #4.48.0-3. The earlier pre-check, in WILSON_IT1_LF_TRIAGE_P13A_R5_2026_11_07.md, stands otherwise.
- S1's repair removes the reason 13a2 was held (c′_Λ and N_bl are now sourced).
