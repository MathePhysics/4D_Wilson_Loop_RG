# Triage: RC Consolidation and Peer Pointers (11 November 2026)

Two-loops session. The user's instructions: "Also consolidate" (the series RW1, RC, READINGS); "Continue with RW1, when consolidating check for "not used" phrases"; "Close the open gaps, then continue with RC"; "Continue".

## RC_PROOF_PASS_2026_10_23.md

- 966A0D5FC01A (97,834 bytes, 203 lines) → 40BA9FDBEBB1 (61,908 bytes, 151 lines, 129 tags {#RC.x}, longest line 624 characters, LF endings).
- Pre-check:
  - every line re-read against the cited transcriptions (CRE, RG I, RG II, PBG, VAR, LFR I and II) and against V4's labels;
  - status history, pass numbers, roadmaps, hedging and "not used" asides deleted (none left);
  - V3 and V4 line pins replaced by V4 labels;
  - every new symbol checked against all table rows: θ, C_V, ρ_b, ζ, λ and g(z) clashed and became C_{P″}, C_𝔙, Ω_V, m_z and f^♮_{P°}; ρ₀ and c_dec removed; δ_* is now δ₀^{PBG};
  - #RC.5-3 (739 characters) and #RC.5-6-2 (673) split into the new #RC.5-3-1 and #RC.5-6-3, and their citers (#RC.4-4, #RC.5-7-1, #RC.6-7) repointed.
- Repairs:
  - The potentials' dependence on the shift through Q(Y, B) in §6. The per-bond hypergraph expansion failed, since its 2^{|Y|} subsets beat the decay per M⁴ volume. It is replaced by one Cauchy estimate in all shift variables of P° at radius (C_{P″}r)^{−1}, with β_{P″} := 2e²C_{P″}ϵ_mr² ≤ g₀^{1/2} (#RC.6-5-8–#RC.6-5-13). The potentials are bounded by Cauchy in one variable on Ω_V := {|B| ≤ O(K_m)r}, with C_𝔙 := O(α₄M⁴K_m²) (#RC.6-5-12–#RC.6-5-12-1), and the step-1 τ (#RC.5-6–#RC.5-6-3).
  - The argument bound (K_m + 3)r held only at s = 1; it is now O(K_m)r on Ω_V.
  - B₀. #RC.4-4-2 had redefined CRE's B₀ as a g₀-dependent constant and dropped the factor g_k of p.278 l.34–35. The (3.37) terms are now O(g₀p₀³(g₀)) (#RC.3-14-1), and (2.42) holds for every B₀ ≥ 2C_{d,L,M}C₃ε₁, independent of Λ and g₀ (#RC.4-4-2–#RC.4-4-3, #RC.0-2).
- Not reviewed (#RC.0-4): #RC.5-6–#RC.5-7, #RC.5-6-2–#RC.5-6-3, #RC.5-8, #RC.6-5-8–#RC.6-5-13, and the B₀ repair in #RC.3-14-1 and #RC.4-4-2.

## RC_PAYMENT_PASS_2026_10_24.md

- 672F30EE25EE → 7C12BDBA0A43. #RP.0, #RP.N5, #RP.2 ("Section 5 is not used" deleted), #RP.2-9-1, #RP.2-17-1 and #RP.7-4 now cite RC tags. Bookkeeping; no round.

## Peer Pointers from the LF Session ("yang mills 4 handover (4)")

- BLL change notice. EP #39-7-0 now cites #BLL.6-00 and LFR II p.370 l.45–48, and the undefined "Λ̄" is gone. Re-derivation: the zero piece vanishes by RG2 p.4 l.17–24, since the arguments enter at points of Λ, which the cubes outside σ cover, and J_{1,2} enters only through 𝐆″_k's kernel, with its sources in Z″_{h+2} ⊂ Λ. EP #39-5-1-0's Dep(F) ⊂ X(F) now cites #BLL.4-00. Every other BLL tag in EP and GC resolves at BLL AC2673259A3B.
- O4 bracket. EP #71-2 (with the new #71-2-1) and GC #6.17.3-3 now quote O4 §2(e)'s generator bracket C_w′/2 + 4C_{c₀} + 8C_odL, with ρ_ω = 4c_G′ times the bracket times (1+β₀)²α_{1,1}r (O4 lines 72–74 and 95, and D2.6 closure line 206, read).
- PC #PC4.8-5.2: "V3's" → "V4's" (map #MD2.4.3.10 and #MD2.4.3.12-1 read).
- X(𝒢). TL #512-1 (BETA's) already contains the members of merged old occurrences. NL #NL6A.2-3 now cites #512-1, #512, #514 and map #MD2.4.4.3-1, and the new #NL6A.2-3-1 notes that #_{k+1}(𝒢) counts the members (map #MD2.4.3.1). NL #NL6A.5-3-4's count is unchanged, since the map's Γ-vertices carry the members' domains (#MD2.4.12.17, #MD2.4.12.19-2).
- FV. PC's two citations of (5.11) use the rooted form (Theorem 5.4) and are correct; the hits form is Lemma 5.6, (5.17), p.226 (FV pp.221–227 read).
- Sent to the LF session:
  - this session's role;
  - the RC tag map for map #MOMGD.22–#MOMGD.25-2, LINE_DEFECT lines 5, 350, 356, 509–511 and 554, D26 line 412, and READINGS_INVENTORY line 60;
  - defect (a): LINE_DEFECT line 356 and CRE_SOURCE_INSERTION_PASS line 46 drop the factor g_k of p.278 l.34–35, and the latter pins the passage at "L5–6" instead of l.32–35;
  - defect (b): LINE_DEFECT line 510's margin count differs from RC #RC.4's (5LM₁ ≤ ½ℓ for R₁ ≥ 10);
  - the Cauchy note's line 1050 cites (5.11) for a hits bound, which is (5.17);
  - LABELS_D2_STEP_MAP line 1269 is stale.
- The pointer edits change no bound. They are bookkeeping, with no round.

## READINGS_RECHECK_2026_10_23.md

- 32F7FAA03962 (62,750 bytes, 75 lines, one table) → F9854511A508 (34,908 bytes, 134 lines, 80 tags {#RR.x}, longest line 624 characters, LF endings, no table) → F6BD3BF784DA after the P₁ relabel below (35,566 bytes, 81 tags). Old row n is now #RR.n (row 2a → #RR.2a, row 7a → #RR.7a, row 9a → #RR.9a); the old summary bullets are #RR.36–#RR.38 and the status block #RR.S1–#RR.S6.
- Pre-check:
  - every pointer resolves (122 map, RTR, RC and RP tags);
  - every page pin re-read in the corrected transcriptions;
  - no "not used" asides, history or roadmaps left.
- Repins to corrected lines:
  - CRE: p.244 l.22, p.256 l.2, p.247 l.53–57, p.267 l.27–28, l.42 and l.44, p.269 l.43–44, l.46–47 and l.51–55, p.276 l.25–31, p.279 l.8–12, p.246 l.14, p.262 l.39–40, p.251 l.39;
  - RG1: p.251 l.30, p.255 l.14, p.279 l.47, p.275 l.28, p.259 l.38–p.260 l.2;
  - RG2: p.3 l.23, p.5 l.16, p.8 l.27, p.9 l.48, and p.15 line 30, where the print's "|(7.14)|" survives only in p015.tex l.31 with its note at l.38.
- Row fixes:
  - row 22's equation now has B′ = B − hD̃(B);
  - row 27's stale C₃′ = C₃e^{(L−2)κ/20} is replaced by the enlarged-constant C₃′ (map #MD2.4.1.20–21);
  - row 16's θ is per layer (#MOMGD.55-1);
  - row 3's condition is 40C_H(α_{0,1} + α_{1,1})e^{−R₀} ≤ g₀ (#MD2.2.6.194-6), and D₀ is printed (p.251 l.23);
  - row 9 reads q₀ = q₁ > p₀;
  - row 23 cites the D2.7 closure item 1(a)–(b) with the step depth N_k := N̄(K − k), and the new #RR.23-1 quotes LFR II p.390 l.10–11;
  - the status of the base points and of (d′) now records the reviews of rounds 45 and 53.
- New item #RR.39: PBG p.397 l.29's "(2.36) in [4]" is PRT2 (2.46). [4] is CMP 96 (PBG p.433 l.53); PRT2 (2.36) is Σh² = 1 (p.229 l.15); PRT2's only d(y,y′) is (2.46), p.231 (p.230 l.52); and VAR p.288 l.45 refers to [3] = PRT2 (VAR p.309 l.23). This is not yet reviewed.
- P₁ (after the LF session's map 1ca92b6f470a, re-derived here from RG1 pp.272–273 and PBG (3.33), p.396):
  - D2 no longer reads P₁. (3.13)'s second argument is (L^{j−1}η)³𝐉 + (D*D + DRD*)𝐀 + 𝐅(𝐔, 𝐀), with 𝐅(𝐔, 0) = 0 by (3.11), and the analyticity condition is (3.14′) (map #MD2.2.4.88-3).
  - Bałaban's (3.14) bounds on 𝐇 (p.273), together with his identity at p.272 l.22, give the (3.14′) bound (#MD2.2.4.91-2).
  - #RR.19 is now "Derived from print", #RR.19-1 states (3.14′) and the covariance, and the new #RR.19-2 lists P₁'s occurrences and the other P₁ objects. #RR.S5 records that no item rests on an inferred reading.
  - The map's pin "(p.272 l.17)" for 𝐅's locality in #MD2.2.4.88-3 should be l.19. The LF session fixed it (map 7e2a5cdf96e6, checked here) and confirmed that #RR.19–#RR.19-2 and #RR.S5 match the map.
- Citers to repoint, sent to the LF session at 05:50 with the tag map and #RR.39's evidence:
  - map #MOMGD.17's "rows 1–34";
  - D2_OPEN_ITEMS_CLOSURE line 74's bullets (→ #RR.36–#RR.38) and its line 17 status;
  - GAMMA_REPAIR_ATTEMPTS l.4813 (row 9) and l.4815 (row 27);
  - map #MD2.2.6.159-1's "inferred, not printed" (→ identified, #RR.39);
  - map #MD2.2.6.190-54's "not used" aside;
  - map #MD2.2.6.190-12, which mixes N and N_k.

## SHAs

RC 40BA9FDBEBB1, RP 7C12BDBA0A43, EP 2081F76D1A00, GC 1BFCB0FD8DD1, PC E1340CF820F5 (LABELS_PAIR_CAUCHY DFE71A7404C6), NL E128A0394BD9, READINGS F6BD3BF784DA.
