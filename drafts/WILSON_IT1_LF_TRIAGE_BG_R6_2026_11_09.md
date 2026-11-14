# Background-Iteration Closure, Round r6 (it1-bg-20261109-r6): Triage

Packet: reviews\it1-bg-20261109-r6, a full round of the repaired part on note 44f58683dac5. Its pre-check is in WILSON_IT1_LF_TRIAGE_BG_R5_2026_11_09.md, *Pre-check for r6*.

## Verdict (report read in full, 9 Nov 2026)

Not clean. There is no fatal finding, two serious findings and nine minor ones. The referee found §3.2 and its conditions correct, uniform in K and ℓ_C, and r5's findings all repaired.

## Repairs

Line numbers are the snapshot's.
- **S1** (l.127–134): the prints bound |∂U − 1| and |A′| only on Bałaban's layers, not on Γ₀ = Ω₁ᶜ, and TL #222-2 places the 𝐑-step's points in 𝒟^{λ,3} only up to T₂^{old}; the note also conflated points with their representatives.
  - Repair, a structural one: the coarse loop now uses the k-fold average only on its *inner* bonds, those whose two scale-k blocks lay in Ω_k at step k, and the transport T_c(U_j) on the others (§1.1). On an inner bond (M^kU_k)(c) = V_k(c) by CRE (2.11)–(2.12).
  - An inner bond's blocks lie in Ω₁, which never shrinks: CRE p.256 l.26–29, LFR I (1.12) Ω″₁ = Ω₁, and LFR II (1.33) Γ_k = Γ″_k ∪ Z^{(k)} (§1.6). So the layer bounds cover every block an average is taken over, and Γ₀ is not used ((iii-d) *The layer bounds*).
  - At TL's points: off T₂^{old}, the conjugation by ũ costs 17/16 (#6.1, #6.2-1), and the telescoping to the G-valued U adds 4.1θ; on T₂^{old}, #5.6-1 gives the curvature. No representative is used (*At TL's points*, the chart bullet). t^R and θ^R are redefined accordingly.
  - β_k^{(j)} := f_j − g_k^{(j)} is the map's #MOMST.85 on all-inner terms, and #MOMST.83, #MOMST.89 hold as printed, since a transport bond has E_c = 0 (§1.4). Consumers updated: §1.2, §1.3, §1.5, §1.6, §2.2, §3.1, §3.3–§3.5, §4.3, (iv-a), the carrier item.
- **S2** (l.129, l.141–142): the coarse class's bound at the 𝐑-step's 𝒟^{λ,3}_j points was not shown, since TL #6.13-2 uses entire transports (#6.12.4).
  - Repair: a coarse #6.13-2 (*The carried insertions and the class*). Of #6.12.4–#6.12.5 and #130.15.2 (4), only #6.12.4 uses entireness. The coarse transports and composed slots on the inner bonds are bounded at the point itself by the chart bullet (τ_c ≤ 2, 1 + ‖X_c‖ ≤ e^{0.52}), and those on the other bonds are the fine chain's. T-step-made members go through #6.14.
  - The two-loops point queued after r6 is applied: the coarse chain's 𝐑-step evaluates at points of the same 𝒟^{ev}_j (*The evaluation points*).
- **m1** (l.124): the covariance of M^k is cited to 4.1(2) and RG1 (0.4), and M^k(1) = 1 to (0.4) with log 1 = 0.
- **m2** (l.132, (C6)): L₀² ≤ L/3 is recorded as printed "for example" on LFR I p.191 and adopted in (C6).
- **m3** (l.240): the closing list says that §1.6 and (iii-d) also use the readings they label inferred, not printed.
- **m4** (sources): LFR II p.373 l.15–16, #MOSTC.15-2, TL #130–#136, and the table rows #T3.39, #T4.37, #T4.47, #T4.49 and #T12.13 are listed.
- **m5** (l.139): the arc's phase bound reaches the fine bonds of the arc's blocks because D^R_c ⊂ B^j(Ω_j) (15.5 bullet). c_π^ℂ (relative to ‖·‖) and c_π′ (relative to |·|) are distinct symbols.
- **m6** (the list of uses): the flat and pure-gauge values (15.4(i), 15.6(a)) and 15.8(c)'s e^{A_j} ≤ e are listed and treated.
- **m7** (l.125): the arc and block statement is labelled inferred, not printed.
- **m8** (l.137): the count is 3^d for a far word whose D^R_c meets no component of Z, and if D^R_c meets components, Y₁ contains them and D^R_c adds at most 3^d cubes. The same point in D2.7 15.5(ii)(α) was sent to (4).
- **m9** (trivial): the arc count is (100R_j + 6)^d ≤ (103R_j)^d with M ≥ 1. a_j's new term is said to tend to 0 with g_K. The constants line names θ_c as local.

## Self-Review of the Whole Note (user, 9 Nov 2026: "You are supposed to review every package yourself!")

Every line from §1 to the closing lists was read after the S1–S2 repairs. Repairs:
- §1.3 (k = 1, j = 1): the identification with the map's (6) X_j is restricted to the inner bonds, where (MU₁(V₁))(c) = V₁(c) as an identity in V₁.
- §3.4:
  - g_K^{(K)} is cited as §1.1's.
  - The ℒ_K term of §3.4's identity is Σ_{ℒ_K}∫(𝒲^f_K − κ_f^{(K)}e^{𝓔^f_K}g_K^{(K)}), bounded by 2κ_f^{(K)}e^{c_C}δ_LF ((iv-e) *The bound*). The former κ_f^{(K)}(e^{c_C} + e^{Re E^f_{const,K}})δ_LF was §3.1's R_bad at k = K, not §3.4's term.
  - The volume-uniform form with an undefined constant C is deleted from §3.4, and the K′ sentence no longer counts κ_f^{(K′)} twice.
- §3.5: the coarse words are W_χ(C^{(1)};U^{[1]}_j); g_1^{(1)} = W_χ(C^{(1)};V₁) holds on the all-inner terms, not on every label; "the covered terms" is replaced by 𝔏_good.
- §1.5, 4.1(1), §2.4: k = j is allowed, so L^{k−j} ≤ 1, not ≤ 1/L; the enlargement stays below a π_{j+1}-side LM.
- 4.1(3), (C4): the Claim's condition is c_π′c_CM·4B₀e^{16κ_s}ε_H ≤ 1 (#MD2.1.4.27-1), not with c_π. With c_π′ ≥ 2c_πc_h the first part of (C4) at k = 1 needs M ≥ 6(d+2)/c_π (1.06·44/8 = 5.83). The j-form condition is now said to imply (C4). (C4)'s restatement of 4.1(3) is deleted.
- 4.1(4), (iii-a): 1.04·1.06 = 1.1024, so the constant is 1.11, not 1.1. One coarse radius ε_H^{(k)} := ε_H/(1.12(b_d^c)^k) serves (iii-a) and §5.3 (4), which had ε_H/(b_d^c)^k.
- §5.3 (4): the 𝐇 part of the transport factor is ≤ e at ε_H^{(k)}, by c_hc_π^ℂ ≤ c_π′ and #MD2.1.4.27-2. The a′ part is ≤ e for small g_K, the a′ budget of #MD2.4.11.4-1. The conditions list is updated.
- (iii-d):
  - A scale-k arc bond that is not inner carries fine transports, which the arc excess did not count. Both kinds are at most e^{3.31c_π′(b_d^c)^kα_{1,j}L^{k−j}}, since c_hc_π^ℂ ≤ 2c_πc_h ≤ c_π′. So a_j's arc term is 1330c_π′(b_d^c)^kα_{1,j}MR_j, and a_j names C_α's (103R_j)^d.
  - The fine transports in 15.8's sum use c_π^ℂ, not c_π.
  - The site and block inference is restated. Bałaban's sets of the scale j are sets of step-j sites, with fine point sets B^j(·), so the arcs end at step-j sites, which are scale-k sites. "MR_j is a power of L" is deleted, since nothing uses it.
  - The 3^d count is stated with M ≥ 2.
- (iv-b):
  - The undefined C is replaced by the pointwise factors (1 + ‖I‖) and max(1, e^{Re E^f_{const,k}}). The needed per-creation-step total is C_we^{−2p₀(g_j)}, with C_w independent of K, j, □ and the volume.
  - The tube lies within L^{k−K}/2 ≤ 1/2 of C, since k = K is allowed.
  - Bałaban's lifetime is written K_Z.
  - The line is split.
- Sources: #MD2.0.5.30, #MD2.1.4.27–#MD2.1.4.27-2 and #MD2.4.11.4-1 are added. The constants line names ε_H^{(k)}.
- Lines rewritten in this pass and over ~600 characters are split at sentence boundaries: 4.1(3), (iii-a), §3.4, §3.5, (iv-b), (iv-e).

Note SHA after the pass: 21f190678787 (103,571 bytes, LF).

## Status

(iii-d) is derived, given (iii-a)–(iii-c) and (iv-a)–(iv-c) under (C4R), and not reviewed. No round is built: per the user's instruction, the review in this pass is the session's own.
