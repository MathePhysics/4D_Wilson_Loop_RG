# Cauchy §7.6, the 𝐑-Part of the Loop Constant, and D2.7 Item 2, 9 Nov 2026

## D2.7 Item 2's Last Clause (Closed)

- **Claim:** every D26 bound for a component outside the class holds after R. 15.8(a) uses it.
- **Derivation:**
  - On Z_k ∩ Zᶜ the operation 𝐓_k is the same operator ((1.1), p.177). The fundamental factors and the labels the links read are unchanged.
  - A carried member D of an unchanged component is a function of U^{old} on Dep(D), so after R its value is D(Φ(𝐔)) (two-loops #39-2, #130).
  - The next T-step evaluates at 𝒟^{ev}_k, which contains D26 5.1's points (two-loops #222-1, #222.1).
  - Φ maps 𝒟^{ev}_k into 𝒟^{λ,3}_k on every layer, up to T₂^{old} (two-loops #73–#76, #222-2, #229; #5). D26's att bounds hold on the family (#60).
  - The parts with 𝒦 ≠ ∅ are 15.5(i)'s. (T3)'s bridge holds by (G1) for the post-R sequence (LFR II Theorem 1).
- **Edits:** item 2's status heading and last paragraphs, the header sentence, 15.8(a), the Derived list, and removal of *Not derived here*. D2.7 1fcd9c00ecf8 → e88981b21801 → 55d8246f93a0.
- **Message:** to the two-loops session, asking it to check the use of #72–#76, #222-2, #229, and #60. Its reply (12:36) confirms them, with two precisions, both applied: the value is D(Φ(P(𝐔))), equal to D(Φ(𝐔)) on 𝓜^c; off 𝓜^c the bound goes through P, and the part (b) pairs carry #6.8's factor outside the family bounds (#76, #222.1, #130.15.1).

## Cauchy #C7.6-3 (Reported by the Table Fork, 12:24)

- **Finding:** #C7.6-3 quoted D2.7 15.4(ii) without the factor MR_j, with /2 for /4, and without the MR_j-cube units of the rate. Checked against D2.7 15.4(ii): the finding is correct. The rate per L^m is c^R_E/(L·MR_j), which tends to 0 as R_j grows, so no bound of the form A L^m e^{−aL^m} with fixed a holds.
- **Repair (re-derived):**
  - R_j = R̄(K − j) and R_k = R̄(j(C)) (#CP.13).
  - #CP.14-1 and #CP.14-2 give R_j ≤ L^{m/2}R_k.
  - With ι_{T,j} ≥ L^{m−1} (#C7.6-2, from the map's ι_{T,k} = Lι_{T,k+1}, #MD2.0.5.40, and (TC), #MD2.3.4.43), the remainder is ≤ ℓ_CC^R_ER^EL^{3m/2}e^{−b^R_EL^{m/2}}.
  - y²e^{−by/2} ≤ 16e^{−2}b^{−2} then gives ≤ ℓ_CA^R_EL^{m/2}e^{−(b^R_E/2)L^{m/2}}.
  - The T-part reaches the same form with the factor (ea^T_E)^{−1} (#C7.6-2-1).
  - The common per-step form becomes A_EL^{m/2}e^{−a_EL^{m/2}}.
- **Consumers repaired in the same pass:**
  - #C7.6-1 (constants; the anchor #D.A^{TZ}_E moved here);
  - #C7.6-4 (m^E_K, ratio L^{1/2}4^{−(L^{1/2}−1)} ≤ ½ for L ≥ 4, τ^E_K);
  - #C7.6-6-3, #C7.6-6-7 (A^{E,2}, a^{E,2} as #C7.6-1's at the enlarged constants), and #C7.6-6-8;
  - #C7.6-6-4 (r̄^E_K exponent 2/3);
  - #C7.6-7 (split: #C7.6-7-0 holds Δ^E_K);
  - #C7.6-7-1 (sum lemma for a real base Λ ≥ 2, with the m = 1 maximum justified);
  - #C7.8-9-9-1-1 and #C7.8-9-9-1-2; #CK.1-30;
  - continuum #D.B_E := C_Σ𝔞̄ + ℓ_CA^R_ES_E, #ND.5.3-0 (with Cauchy's R̄ choice, on which W_ren does not depend, #CP.13-2), #ND.5.3-2, and #NK.4;
  - LF #3.99-1.
- **Unchanged and checked:**
  - #C7.4-7-5: m^E_K still grows as log log K.
  - #C7.6-7-2: τ^E_K, Δ^E_K, and ρ^E_K are still summable.
  - #C7.8-6 and #C7.9-3-2 use the sum lemma at base L ≥ 2, which still holds.
- **SHAs:** Cauchy 648f51a2e090 → 785c3a36fed5, continuum ebef1c5a23dc → 3ded0274387d, LF b510202f38c5 → f9aee603cdc7.
- **Messages:** to the table fork, with the rows #T4.37–#T4.38 and the SHAs. It updated #T4.37, #T4.38, and #T4.52 after re-deriving them (table 3f044f23ff9e, LABELS 65f0b227aea3), and confirmed that the background-iteration closure uses only the sum lemma.
- **Specs:** spec_p14bp_r7 is updated to LF f9aee603cdc7 and Cauchy 785c3a36fed5. Definition check: 0 conflicts (9 allowed). No line in its extracts changed.

Written 2026-11-09 12:36.
