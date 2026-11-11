# Non-Gaussianity Note: Triage and Pre-Check

Owner: BETA session. Note: `WILSON_IT1_NON_GAUSSIANITY_2026_11_11.md`.

## Status (2026-11-11 03:11)

- Note SHA 124102a7911b, 25,105 characters, 6 sections, tags #NG.0–#NG6.3.
- No referee round yet; none launched (needs the user's go). A full round needs the 25k split: part a = header, §§1–4; part b = §§5–6, with §§1–4 as context.
- Open: (O1) = (O1a) + (O1b), #NG.2–#NG.2-2.

## Pre-check (03:11)

- Every line of the note re-read after the rewrite.
- Every cited tag resolves (129 tags) against: GL b55baaef58e9 (live, own), NV a23c5c204987, PF 3137f5cade3e, continuum note e11a4286a383, Cauchy b90f03322044, map ea2d3fdca669, table c571f2502afe, V4 0f859f2d3652 (snapshots in the scratchpad's snap folder).
- Table and map changed since the earlier snapshots (3e9dd1981ea0, 5c5203be2b03): diffs read; no cited row changed (#T1.2, #T3.27-0, #T3.33, #T4.52, #T10.2, #T12.14, #T12.16, #MOMST.76, #MOMST.82, #MD2.0.5.40).
- V4 changed (64c07217fa40 to 0f859f2d3652): V4 (H1) still reads "compact connected simple", and cor:main-leading-size still defines Lip_χ by ‖π_χ(g) − π_χ(h)‖_op ≤ Lip_χ‖g − h‖_op.
- No line over 600 characters.
- Each cited line read against the claim it supports:
  - #GL2.6, #GL2.7-2, #GL2.8-2, #GL4.6, #GL5.2-6, #GL5.5-1, #GL5.5-2, #MD2.0.5.40 (ι_{T,k} = Lι_{T,k+1}), #CP.13, #NK.4, #ND.2.3, #ND.5.3-0: Lemma E♯ and its size.
  - #NV.1–#NV.1-2.1, #NV.3, #NV.4-2–#NV.4-4, #NV.5-2–#NV.5-2.1, #NV.9, #GL9.8–#GL9.8-4, #ND.7.1: the stopping-scale form and λ^ng.
  - #PF4.2-0–#PF4.4-4, #PF4.5-2, #MOMST.74–#MOMST.84: the enlarged typical event. #MOMST.82 has Hol_{C^{(k)}}(M^kU) = Π_ie^{iE_{c_i}}T_{c_i}(U) with E_c ∈ 𝔤, so the telescoping bound needs no exponential (GL's 1.06 is not needed here).
  - #PF3.2-3–#PF3.2-9b, #T4.52, #GL6.5–#GL6.5-2: the near part on ℓ₀.
  - #GL9.1–#GL9.7-2, #GL7.1: levels, normalisations, families, §7's conditions.
  - #ND.5.4–#ND.5.4-2, #T12.14: ι^{ℓ₀} and ρ_k.

## Repairs made during the pre-check

- Symbol clashes with table rows, renamed:
  - R_n (#T12.7-29 and others: radii R_n) to 𝖱_n.
  - P_k (tube projection, bond counts P_k(C)) to 𝖯_k.
  - a_R (#T12.24-1-4) to 𝖺_𝖱.
  - n_R (#T4.29-6) to n(𝖱).
  - r_S (#T4.47, #T12.5) to 𝗋_S.
  - h_m (#T12.7) to 𝗁_𝗆.
  - ι in Lemma E♯ (#T12.35's RW1 ι := ι_{T,1}) to ι_{T,K′} written out.
  - ι_C to the existing ι^{ℓ₀}_C (#PF4.2-0-1, #GL8.6).
  - I_a to 𝖨_a.
  - Gaussian vector Φ (table Φ_ℓ(X), Φ^⋆) to 𝖷.
  - 1-form A (Wilson action A) to 𝖡.
  - F (NV's F_𝔇) to 𝖥.
  - Charge e (Euler's e in the same lines) to 𝗀.
  - Lattice Λ_a, side T, spacing a in §4 to 𝕋_ε, 𝖳, ε, as Λ_a clashed with Λ_{𝖨_a} and a with the index a.
  - M_C to 𝖬_C.
  - Directions ρ, σ in §4 (σ_C, σ_ng) to α ∉ {μ, ν}.
- New symbols, all free in table c571f2502afe: 𝔜, 𝔶_S, 𝔶_k, 𝔶^{ℓ₀}_S, c^G_k, c^F_k, D^F, B^♯_E, B^♯, B^♯_S, T_ng, ε_ng, 𝒱_ng, h^ng_C, σ_C, σ_ng, λ^ng, 𝖺_𝖱, 𝗋_S, 𝗋′_S, 𝖬_C, and the sans-serif diagram names.
- Proposition K(ii), Theorem P and Proposition R gained "Under #GL7.1's conditions for the five diagrams": #GL9.8 holds under §7's conditions, which include constants fixed after the family (L ≥ L₀(𝒞), #GL6.6).
- Theorem P: σ_ng := 3ḡ⁴ + limsup_Kσ_{𝖨₀}, with the order bound uniform in K, so that "let K → ∞" is valid.
- Near part (#NG5.5-3–#NG5.5-6) re-derived on ℓ₀ from #PF3.2-4–#PF3.2-6 with ℓ₀'s majorants 𝖬_a = Π_n(1 + ν_n) and N^{nr} of #PF3.2-9. On ℓ₀ there are no large-field components, and the local terms are constants, so N^{LF} and the δ̄_D terms are absent. GL's rate e^{−c_dP_{K′}/(2Λ̄)} is now cited, with its bound e^{−c_dr_{K′}}.
- ι^{ℓ₀}_C order (#NG5.5-10): the wrap term of #ND.5.4-2 is stated and bounded, with j(C) = j_q by #GL9.1-1.
- Lemma F: hypothesis 4t ≤ 𝖳 added for k = 3.
- #NG2.1-1 examples: "generalised free fields" dropped; the continuum case is stated with L² limits of Riemann sums.
- #NG.1-1: the conditional sentence replaced by "is open: it follows from (O1) by #NG6.3".

## Messages

- To the two-loops session, the PF and NV owner: sent 2026-11-11 (see below).
- To the table session: announced the new rows (list above), to be entered after their reply; no table edit by this session.

## For the user

- Route: the witness compares with abelian Gaussian charge models and their limits (#NG2.3). A 𝔤-valued Gaussian field with path-ordered holonomies is not covered.
- Referee rounds for GL, TL and NG need the user's go.
- (O1) open.
