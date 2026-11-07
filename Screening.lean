import Mathlib

/-!
# Screening, capacity, and triage

This file formalizes the algebraic core of Section 5 of
*Certification under Cheap Generation*.  The paper uses differential notation.
Here, the differential quantities are explicit real-valued arguments.  The
identities below are therefore fully checked algebraically; an application that
identifies these quantities with derivatives must separately establish the
corresponding differentiability assumptions.
-/

namespace CertificationLean

noncomputable section

/-! ## Review load, capacity, and delay -/

def humanLoad (delta zeta Nv Nf Nm : ℝ) : ℝ :=
  Nv + (1 - delta) * Nf + (1 - zeta) * Nm

def endorsedJunk (psiF psiM delta zeta Nf Nm : ℝ) : ℝ :=
  psiF * (1 - delta) * Nf + psiM * (1 - zeta) * Nm

def endorsementCredibility (Nv psiF psiM delta zeta Nf Nm : ℝ) : ℝ :=
  Nv / (Nv + endorsedJunk psiF psiM delta zeta Nf Nm)

def validationCredibility (Nv Nf Nm delta : ℝ) : ℝ :=
  (Nv + Nm) / (Nv + Nm + (1 - delta) * Nf)

def serviceRate (attention timePerPaper intensity : ℝ) : ℝ :=
  attention / (timePerPaper * intensity)

def reviewDelay (service load : ℝ) : ℝ :=
  1 / (service - load)

def reviewFrontier (attention timePerPaper load delayBound : ℝ) : ℝ :=
  attention / (timePerPaper * (load + 1 / delayBound))

/-! ### Lemma 2: review frontier -/

theorem review_frontier_iff
    {attention timePerPaper load delayBound intensity : ℝ}
    (hattention : 0 < attention) (htime : 0 < timePerPaper)
    (hload : 0 ≤ load) (hdelay : 0 < delayBound)
    (hintensity : 0 < intensity) :
    load + 1 / delayBound ≤ serviceRate attention timePerPaper intensity ↔
      intensity ≤ reviewFrontier attention timePerPaper load delayBound := by
  have hinv : 0 < 1 / delayBound := one_div_pos.mpr hdelay
  have hsum : 0 < load + 1 / delayBound :=
    add_pos_of_nonneg_of_pos hload hinv
  have hdenI : 0 < timePerPaper * intensity := mul_pos htime hintensity
  have hdenF : 0 < timePerPaper * (load + 1 / delayBound) :=
    mul_pos htime hsum
  constructor
  · intro hcapacity
    have hproduct :
        (load + 1 / delayBound) * (timePerPaper * intensity) ≤ attention :=
      (le_div_iff₀ hdenI).mp hcapacity
    apply (le_div_iff₀ hdenF).mpr
    calc
      intensity * (timePerPaper * (load + 1 / delayBound)) =
          (load + 1 / delayBound) * (timePerPaper * intensity) := by ring
      _ ≤ attention := hproduct
  · intro hfrontier
    have hproduct :
        intensity * (timePerPaper * (load + 1 / delayBound)) ≤ attention :=
      (le_div_iff₀ hdenF).mp hfrontier
    apply (le_div_iff₀ hdenI).mpr
    calc
      (load + 1 / delayBound) * (timePerPaper * intensity) =
          intensity * (timePerPaper * (load + 1 / delayBound)) := by ring
      _ ≤ attention := hproduct

theorem delay_le_iff_capacity
    {service load delayBound : ℝ}
    (hstable : load < service) (hdelay : 0 < delayBound) :
    reviewDelay service load ≤ delayBound ↔
      load + 1 / delayBound ≤ service := by
  have hgap : 0 < service - load := sub_pos.mpr hstable
  constructor
  · intro hreview
    have hproduct : 1 ≤ delayBound * (service - load) :=
      (div_le_iff₀ hgap).mp (by simpa [reviewDelay] using hreview)
    have hproduct' : 1 ≤ (service - load) * delayBound := by
      nlinarith [hproduct]
    have hinv : 1 / delayBound ≤ service - load :=
      (div_le_iff₀ hdelay).mpr hproduct'
    linarith
  · intro hcapacity
    have hinv : 1 / delayBound ≤ service - load := by
      linarith
    have hproduct' : 1 ≤ (service - load) * delayBound :=
      (div_le_iff₀ hdelay).mp hinv
    have hproduct : 1 ≤ delayBound * (service - load) := by
      nlinarith [hproduct']
    simpa [reviewDelay] using (div_le_iff₀ hgap).mpr hproduct

/-! ### Lemma 3: net-capacity accounting -/

def loadDifferential
    (delta zeta deltaPrime Nf Nm dr dzeta dNv dNf dNm : ℝ) : ℝ :=
  -deltaPrime * Nf * dr - Nm * dzeta
    + (1 - delta) * dNf + (1 - zeta) * dNm + dNv

def serviceDifferential (service timePerPaper timePrime dr : ℝ) : ℝ :=
  -service * (timePrime / timePerPaper) * dr

def netCapacity
    (service timePerPaper timePrime delta zeta deltaPrime Nf Nm dr dzeta dNv dNf dNm : ℝ) : ℝ :=
  -service * (timePrime / timePerPaper) * dr + deltaPrime * Nf * dr + Nm * dzeta
    - (1 - delta) * dNf - (1 - zeta) * dNm - dNv

def delayDifferential (delay dService dLoad : ℝ) : ℝ :=
  delay ^ 2 * (dLoad - dService)

theorem net_capacity_as_service_minus_load
    (service timePerPaper timePrime delta zeta deltaPrime Nf Nm dr dzeta dNv dNf dNm : ℝ) :
    netCapacity service timePerPaper timePrime delta zeta deltaPrime Nf Nm dr dzeta dNv dNf dNm =
      serviceDifferential service timePerPaper timePrime dr -
        loadDifferential delta zeta deltaPrime Nf Nm dr dzeta dNv dNf dNm := by
  simp [netCapacity, serviceDifferential, loadDifferential]
  ring

theorem delay_differential_identity
    (delay service timePerPaper timePrime delta zeta deltaPrime Nf Nm dr dzeta dNv dNf dNm : ℝ) :
    delayDifferential delay
        (serviceDifferential service timePerPaper timePrime dr)
        (loadDifferential delta zeta deltaPrime Nf Nm dr dzeta dNv dNf dNm) =
      -delay ^ 2 *
        netCapacity service timePerPaper timePrime delta zeta deltaPrime Nf Nm dr dzeta dNv dNf dNm := by
  rw [net_capacity_as_service_minus_load]
  simp [delayDifferential]
  ring

def logFrontierDifferential
    (timePerPaper timePrime dr dLoad load delayBound : ℝ) : ℝ :=
  -(timePrime / timePerPaper) * dr - dLoad / (load + 1 / delayBound)

theorem log_frontier_differential_identity
    {service timePerPaper timePrime dr dLoad load delayBound : ℝ}
    (htime : timePerPaper ≠ 0) (hservice : service ≠ 0)
    (hcapacity : load + 1 / delayBound = service) :
    logFrontierDifferential timePerPaper timePrime dr dLoad load delayBound =
      (serviceDifferential service timePerPaper timePrime dr - dLoad) / service := by
  simp only [logFrontierDifferential, serviceDifferential]
  rw [hcapacity]
  field_simp [htime, hservice]

/-! ## Complementarity (Proposition 5) -/

def gammaPrimeFormula (psiF Nv Nf deltaPrime endorsedPool : ℝ) : ℝ :=
  psiF * Nv * Nf * deltaPrime / endorsedPool ^ 2

def lookThroughIndex (kappa lambda rho chi alphaE betaE : ℝ) : ℝ :=
  (kappa + lambda * rho) * alphaE + (rho + lambda * chi) * betaE

def crossEffect (theta D gammaPrime index : ℝ) : ℝ :=
  theta * gammaPrime / D * index

theorem gamma_prime_nonneg
    {psiF Nv Nf deltaPrime endorsedPool : ℝ}
    (hpsiF : 0 ≤ psiF) (hNv : 0 ≤ Nv) (hNf : 0 ≤ Nf)
    (hdelta : 0 ≤ deltaPrime) :
    0 ≤ gammaPrimeFormula psiF Nv Nf deltaPrime endorsedPool := by
  unfold gammaPrimeFormula
  exact div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hpsiF hNv) hNf) hdelta)
    (sq_nonneg endorsedPool)

theorem gamma_prime_pos
    {psiF Nv Nf deltaPrime endorsedPool : ℝ}
    (hpsiF : 0 < psiF) (hNv : 0 < Nv) (hNf : 0 < Nf)
    (hdelta : 0 < deltaPrime) (hpool : 0 < endorsedPool) :
    0 < gammaPrimeFormula psiF Nv Nf deltaPrime endorsedPool := by
  unfold gammaPrimeFormula
  exact div_pos
    (mul_pos (mul_pos (mul_pos hpsiF hNv) hNf) hdelta)
    (pow_pos hpool 2)

theorem cross_effect_pos_iff
    {theta D gammaPrime index : ℝ}
    (htheta : 0 < theta) (hD : 0 < D) (hgamma : 0 < gammaPrime) :
    0 < crossEffect theta D gammaPrime index ↔ 0 < index := by
  change 0 < theta * gammaPrime / D * index ↔ 0 < index
  have hfactor : 0 < theta * gammaPrime / D :=
    div_pos (mul_pos htheta hgamma) hD
  constructor
  · intro hcross
    rcases (mul_pos_iff.mp hcross) with hgood | hbad
    · exact hgood.2
    · exact False.elim ((not_lt_of_ge (le_of_lt hfactor)) hbad.1)
  · intro hindex
    exact mul_pos hfactor hindex

def attentionLogSlope
    (timePerPaper timePrime deltaPrime Nf capacityDenom : ℝ) : ℝ :=
  -(timePrime / timePerPaper) + deltaPrime * Nf / capacityDenom

theorem attention_log_slope_nonneg
    {timePerPaper timePrime deltaPrime Nf capacityDenom : ℝ}
    (htime : 0 < timePerPaper) (htimePrime : timePrime ≤ 0)
    (hdelta : 0 ≤ deltaPrime) (hNf : 0 ≤ Nf)
    (hdenom : 0 < capacityDenom) :
    0 ≤ attentionLogSlope timePerPaper timePrime deltaPrime Nf capacityDenom := by
  unfold attentionLogSlope
  apply add_nonneg
  · apply neg_nonneg.mpr
    exact div_nonpos_of_nonpos_of_nonneg htimePrime (le_of_lt htime)
  · exact div_nonneg (mul_nonneg hdelta hNf) (le_of_lt hdenom)

/-! ## Screening versus triage (Proposition 6) -/

def marginalRemoval (N elasticity : ℝ) : ℝ :=
  N * (1 + elasticity)

def delayTriageRatio (Nf etaF Nm etaM : ℝ) : ℝ :=
  marginalRemoval Nm etaM / marginalRemoval Nf etaF

def credibilityTriageRatio (psiF psiM Nf etaF Nm etaM : ℝ) : ℝ :=
  (psiM * marginalRemoval Nm etaM) /
    (psiF * marginalRemoval Nf etaF)

theorem credibility_ratio_eq_scaled_delay_ratio
    {psiF psiM Nf etaF Nm etaM : ℝ}
    (hpsiF : psiF ≠ 0)
    (hremoval : marginalRemoval Nf etaF ≠ 0) :
    credibilityTriageRatio psiF psiM Nf etaF Nm etaM =
      (psiM / psiF) * delayTriageRatio Nf etaF Nm etaM := by
  simp [credibilityTriageRatio, delayTriageRatio]
  field_simp [hpsiF, hremoval]

theorem marginal_removal_pos
    {N elasticity : ℝ}
    (hN : 0 < N) (helasticity : 0 ≤ elasticity) :
    0 < marginalRemoval N elasticity := by
  unfold marginalRemoval
  exact mul_pos hN (by linarith)

end

end CertificationLean
