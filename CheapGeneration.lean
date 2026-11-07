import Mathlib
import CertificationLean.Core

/-!
  Algebraic and order-theoretic core of Propositions 2--4.

  The article's comparative statics hold with reward slopes, credibility and
  the review architecture fixed.  The first group of results below verifies
  the quotient-rule expressions algebraically; a separate calculus wrapper
  can use them as the final simplification step of a `HasDerivAt` proof.
-/

namespace CertificationLean

noncomputable section

/-! ## Proposition 2: quotient-rule normal forms and signs -/

/-- The quotient-rule normal form for `∂x*/∂κ`. -/
theorem xStar_kappa_rhs_normal_form
    {theta chi kap rho A B : ℝ} (hD : D chi kap rho ≠ 0) :
    rho * yStar theta chi kap rho A B / D chi kap rho =
      theta * rho * (chi * B - rho * A) / (D chi kap rho) ^ 2 := by
  simp only [yStar]
  field_simp [hD]
  ring

/-- The quotient-rule normal form for `∂y*/∂κ`. -/
theorem yStar_kappa_rhs_normal_form
    {theta chi kap rho A B : ℝ} (hD : D chi kap rho ≠ 0) :
    -chi * yStar theta chi kap rho A B / D chi kap rho =
      -theta * chi * (chi * B - rho * A) / (D chi kap rho) ^ 2 := by
  simp only [yStar]
  field_simp [hD]
  ring

/-- The quotient-rule normal form for `∂x*/∂χ`. -/
theorem xStar_chi_rhs_normal_form
    {theta chi kap rho A B : ℝ} (hD : D chi kap rho ≠ 0) :
    -kap * xStar theta chi kap rho A B / D chi kap rho =
      -theta * kap * (kap * A - rho * B) / (D chi kap rho) ^ 2 := by
  simp only [xStar]
  field_simp [hD]
  ring

/-- The quotient-rule normal form for `∂y*/∂χ`. -/
theorem yStar_chi_rhs_normal_form
    {theta chi kap rho A B : ℝ} (hD : D chi kap rho ≠ 0) :
    rho * xStar theta chi kap rho A B / D chi kap rho =
      theta * rho * (kap * A - rho * B) / (D chi kap rho) ^ 2 := by
  simp only [xStar]
  field_simp [hD]
  ring

/-- Sign of the `∂x*/∂κ` right-hand side under the article's interior
assumptions. -/
theorem xStar_kappa_rhs_nonneg
    {chi kap rho y : ℝ}
    (hD : 0 < D chi kap rho) (hrho : 0 ≤ rho) (hy : 0 ≤ y) :
    0 ≤ rho * y / D chi kap rho := by
  exact div_nonneg (mul_nonneg hrho hy) (le_of_lt hD)

/-- Sign of the `∂y*/∂κ` right-hand side under the article's interior
assumptions. -/
theorem yStar_kappa_rhs_neg
    {chi kap rho y : ℝ}
    (hD : 0 < D chi kap rho) (hchi : 0 < chi) (hy : 0 < y) :
    -chi * y / D chi kap rho < 0 := by
  have hnum : -chi * y < 0 := by
    nlinarith [mul_pos hchi hy]
  exact div_neg_of_neg_of_pos hnum hD

/-- Sign of the `∂x*/∂χ` right-hand side under the article's interior
assumptions. -/
theorem xStar_chi_rhs_neg
    {chi kap rho x : ℝ}
    (hD : 0 < D chi kap rho) (hkap : 0 < kap) (hx : 0 < x) :
    -kap * x / D chi kap rho < 0 := by
  have hnum : -kap * x < 0 := by
    nlinarith [mul_pos hkap hx]
  exact div_neg_of_neg_of_pos hnum hD

/-- Sign of the `∂y*/∂χ` right-hand side under the article's interior
assumptions. -/
theorem yStar_chi_rhs_nonneg
    {chi kap rho x : ℝ}
    (hD : 0 < D chi kap rho) (hrho : 0 ≤ rho) (hx : 0 ≤ x) :
    0 ≤ rho * x / D chi kap rho := by
  exact div_nonneg (mul_nonneg hrho hx) (le_of_lt hD)

/-- The algebraic combination of the two κ-derivative expressions gives the
output expression in Proposition 2. -/
theorem output_kappa_from_effort_derivatives
    {theta chi kap rho lam A B : ℝ} :
    rho * yStar theta chi kap rho A B / D chi kap rho -
        lam * (-chi * yStar theta chi kap rho A B / D chi kap rho) =
      (rho + lam * chi) * yStar theta chi kap rho A B / D chi kap rho := by
  ring

/-- The algebraic combination of the two χ-derivative expressions gives the
output expression in Proposition 2. -/
theorem output_chi_from_effort_derivatives
    {theta chi kap rho lam A B : ℝ} :
    -kap * xStar theta chi kap rho A B / D chi kap rho -
        lam * (rho * xStar theta chi kap rho A B / D chi kap rho) =
      -(kap + lam * rho) * xStar theta chi kap rho A B / D chi kap rho := by
  ring

/-- The nonnegative-sign part of Proposition 2 for the κ derivative. -/
theorem output_kappa_rhs_nonneg
    {chi kap rho lam y : ℝ}
    (hD : 0 < D chi kap rho) (hrho : 0 ≤ rho) (hlam : 0 ≤ lam)
    (hchi : 0 ≤ chi) (hy : 0 ≤ y) :
    0 ≤ (rho + lam * chi) * y / D chi kap rho := by
  apply div_nonneg
  · exact mul_nonneg (add_nonneg hrho (mul_nonneg hlam hchi)) hy
  · exact le_of_lt hD

/-- The strict sign part of Proposition 2 for the χ (and hence `chi_X`)
derivative. -/
theorem output_chi_rhs_neg
    {chi kap rho lam x : ℝ}
    (hD : 0 < D chi kap rho) (hkap : 0 < kap) (hlam : 0 ≤ lam)
    (hrho : 0 ≤ rho) (hx : 0 < x) :
    -(kap + lam * rho) * x / D chi kap rho < 0 := by
  have hcoef : 0 < kap + lam * rho :=
    add_pos_of_pos_of_nonneg hkap (mul_nonneg hlam hrho)
  have hnum : -(kap + lam * rho) * x < 0 := by
    nlinarith [mul_pos hcoef hx]
  exact div_neg_of_neg_of_pos hnum hD

/-! ## Proposition 3: the value of certification -/

/-- Subtracting the two κ comparative statics yields Proposition 3's first
right-hand side. -/
theorem advantage_kappa_rhs
    {theta chi kap rho lam Am Bm Al Bl : ℝ} :
    (rho + lam * chi) * yStar theta chi kap rho Am Bm / D chi kap rho -
      (rho + lam * chi) * yStar theta chi kap rho Al Bl / D chi kap rho =
    (rho + lam * chi) / D chi kap rho *
      (yStar theta chi kap rho Am Bm - yStar theta chi kap rho Al Bl) := by
  ring

/-- Subtracting the two χ comparative statics yields Proposition 3's second
right-hand side. -/
theorem advantage_chi_rhs
    {theta chi kap rho lam Am Bm Al Bl : ℝ} :
    -(kap + lam * rho) * xStar theta chi kap rho Am Bm / D chi kap rho -
      (-(kap + lam * rho) * xStar theta chi kap rho Al Bl / D chi kap rho) =
    -(kap + lam * rho) / D chi kap rho *
      (xStar theta chi kap rho Am Bm - xStar theta chi kap rho Al Bl) := by
  ring

/-- If the κ right-hand side is positive, lowering κ raises the advantage of
regime `m` locally.  This is the sign interpretation used in Proposition 3. -/
theorem advantage_kappa_rhs_pos_iff
    {chi kap rho lam ym yl : ℝ}
    (hD : 0 < D chi kap rho) (hcoef : 0 < rho + lam * chi) :
    0 < (rho + lam * chi) / D chi kap rho * (ym - yl) ↔ yl < ym := by
  have hscale : 0 < (rho + lam * chi) / D chi kap rho :=
    div_pos hcoef hD
  constructor
  · intro h
    rcases mul_pos_iff.mp h with hp | hn
    · exact sub_pos.mp hp.2
    · exact False.elim ((not_lt_of_ge (le_of_lt hscale)) hn.1)
  · intro h
    exact mul_pos hscale (sub_pos.mpr h)

/-! ## Proposition 4: the look-through bar -/

/-- The look-through threshold in Corollary 1. -/
def lookThroughThreshold (kap chi rho lam : ℝ) : ℝ :=
  (kap + lam * rho) / (rho + lam * chi)

/-- The presentation-cost cutoff in Proposition 4(b). -/
def kappaHat (chi rho lam sx sy : ℝ) : ℝ :=
  (rho + lam * chi) * (sy / sx) - lam * rho

/-- The look-through threshold is strictly increasing in the cost of polish. -/
theorem lookThroughThreshold_strictMono_kappa
    {kap₁ kap₂ chi rho lam : ℝ}
    (hden : 0 < rho + lam * chi) :
    lookThroughThreshold kap₁ chi rho lam < lookThroughThreshold kap₂ chi rho lam ↔
      kap₁ < kap₂ := by
  unfold lookThroughThreshold
  rw [div_lt_div_iff₀ hden hden]
  nlinarith

/-- The threshold is weakly decreasing in substantive-execution cost when
`lam` is nonnegative. -/
theorem lookThroughThreshold_antitone_chi
    {kap chi₁ chi₂ rho lam : ℝ}
    (hnum : 0 ≤ kap + lam * rho) (hlam : 0 ≤ lam)
    (hchi : chi₁ ≤ chi₂)
    (hden₁ : 0 < rho + lam * chi₁) (hden₂ : 0 < rho + lam * chi₂) :
    lookThroughThreshold kap chi₂ rho lam ≤ lookThroughThreshold kap chi₁ rho lam := by
  unfold lookThroughThreshold
  rw [div_le_div_iff₀ hden₂ hden₁]
  have hgap : 0 ≤ rho + lam * chi₂ - (rho + lam * chi₁) := by
    have hmul : 0 ≤ lam * (chi₂ - chi₁) :=
      mul_nonneg hlam (sub_nonneg.mpr hchi)
    nlinarith
  have hprod : 0 ≤ (kap + lam * rho) *
      (rho + lam * chi₂ - (rho + lam * chi₁)) :=
    mul_nonneg hnum hgap
  nlinarith

/-- The decrease in the threshold is strict when `lam` is positive. -/
theorem lookThroughThreshold_strictAnti_chi
    {kap chi₁ chi₂ rho lam : ℝ}
    (hnum : 0 < kap + lam * rho) (hlam : 0 < lam)
    (hchi : chi₁ < chi₂)
    (hden₁ : 0 < rho + lam * chi₁) (hden₂ : 0 < rho + lam * chi₂) :
    lookThroughThreshold kap chi₂ rho lam < lookThroughThreshold kap chi₁ rho lam := by
  unfold lookThroughThreshold
  rw [div_lt_div_iff₀ hden₂ hden₁]
  have hgap : 0 < rho + lam * chi₂ - (rho + lam * chi₁) := by
    have hmul : 0 < lam * (chi₂ - chi₁) :=
      mul_pos hlam (sub_pos.mpr hchi)
    nlinarith
  have hprod : 0 < (kap + lam * rho) *
      (rho + lam * chi₂ - (rho + lam * chi₁)) :=
    mul_pos hnum hgap
  nlinarith

/-- If reviewers do not reward polish, the look-through condition holds at
every admissible cost of polish. -/
theorem look_through_of_nonpositive_polish_sensitivity
    {kap chi rho lam sx sy : ℝ}
    (hsy : sy ≤ 0) (hsx : 0 < sx)
    (hnum : 0 < kap + lam * rho) (hden : 0 < rho + lam * chi) :
    sy / sx < lookThroughThreshold kap chi rho lam := by
  have hleft : sy / sx ≤ 0 :=
    (div_le_iff₀ hsx).2 (by nlinarith)
  have hright : 0 < lookThroughThreshold kap chi rho lam :=
    div_pos hnum hden
  linarith

/-- Proposition 4(b): the look-through condition is exactly a lower bound on
the cost of polish. -/
theorem look_through_iff_kappa_gt_hat
    {kap chi rho lam sx sy : ℝ}
    (hsx : 0 < sx) (hden : 0 < rho + lam * chi) :
    sy / sx < lookThroughThreshold kap chi rho lam ↔
      kappaHat chi rho lam sx sy < kap := by
  change sy / sx < (kap + lam * rho) / (rho + lam * chi) ↔ _
  rw [← look_through_nondivided hsx hden]
  unfold kappaHat
  constructor
  · intro h
    have hdiv : (rho + lam * chi) * sy / sx < kap + lam * rho :=
      (div_lt_iff₀ hsx).2 (by nlinarith)
    calc
      (rho + lam * chi) * (sy / sx) - lam * rho =
          (rho + lam * chi) * sy / sx - lam * rho := by
            field_simp [ne_of_gt hsx]
            ring
      _ < (kap + lam * rho) - lam * rho := by linarith
      _ = kap := by ring
  · intro h
    have hdiv : (rho + lam * chi) * sy / sx < kap + lam * rho := by
      have hrewrite : (rho + lam * chi) * sy / sx =
          (rho + lam * chi) * (sy / sx) := by
        field_simp [ne_of_gt hsx]
        ring
      rw [hrewrite]
      linarith
    have hmul : (rho + lam * chi) * sy < (kap + lam * rho) * sx :=
      (div_lt_iff₀ hsx).1 hdiv
    nlinarith

/-- Cheaper execution (lower `chi`) weakly lowers the presentation cutoff. -/
theorem kappaHat_monotone_chi
    {chi₁ chi₂ rho lam sx sy : ℝ}
    (hchi : chi₁ ≤ chi₂) (hlam : 0 ≤ lam)
    (hsx : 0 < sx) (hsy : 0 < sy) :
    kappaHat chi₁ rho lam sx sy ≤ kappaHat chi₂ rho lam sx sy := by
  unfold kappaHat
  have hgap : 0 ≤ chi₂ - chi₁ := sub_nonneg.mpr hchi
  have hratio : 0 ≤ sy / sx := le_of_lt (div_pos hsy hsx)
  have hprod : 0 ≤ lam * (chi₂ - chi₁) * (sy / sx) :=
    mul_nonneg (mul_nonneg hlam hgap) hratio
  nlinarith

/-- The cutoff movement is strict for strictly positive execution and polish
sensitivities. -/
theorem kappaHat_strictMono_chi
    {chi₁ chi₂ rho lam sx sy : ℝ}
    (hchi : chi₁ < chi₂) (hlam : 0 < lam)
    (hsx : 0 < sx) (hsy : 0 < sy) :
    kappaHat chi₁ rho lam sx sy < kappaHat chi₂ rho lam sx sy := by
  unfold kappaHat
  have hgap : 0 < chi₂ - chi₁ := sub_pos.mpr hchi
  have hratio : 0 < sy / sx := div_pos hsy hsx
  have hprod : 0 < lam * (chi₂ - chi₁) * (sy / sx) :=
    mul_pos (mul_pos hlam hgap) hratio
  nlinarith

end

end CertificationLean
