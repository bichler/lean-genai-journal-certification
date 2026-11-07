import Mathlib

/-!
  Core algebra for "Certification under Cheap Generation".

  This file formalises the deterministic, interior part of the model.  It does
  not formalise empirical assumptions or the interpretation of the parameters:
  Lean checks the stated conclusions conditional on the hypotheses below.
-/

namespace CertificationLean

noncomputable section

/-- The determinant of the author's quadratic cost matrix. -/
def D (chi kap rho : ℝ) : ℝ := chi * kap - rho ^ 2

/-- The quadratic part of the author's cost, before division by `2 * theta`. -/
def quadratic (chi kap rho x y : ℝ) : ℝ :=
  chi * x ^ 2 + 2 * rho * x * y + kap * y ^ 2

/-- Utility apart from the effort-independent visibility term. -/
def utility (theta chi kap rho A B x y : ℝ) : ℝ :=
  A * x + B * y - quadratic chi kap rho x y / (2 * theta)

/-- Optimal substantive effort in the interior solution. -/
def xStar (theta chi kap rho A B : ℝ) : ℝ :=
  theta * (kap * A - rho * B) / D chi kap rho

/-- Optimal presentation effort in the interior solution. -/
def yStar (theta chi kap rho A B : ℝ) : ℝ :=
  theta * (chi * B - rho * A) / D chi kap rho

/-- Net epistemic output at a pair of effort choices. -/
def effortOutput (lam x y : ℝ) : ℝ := x - lam * y

/-- Output per unit of author capability in the interior solution. -/
def q (chi kap rho lam A B : ℝ) : ℝ :=
  ((kap + lam * rho) * A - (rho + lam * chi) * B) / D chi kap rho

/-- Net epistemic output in the interior solution. -/
def output (theta chi kap rho lam A B : ℝ) : ℝ :=
  theta * q chi kap rho lam A B

/-- The effort-dependent part of indirect utility in the interior solution. -/
def phi (chi kap rho A B : ℝ) : ℝ :=
  (kap * A ^ 2 - 2 * rho * A * B + chi * B ^ 2) /
    (2 * D chi kap rho)

/-- The first-order conditions hold at the proposed interior solution. -/
theorem foc_at_star
    {theta chi kap rho A B : ℝ}
    (hD : 0 < D chi kap rho) :
    chi * xStar theta chi kap rho A B + rho * yStar theta chi kap rho A B = theta * A
      ∧ rho * xStar theta chi kap rho A B + kap * yStar theta chi kap rho A B = theta * B := by
  have hD0 : chi * kap - rho ^ 2 ≠ 0 := by
    simpa [D] using ne_of_gt hD
  constructor <;> simp only [xStar, yStar] <;> field_simp [hD0] <;>
    simp [D] <;> ring

/-- Completing the square for the quadratic cost. -/
theorem quadratic_complete_square
    {chi kap rho x y : ℝ} (hchi : chi ≠ 0) :
    quadratic chi kap rho x y =
      chi * (x + (rho / chi) * y) ^ 2 + (D chi kap rho / chi) * y ^ 2 := by
  simp only [quadratic, D]
  field_simp [hchi]
  ring_nf

/-- Positive definiteness of the quadratic cost matrix, in the form needed below. -/
theorem quadratic_nonneg
    {chi kap rho x y : ℝ}
    (hchi : 0 < chi) (hD : 0 < D chi kap rho) :
    0 ≤ quadratic chi kap rho x y := by
  rw [quadratic_complete_square (ne_of_gt hchi)]
  apply add_nonneg
  · exact mul_nonneg (le_of_lt hchi) (sq_nonneg _)
  · exact mul_nonneg (le_of_lt (div_pos hD hchi)) (sq_nonneg _)

/-- Utility at the proposed optimum exceeds utility at any effort vector by a
non-negative quadratic distance. -/
theorem utility_gap
    {theta chi kap rho A B x y : ℝ}
    (htheta : 0 < theta) (hD : 0 < D chi kap rho) :
    utility theta chi kap rho A B (xStar theta chi kap rho A B) (yStar theta chi kap rho A B)
        - utility theta chi kap rho A B x y =
      quadratic chi kap rho
          (x - xStar theta chi kap rho A B)
          (y - yStar theta chi kap rho A B) / (2 * theta) := by
  have htheta0 : theta ≠ 0 := ne_of_gt htheta
  have hD0 : D chi kap rho ≠ 0 := ne_of_gt hD
  have hdet : chi * kap - rho ^ 2 ≠ 0 := by
    simpa [D] using hD0
  simp only [utility, xStar, yStar, quadratic]
  field_simp [htheta0, hdet]
  simp [D]
  ring_nf

/-- Lemma 1: the proposed effort pair is globally optimal under the positive
definiteness and positive-capability assumptions. -/
theorem star_is_maximum
    {theta chi kap rho A B x y : ℝ}
    (htheta : 0 < theta) (hchi : 0 < chi) (hD : 0 < D chi kap rho) :
    utility theta chi kap rho A B x y ≤
      utility theta chi kap rho A B (xStar theta chi kap rho A B) (yStar theta chi kap rho A B) := by
  have hquad : 0 ≤
      quadratic chi kap rho
        (x - xStar theta chi kap rho A B)
        (y - yStar theta chi kap rho A B) :=
    quadratic_nonneg hchi hD
  have hden : 0 < 2 * theta := by linarith
  have hgap : 0 ≤
      utility theta chi kap rho A B (xStar theta chi kap rho A B) (yStar theta chi kap rho A B)
        - utility theta chi kap rho A B x y := by
    rw [utility_gap htheta hD]
    exact div_nonneg hquad (le_of_lt hden)
  linarith

/-- Lemma 1's closed form for net epistemic output. -/
theorem output_at_star
    {theta chi kap rho lam A B : ℝ}
    (hD : D chi kap rho ≠ 0) :
    effortOutput lam (xStar theta chi kap rho A B) (yStar theta chi kap rho A B) =
      output theta chi kap rho lam A B := by
  simp only [effortOutput, xStar, yStar, output, q]
  field_simp [hD]
  ring

/-- Lemma 1's closed form for the effort-dependent indirect utility. -/
theorem utility_at_star
    {theta chi kap rho A B : ℝ}
    (htheta : theta ≠ 0) (hD : D chi kap rho ≠ 0) :
    utility theta chi kap rho A B (xStar theta chi kap rho A B) (yStar theta chi kap rho A B) =
      theta * phi chi kap rho A B := by
  have hdet : chi * kap - rho ^ 2 ≠ 0 := by
    simpa [D] using hD
  simp only [utility, xStar, yStar, phi, quadratic]
  field_simp [htheta, hdet]
  simp [D]
  ring

/-- Algebraic form of the output difference between two regimes. -/
theorem output_difference
    {theta chi kap rho lam Am Bm Al Bl : ℝ}
    (hD : D chi kap rho ≠ 0) :
    output theta chi kap rho lam Am Bm - output theta chi kap rho lam Al Bl =
      theta / D chi kap rho *
        ((kap + lam * rho) * (Am - Al) - (rho + lam * chi) * (Bm - Bl)) := by
  simp only [output, q]
  field_simp [hD]
  ring

/-- Proposition 1: a regime produces more net epistemic output exactly when
its weighted increase in rewards for substance exceeds its weighted increase
in rewards for presentation. -/
theorem regime_compare_iff
    {theta chi kap rho lam Am Bm Al Bl : ℝ}
    (htheta : 0 < theta) (hD : 0 < D chi kap rho) :
    output theta chi kap rho lam Am Bm > output theta chi kap rho lam Al Bl ↔
      (kap + lam * rho) * (Am - Al) > (rho + lam * chi) * (Bm - Bl) := by
  have hscale : 0 < theta / D chi kap rho := div_pos htheta hD
  calc
    output theta chi kap rho lam Am Bm > output theta chi kap rho lam Al Bl ↔
        0 < output theta chi kap rho lam Am Bm -
          output theta chi kap rho lam Al Bl := by
            constructor <;> intro h <;> linarith
    _ ↔ 0 < theta / D chi kap rho *
          ((kap + lam * rho) * (Am - Al) -
            (rho + lam * chi) * (Bm - Bl)) := by
            rw [output_difference (ne_of_gt hD)]
    _ ↔ (kap + lam * rho) * (Am - Al) >
          (rho + lam * chi) * (Bm - Bl) := by
            constructor
            · intro h
              rcases (mul_pos_iff.mp h) with hpos | hneg
              · exact sub_pos.mp hpos.2
              · exact False.elim ((not_lt_of_ge (le_of_lt hscale)) hneg.1)
            · intro h
              exact mul_pos hscale (sub_pos.mpr h)

/-- The easy sufficient case in Proposition 1. -/
theorem regime_compare_of_reward_order
    {theta chi kap rho lam Am Bm Al Bl : ℝ}
    (htheta : 0 < theta) (hD : 0 < D chi kap rho)
    (hkap : 0 < kap) (hlam : 0 ≤ lam) (hrho : 0 ≤ rho) (hchi : 0 ≤ chi)
    (hA : Al < Am) (hB : Bm ≤ Bl) :
    output theta chi kap rho lam Am Bm > output theta chi kap rho lam Al Bl := by
  apply (regime_compare_iff htheta hD).2
  have hleftcoef : 0 < kap + lam * rho := by
    have : 0 ≤ lam * rho := mul_nonneg hlam hrho
    linarith
  have hrightcoef : 0 ≤ rho + lam * chi := by
    exact add_nonneg hrho (mul_nonneg hlam hchi)
  have hleft : 0 < (kap + lam * rho) * (Am - Al) :=
    mul_pos hleftcoef (sub_pos.mpr hA)
  have hright : (rho + lam * chi) * (Bm - Bl) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hrightcoef (sub_nonpos.mpr hB)
  linarith

/-- The non-divided form of Corollary 1's look-through condition. -/
theorem look_through_nondivided
    {kap rho lam chi sx sy : ℝ}
    (hsx : 0 < sx) (hden : 0 < rho + lam * chi) :
    (kap + lam * rho) * sx > (rho + lam * chi) * sy ↔
      sy / sx < (kap + lam * rho) / (rho + lam * chi) := by
  constructor
  · intro h
    apply (div_lt_div_iff₀ hsx hden).2
    nlinarith
  · intro h
    have h' := (div_lt_div_iff₀ hsx hden).1 h
    nlinarith

/-- The article's primitive reviewer sensitivities satisfy the divided
look-through condition exactly when the endorsement contribution to the
output comparison is positive. -/
theorem reviewer_sensitivity_iff_look_through
    {kap rho lam chi V sx sy : ℝ}
    (hV : 0 < V) (hsx : 0 < sx) (hden : 0 < rho + lam * chi) :
    0 < (kap + lam * rho) * (V * sx) +
        (rho + lam * chi) * (-V * sy) ↔
      sy / sx < (kap + lam * rho) / (rho + lam * chi) := by
  have hfactor : 0 < V := hV
  have hrewrite :
      (kap + lam * rho) * (V * sx) +
          (rho + lam * chi) * (-V * sy) =
        V * ((kap + lam * rho) * sx -
          (rho + lam * chi) * sy) := by
    ring
  rw [hrewrite]
  calc
    0 < V * ((kap + lam * rho) * sx -
          (rho + lam * chi) * sy) ↔
        0 < (kap + lam * rho) * sx -
          (rho + lam * chi) * sy := by
            constructor
            · intro h
              rcases (mul_pos_iff.mp h) with hp | hn
              · exact hp.2
              · exact False.elim ((not_lt_of_ge (le_of_lt hfactor)) hn.1)
            · intro h
              exact mul_pos hfactor h
    _ ↔ (kap + lam * rho) * sx > (rho + lam * chi) * sy := by
            constructor <;> intro h <;> linarith
    _ ↔ sy / sx < (kap + lam * rho) / (rho + lam * chi) :=
          look_through_nondivided hsx hden

/-! ## Corollary 1: journal versus platform -/

/-- Reward slope for substance in the platform regime.  The common validation
component is deliberately kept as a free number `AP`; it cancels in the
comparison. -/
def platformA (AP : ℝ) : ℝ := AP

/-- Reward slope for presentation in the platform regime. -/
def platformB (BP : ℝ) : ℝ := BP

/-- Reward slope for substance in the journal regime when the platform and the
journal use the same validation screen. -/
def journalA (AP gamma alphaE e : ℝ) : ℝ := AP + gamma * alphaE * e

/-- Reward slope for presentation in the journal regime. -/
def journalB (BP gamma betaE e : ℝ) : ℝ := BP - gamma * betaE * e

/-- The journal-platform output gap is exactly credibility times review
intensity times the look-through index. -/
theorem journal_platform_output_gap
    {theta chi kap rho lam AP BP gamma alphaE betaE e : ℝ}
    (hD : D chi kap rho ≠ 0) :
    output theta chi kap rho lam
        (journalA AP gamma alphaE e) (journalB BP gamma betaE e) -
      output theta chi kap rho lam (platformA AP) (platformB BP) =
      theta * gamma * e / D chi kap rho *
        ((kap + lam * rho) * alphaE + (rho + lam * chi) * betaE) := by
  simp only [journalA, journalB, platformA, platformB]
  rw [output_difference hD]
  field_simp [hD]
  ring

/-- Corollary 1 in the paper: with a common validation screen, the journal
improves net output iff its reviewers satisfy the look-through condition. -/
theorem journal_beats_platform_iff_look_through
    {theta chi kap rho lam AP BP gamma alphaE betaE e : ℝ}
    (htheta : 0 < theta) (hgamma : 0 < gamma) (he : 0 < e)
    (hD : 0 < D chi kap rho) :
    output theta chi kap rho lam
        (journalA AP gamma alphaE e) (journalB BP gamma betaE e) >
      output theta chi kap rho lam (platformA AP) (platformB BP) ↔
      0 < (kap + lam * rho) * alphaE + (rho + lam * chi) * betaE := by
  have hfactor : 0 < theta * gamma * e / D chi kap rho := by
    exact div_pos (mul_pos (mul_pos htheta hgamma) he) hD
  calc
    output theta chi kap rho lam
          (journalA AP gamma alphaE e) (journalB BP gamma betaE e) >
        output theta chi kap rho lam (platformA AP) (platformB BP) ↔
        0 < output theta chi kap rho lam
          (journalA AP gamma alphaE e) (journalB BP gamma betaE e) -
          output theta chi kap rho lam (platformA AP) (platformB BP) := by
            constructor <;> intro h <;> linarith
    _ ↔ 0 < theta * gamma * e / D chi kap rho *
          ((kap + lam * rho) * alphaE + (rho + lam * chi) * betaE) := by
            rw [journal_platform_output_gap (ne_of_gt hD)]
    _ ↔ 0 < (kap + lam * rho) * alphaE + (rho + lam * chi) * betaE := by
            constructor
            · intro h
              rcases (mul_pos_iff.mp h) with hpos | hneg
              · exact hpos.2
              · exact False.elim ((not_lt_of_ge (le_of_lt hfactor)) hneg.1)
            · intro h
              exact mul_pos hfactor h

end

end CertificationLean
