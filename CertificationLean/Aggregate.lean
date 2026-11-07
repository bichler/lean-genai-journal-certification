import Mathlib

/-!
  Formal support for Proposition 9 (average quality versus aggregate output).

  The paper writes aggregate output as the sum of the contribution below and
  above an endogenous capability cutoff.  Rather than encoding a particular
  measure-theoretic representation of the cdf, this file makes the two
  fundamental-theorem-of-calculus facts used in the paper explicit as
  `HasDerivAt` assumptions.  The derivative and all sign conclusions are then
  proved by Lean.
-/

namespace CertificationLean

noncomputable section

/-- Data needed for the local comparative static in Proposition 9.  `below`
and `above` are the two capability-weighted cdf integrals in the paper. -/
structure AggregateInputs where
  nV : ℝ
  qO : ℝ
  qJ : ℝ
  eta : ℝ
  delta : ℝ
  nF : ℝ
  below : ℝ → ℝ
  above : ℝ → ℝ
  threshold : ℝ
  density : ℝ
  below_hasDerivAt : HasDerivAt below (threshold * density) threshold
  above_hasDerivAt : HasDerivAt above (-(threshold * density)) threshold

/-- Aggregate net epistemic output, holding the flawed-submission term fixed
when the cutoff changes. -/
def aggregateOutput (p : AggregateInputs) (t : ℝ) : ℝ :=
  p.nV * (p.qO * p.below t + p.qJ * p.above t) -
    p.eta * (1 - p.delta) * p.nF

/-- The derivative asserted in Proposition 9. -/
def aggregateSlope (p : AggregateInputs) : ℝ :=
  -(p.nV * (p.qJ - p.qO) * p.threshold * p.density)

/-- Proposition 9's derivative formula.  The two derivative hypotheses are
exactly the applications of Leibniz' rule to the lower and upper integrals. -/
theorem aggregateOutput_hasDerivAt (p : AggregateInputs) :
    HasDerivAt (aggregateOutput p) (aggregateSlope p) p.threshold := by
  have hbelow : HasDerivAt (fun t : ℝ => p.qO * p.below t)
      (p.qO * (p.threshold * p.density)) p.threshold :=
    p.below_hasDerivAt.const_mul p.qO
  have habove : HasDerivAt (fun t : ℝ => p.qJ * p.above t)
      (p.qJ * (-(p.threshold * p.density))) p.threshold :=
    p.above_hasDerivAt.const_mul p.qJ
  have hsum : HasDerivAt
      (fun t : ℝ => p.qO * p.below t + p.qJ * p.above t)
      (p.qO * (p.threshold * p.density) +
        p.qJ * (-(p.threshold * p.density))) p.threshold :=
    hbelow.add habove
  have hscaled : HasDerivAt
      (fun t : ℝ => p.nV * (p.qO * p.below t + p.qJ * p.above t))
      (p.nV * (p.qO * (p.threshold * p.density) +
        p.qJ * (-(p.threshold * p.density)))) p.threshold :=
    hsum.const_mul p.nV
  have hconstant : HasDerivAt
      (fun _ : ℝ => p.eta * (1 - p.delta) * p.nF) 0 p.threshold :=
    hasDerivAt_const p.threshold (p.eta * (1 - p.delta) * p.nF)
  convert hscaled.sub hconstant using 1 <;>
    simp only [aggregateOutput, aggregateSlope] <;> ring

/-- Under the substantive conditions in the proposition, aggregate output
falls strictly as the capability cutoff rises. -/
theorem aggregateSlope_negative
    (p : AggregateInputs)
    (hnV : 0 < p.nV) (hquality : p.qO < p.qJ)
    (hthreshold : 0 < p.threshold) (hdensity : 0 < p.density) :
    aggregateSlope p < 0 := by
  have hgap : 0 < p.qJ - p.qO := sub_pos.mpr hquality
  have hproduct : 0 < p.nV * (p.qJ - p.qO) * p.threshold * p.density := by
    exact mul_pos (mul_pos (mul_pos hnV hgap) hthreshold) hdensity
  simpa [aggregateSlope] using neg_neg_of_pos hproduct

/-- A certificate for the selection fact used in Proposition 9.  It is
deliberately independent of a particular cdf implementation: a later file can
derive `mean_gap` from an atomless distribution with positive density. -/
structure TailMeanSelection where
  lower upper : ℝ
  mean : ℝ → ℝ
  gapFactor : ℝ → ℝ → ℝ
  mean_gap : ∀ {s t : ℝ}, lower ≤ t → t < s → s ≤ upper →
    mean s - mean t = (s - t) * gapFactor t s
  gapFactor_pos : ∀ {s t : ℝ}, lower ≤ t → t < s → s ≤ upper →
    0 < gapFactor t s

/-- Raising an admissible selection cutoff strictly raises the average
capability of the selected population. -/
theorem tailMean_strictly_increases
    (p : TailMeanSelection) {s t : ℝ}
    (ht : p.lower ≤ t) (hts : t < s) (hs : s ≤ p.upper) :
    p.mean t < p.mean s := by
  have hgap := p.mean_gap ht hts hs
  have hfactor : 0 < p.gapFactor t s := p.gapFactor_pos ht hts hs
  have hdiff : 0 < (s - t) * p.gapFactor t s :=
    mul_pos (sub_pos.mpr hts) hfactor
  linarith

/-- If journal output per unit of capability is positive, the average output
of genuine journal submissions rises with the cutoff as well. -/
theorem journalAverageOutput_strictly_increases
    (p : TailMeanSelection) {qJ s t : ℝ}
    (hqJ : 0 < qJ)
    (ht : p.lower ≤ t) (hts : t < s) (hs : s ≤ p.upper) :
    qJ * p.mean t < qJ * p.mean s := by
  exact (mul_lt_mul_left hqJ).2 (tailMean_strictly_increases p ht hts hs)

end

end CertificationLean
