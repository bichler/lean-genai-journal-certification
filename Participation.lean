import Mathlib

/-!
# Participation, fixed credibility, and the credibility trap

This module formalizes the order-theoretic core of Propositions 7 and 8 in
the article.  The economic primitives (a distribution of authors, an outside
option, and the exact best-response formula) are intentionally kept outside
the theorems below.  What the proofs use from those primitives is stated
explicitly as continuity, antitonicity, and endpoint/crossing hypotheses.

This division is deliberate.  It gives a kernel with no proof placeholders and
no added postulates, while making clear which analytical properties of a particular cdf
`G` must be established before it instantiates the generic results.
-/

namespace Certification.Participation

open Set Function

noncomputable section

/-! ## Fixed credibility (Proposition 7) -/

/-- A response rule has a fixed point at `n` on the stated feasible interval. -/
def IsEquilibrium (response : ℝ → ℝ) (left right n : ℝ) : Prop :=
  n ∈ Icc left right ∧ response n = n

/--
An abstract version of the fixed-credibility environment.

`capacity` is the service rate `\mu`, `junk` is `Z`, and `response` is the
equilibrium map `N \mapsto N_v(T(N))`.  A concrete application must prove
that its cdf-based response has the continuity, antitonicity, and bracket
properties recorded here.  `cutoff` is a finite point below `capacity - junk`
at which the response lies weakly below the 45-degree line.  It replaces the
informal limiting argument at the open endpoint `capacity - junk`.
-/
structure FixedCredibilityProblem where
  capacity : ℝ
  junk : ℝ
  response : ℝ → ℝ
  cutoff : ℝ
  cutoff_nonneg : 0 ≤ cutoff
  cutoff_lt_slack : cutoff < capacity - junk
  response_continuous : ContinuousOn response (Icc 0 cutoff)
  response_antitone : AntitoneOn response (Icc 0 (capacity - junk))
  response_nonneg_at_zero : 0 ≤ response 0
  response_below_at_cutoff : response cutoff ≤ cutoff

namespace FixedCredibilityProblem

/-- The review delay associated with a feasible mass of genuine submissions. -/
def delay (p : FixedCredibilityProblem) (n : ℝ) : ℝ :=
  (p.capacity - p.junk - n)⁻¹

/-- The article's equilibrium condition, including feasibility. -/
def Equilibrium (p : FixedCredibilityProblem) (n : ℝ) : Prop :=
  IsEquilibrium p.response 0 (p.capacity - p.junk) n

theorem cutoff_mem_feasible (p : FixedCredibilityProblem) :
    p.cutoff ∈ Icc 0 (p.capacity - p.junk) :=
  ⟨p.cutoff_nonneg, le_of_lt p.cutoff_lt_slack⟩

theorem response_antitone_on_cutoff (p : FixedCredibilityProblem) :
    AntitoneOn p.response (Icc 0 p.cutoff) := by
  intro x hx y hy hxy
  exact p.response_antitone
    ⟨hx.1, le_trans hx.2 (le_of_lt p.cutoff_lt_slack)⟩
    ⟨hy.1, le_trans hy.2 (le_of_lt p.cutoff_lt_slack)⟩ hxy

/-- An antitone response has at most one fixed point on an interval. -/
theorem fixed_eq_of_antitone
    {f : ℝ → ℝ} {a b x y : ℝ}
    (hanti : AntitoneOn f (Icc a b))
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hfx : f x = x) (hfy : f y = y) : x = y := by
  apply le_antisymm
  · by_contra hnot
    have hxy : y < x := lt_of_not_ge hnot
    have hle : f x ≤ f y := hanti hy hx (le_of_lt hxy)
    linarith
  · by_contra hnot
    have hyx : x < y := lt_of_not_ge hnot
    have hle : f y ≤ f x := hanti hx hy (le_of_lt hyx)
    linarith

/--
Existence and uniqueness of the fixed-credibility equilibrium (Proposition 7,
first sentence).  The proof is the intermediate-value theorem plus the fact
that an antitone function cannot meet the increasing 45-degree line twice.
-/
theorem existsUnique_equilibrium (p : FixedCredibilityProblem) :
    ∃! n, p.Equilibrium n := by
  obtain ⟨x, hx, hfixed⟩ := exists_mem_Icc_isFixedPt
    p.response_continuous p.cutoff_nonneg p.response_nonneg_at_zero
    p.response_below_at_cutoff
  change p.response x = x at hfixed
  refine ⟨x, ?_, ?_⟩
  · exact ⟨⟨hx.1, le_trans hx.2 (le_of_lt p.cutoff_lt_slack)⟩, hfixed⟩
  · intro y hy
    rcases hy with ⟨hy_feasible, hyfixed⟩
    by_cases hy_cutoff : y ≤ p.cutoff
    · exact (fixed_eq_of_antitone p.response_antitone_on_cutoff hx
        ⟨hy_feasible.1, hy_cutoff⟩ hfixed hyfixed).symm
    · have hcutoff_lt_y : p.cutoff < y := lt_of_not_ge hy_cutoff
      have hresponse_le : p.response y ≤ p.response p.cutoff :=
      p.response_antitone p.cutoff_mem_feasible hy_feasible
          (le_of_lt hcutoff_lt_y)
      have hy_le_cutoff : y ≤ p.cutoff := by
        rw [← hyfixed]
        exact le_trans hresponse_le p.response_below_at_cutoff
      exact False.elim ((not_lt_of_ge hy_le_cutoff) hcutoff_lt_y)

/-- A fixed point produced above lies strictly inside the queue's slack region. -/
theorem equilibrium_slack_positive (p : FixedCredibilityProblem) {n : ℝ}
    (hn : p.Equilibrium n) : 0 < p.capacity - p.junk - n := by
  rcases hn with ⟨hn_feasible, hn_fixed⟩
  have hn_cutoff : n ≤ p.cutoff := by
    by_contra hnot
    have hcutoff_lt_n : p.cutoff < n := lt_of_not_ge hnot
    have hresponse_le : p.response n ≤ p.response p.cutoff :=
      p.response_antitone p.cutoff_mem_feasible hn_feasible
        (le_of_lt hcutoff_lt_n)
    have hn_le_cutoff : n ≤ p.cutoff := by
      rw [← hn_fixed]
      exact le_trans hresponse_le p.response_below_at_cutoff
    exact (not_lt_of_ge hn_le_cutoff) hcutoff_lt_n
  have hn_lt : n < p.capacity - p.junk :=
    lt_of_le_of_lt hn_cutoff p.cutoff_lt_slack
  linarith

theorem delay_pos (p : FixedCredibilityProblem) {n : ℝ}
    (hn : p.Equilibrium n) : 0 < p.delay n := by
  unfold delay
  exact inv_pos.mpr (p.equilibrium_slack_positive hn)

end FixedCredibilityProblem

/--
Order comparison for equilibrium maps.  If one antitone response rule lies
weakly below another everywhere, its fixed point lies weakly below the other
fixed point.  This is the reusable comparative-statics step behind the claim
that an increase in congestion lowers genuine submissions.
-/
theorem fixedPoint_le_of_response_le
    {f g : ℝ → ℝ} {a b x y : ℝ}
    (hanti : AntitoneOn f (Icc a b))
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hfx : f x = x) (hgy : g y = y)
    (hfg : ∀ z ∈ Icc a b, f z ≤ g z) : x ≤ y := by
  by_contra hnot
  have hyx : y < x := lt_of_not_ge hnot
  have h1 : f x ≤ f y := hanti hy hx (le_of_lt hyx)
  have h2 : f y ≤ g y := hfg y hy
  rw [hfx] at h1
  rw [hgy] at h2
  linarith

/-- If delay rises, an antitone submission-demand function weakly falls. -/
theorem response_le_of_le_delay
    {d : ℝ → ℝ} {a b t₁ t₂ : ℝ}
    (hanti : AntitoneOn d (Icc a b))
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (hdelay : t₁ ≤ t₂) : d t₂ ≤ d t₁ :=
  hanti ht₁ ht₂ hdelay

/-! ## Endogenous credibility and the credibility trap (Proposition 8) -/

/-- The one-sided local stability needed for the collapse equilibrium. -/
def StableFromAbove (br : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0, ∀ y, x < y → y < x + ε → br y < y

/-- A best-response curve has positive excess at some positive-submission mass. -/
def HasHighCrossing (br : ℝ → ℝ → ℝ) (z : ℝ) : Prop :=
  ∃ n, n < br z n

/-- The set of junk loads at which the best response crosses above 45 degrees. -/
def highCrossingSet (br : ℝ → ℝ → ℝ) : Set ℝ :=
  {z | HasHighCrossing br z}

/-- The supremum version of the article's threshold `\bar Z`. -/
def junkThreshold (br : ℝ → ℝ → ℝ) : ℝ :=
  sSup (highCrossingSet br)

/-- A zero best-response window makes collapse stable from above. -/
theorem collapse_stable_of_zero_window
    {br : ℝ → ℝ} {n₀ : ℝ}
    (hn₀ : 0 < n₀)
    (hzero : ∀ n, 0 ≤ n → n ≤ n₀ → br n = 0) :
    StableFromAbove br 0 := by
  refine ⟨n₀, hn₀, ?_⟩
  intro y hy hy_small
  have hy_nonneg : 0 ≤ y := le_of_lt hy
  have hy_le_n₀ : y ≤ n₀ := by linarith
  rw [hzero y hy_nonneg hy_le_n₀]
  exact hy

/-- The credibility of a pool with `n` genuine and `z` junk submissions. -/
def credibility (n z : ℝ) : ℝ := n / (n + z)

/-- The size of the zero-response window implied by a credibility cutoff. -/
def collapseCutoff (γ z : ℝ) : ℝ := γ * z / (1 - γ)

/--
Below the cutoff in Proposition 8(a), the pool credibility is below the
credibility threshold.  This is an elementary algebraic lemma; the economic
step from low credibility to a zero best response remains an explicit
hypothesis in `bestResponse_zero_below_cutoff` below.
-/
theorem credibility_le_of_le_collapseCutoff
    {n z γ : ℝ}
    (hn : 0 ≤ n) (hz : 0 < z) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hbound : n ≤ collapseCutoff γ z) : credibility n z ≤ γ := by
  have hden : 0 < 1 - γ := sub_pos.mpr hγ1
  have hpool : 0 < n + z := by linarith
  have hmul : n * (1 - γ) ≤ γ * z := by
    rw [collapseCutoff] at hbound
    exact (le_div_iff₀ hden).mp hbound
  unfold credibility
  apply (div_le_iff₀ hpool).mpr
  nlinarith

/--
The exact bridge from the article's `\Phi_J(\gamma) \le \Phi_o` condition to a
zero submission best response.  It is parameterized rather than postulated:
an application supplies this lemma after proving monotonicity of its payoff
and cdf expression.
-/
theorem bestResponse_zero_below_cutoff
    {br : ℝ → ℝ} {z γ : ℝ}
    (hz : 0 < z) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hzero_of_credibility : ∀ m, 0 ≤ m → credibility m z ≤ γ → br m = 0) :
    ∀ m, 0 ≤ m → m ≤ collapseCutoff γ z → br m = 0 := by
  intro m hm_nonneg hm_bound
  exact hzero_of_credibility m hm_nonneg
    (credibility_le_of_le_collapseCutoff hm_nonneg hz hγ0 hγ1 hm_bound)

/--
If the best response is zero below the induced credibility cutoff, collapse is
a stable equilibrium.  This formalizes Proposition 8(a) once the payoff/cdf
bridge has been supplied.
-/
theorem collapse_stable_of_credibility_cutoff
    {br : ℝ → ℝ} {z γ : ℝ}
    (hz : 0 < z) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hzero_of_credibility : ∀ m, 0 ≤ m → credibility m z ≤ γ → br m = 0) :
    StableFromAbove br 0 := by
  apply collapse_stable_of_zero_window (n₀ := collapseCutoff γ z)
  · unfold collapseCutoff
    exact div_pos (mul_pos hγ0 hz) (sub_pos.mpr hγ1)
  · exact bestResponse_zero_below_cutoff hz (le_of_lt hγ0) hγ1
      hzero_of_credibility

/--
A strict crossing and a strictly negative endpoint yield a positive fixed
point.  This is the intermediate-value core of Proposition 8(b).
-/
theorem high_fixedPoint_of_crossing
    {br : ℝ → ℝ} {n b : ℝ}
    (hnb : n < b)
    (hcont : ContinuousOn br (Icc n b))
    (hcross : n < br n)
    (hright : br b < b) :
    ∃ x ∈ Icc n b, n < x ∧ br x = x := by
  obtain ⟨x, hx, hfixed⟩ := exists_mem_Icc_isFixedPt hcont
    (le_of_lt hnb) (le_of_lt hcross) (le_of_lt hright)
  change br x = x at hfixed
  have hnx : n < x := by
    by_contra hnot
    have hxn : x ≤ n := le_of_not_gt hnot
    have hxeq : x = n := le_antisymm hxn hx.1
    rw [hxeq] at hfixed
    linarith
  exact ⟨x, hx, hnx, hfixed⟩

/-- Junk-load monotonicity makes the high-crossing property downward closed. -/
theorem highCrossing_downward
    {br : ℝ → ℝ → ℝ}
    (hanti : ∀ z z' n, z ≤ z' → br z' n ≤ br z n)
    {z z' : ℝ} (hzz' : z ≤ z')
    (hhigh : HasHighCrossing br z') : HasHighCrossing br z := by
  rcases hhigh with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  exact lt_of_lt_of_le hn (hanti z z' n hzz')

theorem highCrossingSet_downwardClosed
    {br : ℝ → ℝ → ℝ}
    (hanti : ∀ z z' n, z ≤ z' → br z' n ≤ br z n) :
    ∀ ⦃z z'⦄, z ≤ z' → z' ∈ highCrossingSet br → z ∈ highCrossingSet br := by
  intro z z' hzz' hz'
  exact highCrossing_downward hanti hzz' hz'

/-- Every load strictly below the supremum threshold has a high crossing. -/
theorem highCrossing_below_junkThreshold
    {br : ℝ → ℝ → ℝ}
    (hanti : ∀ z z' n, z ≤ z' → br z' n ≤ br z n)
    (hne : (highCrossingSet br).Nonempty)
    {z : ℝ} (hz : z < junkThreshold br) : HasHighCrossing br z := by
  change z < sSup (highCrossingSet br) at hz
  obtain ⟨z', hz', hzz'⟩ := exists_lt_of_lt_csSup hne hz
  exact highCrossing_downward hanti (le_of_lt hzz') hz'

/-- No load strictly above a bounded threshold has a high crossing. -/
theorem no_highCrossing_above_junkThreshold
    {br : ℝ → ℝ → ℝ}
    (hbounded : BddAbove (highCrossingSet br))
    {z : ℝ} (hz : junkThreshold br < z) : ¬ HasHighCrossing br z := by
  intro hhigh
  have hle : z ≤ junkThreshold br := le_csSup hbounded hhigh
  linarith

/-!
### Scope note

The theorems above prove the topological and order-theoretic steps used in
Propositions 7 and 8.  To obtain the paper's full comparative statics from the
displayed cdf formula, a subsequent module must prove (rather than assume)
the relevant continuity and monotonicity of that formula, including behavior
at the open queue-capacity boundary.  Likewise, the statement that the
largest high fixed point is stable from above requires a compactness/sign
argument for the particular best-response curve.  Those are deliberately not
represented by an unchecked postulate here.
-/

end

end Certification.Participation
