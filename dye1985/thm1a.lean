import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFraction

open MeasureTheory Set Classical

/-!
# Dye (1985) Theorem 1 in Lean 4

Theorem: If the density f(x) is positive on [0, X], there exists a
nondegenerate disclosure equilibrium threshold x_star ∈ (0, X).
-/

noncomputable section

/--
Standard assumptions for the Dye (1985) model
-/
structure DyeModel where
  -- Upper bound of the support
  X : ℝ
  hX : X > 0
  -- Probability that the manager is NOT endowed with information
  p : ℝ
  hp : 0 < p ∧ p < 1
  -- Density function f
  f : ℝ → ℝ
  f_cont : ContinuousOn f (Icc 0 X)
  f_pos : ∀ x ∈ Icc 0 X, f x > 0
  -- f is a PDF on [0, X]
  f_integral : ∫ x in (0)..X, f x = 1

namespace DyeModel

variable (m : DyeModel)

/-- The Cumulative Distribution Function F(y) -/
def F (y : ℝ) : ℝ := ∫ x in (0)..y, m.f x

/-- The unconditional mean μ of the information -/
def μ : ℝ := ∫ x in (0)..m.X, x * m.f x

lemma mean_lt_upper : m.μ < m.X := by
  -- Sketch: Since f > 0 and μ is the average, and X is the max of the support,
  -- the mean must be strictly less than the maximum.
  sorry

lemma mean_pos : m.μ > 0 := by
  -- Sketch: Integral of x*f(x) over [0, X] with X > 0 and f > 0.
  sorry

/--
The market's Bayesian price function when no disclosure occurs,
given a conjectured threshold `y`.
Price = E[x | no disclosure] = (p*μ + (1-p) * ∫₀ʸ x f(x) dx) / (p + (1-p)*F(y))
-/
def price_nd (y : ℝ) : ℝ :=
  (m.p * m.μ + (1 - m.p) * ∫ x in (0)..y, x * m.f x) / (m.p + (1 - m.p) * m.F y)

/-- The equilibrium condition function: g(y) = price_nd(y) - y -/
def g (y : ℝ) : ℝ := m.price_nd y - y

theorem existence_of_nontrivial_threshold :
  ∃ x_star ∈ Ioo 0 m.X, m.g x_star = 0 := by
  -- 1. g is continuous
  have g_cont : ContinuousOn m.g (Icc 0 m.X) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.div
      · -- Numerator is continuous (integral is continuous in its limit)
        sorry
      · -- Denominator is continuous and never zero (since p > 0 and F ≥ 0)
        sorry
      · -- Denominator check
        intro y hy
        have : m.F y ≥ 0 := sorry
        linarith [m.hp.1, m.hp.2]
    · exact continuousOn_id

  -- 2. Value at the lower bound g(0)
  have g_zero : m.g 0 = m.μ := by
    simp [g, price_nd, F]
    -- Integral from 0 to 0 is 0
    field_simp [m.hp.1]

  have g_zero_pos : m.g 0 > 0 := by
    rw [g_zero]
    exact m.mean_pos

  -- 3. Value at the upper bound g(X)
  have g_X : m.g m.X = m.μ - m.X := by
    simp [g, price_nd, F, m.f_integral]
    -- The denominator p + (1-p)*1 = 1
    -- The numerator pμ + (1-p)μ = μ
    field_simp
    ring

  have g_X_neg : m.g m.X < 0 := by
    rw [g_X]
    linarith [m.mean_lt_upper]

  -- 4. Apply Intermediate Value Theorem
  apply intermediate_value_Icc (m.hX.le) g_cont
  · rw [mem_Icc]
    exact ⟨g_X_neg.le, g_zero_pos.le⟩

/--
Theorem 1 Conclusion:
There exists an equilibrium x_star where the manager discloses
if and only if x ≥ x_star, and this is not full disclosure (x_star > 0).
-/
theorem Dye_Theorem_1 :
  ∃ x_star, x_star ∈ Ioo 0 m.X ∧ m.price_nd x_star = x_star := by
  obtain ⟨x_star, h_mem, h_eq⟩ := m.existence_of_nontrivial_threshold
  use x_star
  constructor
  · exact h_mem
  · rw [g] at h_eq
    linarith

end DyeModel
