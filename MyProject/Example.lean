
import Mathlib

theorem sum_product_formula (n : ℕ) :
  ∑ k in Finset.range n, k * (k + 3) = n * (n + 1) * (n + 5) / 3 := by
  induction n with
  | zero => 
    simp
    
  | succ k ih => 
    -- Rewrite sum for k + 1 using previous sum
    have step1 : ∑ i in Finset.range (k + 1), i * (i + 3) = 
                 ∑ i in Finset.range k, i * (i + 3) + k * (k + 3) := by
      rw [Finset.sum_range_succ]
      ring

    -- Use inductive hypothesis
    have step2 : ∑ i in Finset.range k, i * (i + 3) = 
                 k * (k + 1) * (k + 5) / 3 := by
      exact ih

    -- Substitute and begin algebraic manipulation
    have step3 : k * (k + 1) * (k + 5) / 3 + k * (k + 3) = 
                 (k + 1) * (k * (k + 5) + 3 * (k + 4)) / 3 := by
      field_simp
      ring

    -- Simplify expression in numerator
    have step4 : k * (k + 5) + 3 * (k + 4) = k^2 + 8*k + 12 := by
      ring

    -- Factor the expression
    have step5 : k^2 + 8*k + 12 = (k + 2) * (k + 6) := by
      ring

    -- Show final equality
    have step6 : (k + 1) * (k + 2) * (k + 6) / 3 = 
                 (k + 1) * ((k + 1) + 1) * ((k + 1) + 5) / 3 := by
      ring

    -- Combine all steps
    calc ∑ i in Finset.range (k + 1), i * (i + 3)
      _ = ∑ i in Finset.range k, i * (i + 3) + k * (k + 3) := by rw [step1]
      _ = k * (k + 1) * (k + 5) / 3 + k * (k + 3) := by rw [step2]
      _ = (k + 1) * (k + 2) * (k + 6) / 3 := by
          rw [step3]
          rw [step4]
          rw [step5]
      _ = (k + 1) * ((k + 1) + 1) * ((k + 1) + 5) / 3 := by rw [step6]

