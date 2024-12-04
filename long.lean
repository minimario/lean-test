import Mathlib

theorem block_division (n : ℕ) (weights : Fin n → ℕ)
  (h1 : ∀ i, weights i < n)
  (h2 : ∑ i, weights i < 2*n) :
  ∃ (S : Finset (Fin n)), ∑ i in S, weights i = n :=
by
  -- Step 1: Set up the framework for dynamic programming
  let P : Set (ℕ × Finset (Fin n)) :=
    {p | ∃ S : Finset (Fin n), p = (∑ i in S, weights i, S)}

  -- Step 2: Show that empty sum is achievable
  have h_empty : (0, ∅) ∈ P := by
    use ∅
    simp

  -- Step 3: Show extension property
  have h_extend : ∀ (k : ℕ) (S : Finset (Fin n)) (i : Fin n),
    (k, S) ∈ P → i ∉ S → (k + weights i, insert i S) ∈ P := by
    intros k S i hP hnotIn
    use insert i S
    simp
    rcases hP with ⟨S', hS'⟩
    rw [hS']
    simp [hnotIn]

  -- Step 4: Show all achievable sums are bounded
  have h_bound : ∀ p ∈ P, p.1 < 2*n := by
    intros p hp
    rcases hp with ⟨S, hS⟩
    rw [hS]
    simp
    trans (∑ i, weights i)
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ S
      · intro x _
        exact Nat.zero_le _
    · exact h2

  -- Step 5: Show existence of desired subset using well-ordering
  have h_exists : ∃ S, (n, S) ∈ P := by
    by_contradiction h
    push_neg at h
    let Q := {k | ∃ S, (k, S) ∈ P}
    have hQ_bdd : ∀ k ∈ Q, k < n := by
      intros k hk
      rcases hk with ⟨S, hS⟩
      by_contradiction h'
      push_neg at h'
      have : k ≥ n := h'
      have : (k, S) ∈ P := hS
      have := h S
      contradiction
    have hQ_nonempty : Q.Nonempty := by
      use 0
      use ∅
      exact h_empty
    have := Set.exists_maximal_element_of_bdd hQ_nonempty hQ_bdd
    rcases this with ⟨m, hm_in, hm_max⟩
    rcases hm_in with ⟨S, hS⟩
    have : ∀ i : Fin n, i ∈ S := by
      intro i
      by_contradiction hi
      have := h_extend m S i hS hi
      have : m + weights i ∈ Q := by
        use insert i S
        exact this
      have : m + weights i ≤ m := by
        apply hm_max
        exact this
      have : weights i ≤ 0 := Nat.le_of_add_le_left this
      have : weights i > 0 := Nat.pos_of_ne_zero (h1 i)
      contradiction
    have : ∑ i in S, weights i = ∑ i, weights i := by
      apply Finset.sum_eq_sum_of_subset_eq
      · exact Finset.subset_univ S
      · exact this
    rw [this] at hS
    have := h_bound (∑ i, weights i, S) hS
    linarith

  -- Step 6: Extract final result
  rcases h_exists with ⟨S, hS⟩
  use S
  rcases hS with ⟨S', hS'⟩
  rw [hS']
  simp

