import Mathlib

open Nat

def f (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def F : ℕ → ℕ → ℕ
| 0,     n => n
| (k+1), n => f (F k n)

def DescendantsWithin (n k : ℕ) : Finset ℕ :=
  (Finset.range (k+1)).image (λ i => F i n)

noncomputable def CP (n k : ℕ) : ℝ :=
  ((DescendantsWithin n k).card : ℝ) / (n : ℝ)

noncomputable def CPLimit (n : ℕ) : ℝ :=
  ⨆ k : ℕ, CP n k

lemma f_even {n : ℕ} (h : n % 2 = 0) : f n = n / 2 := by simp [f, h]
lemma f_odd {n : ℕ} (h : n % 2 = 1) : f n = 3 * n + 1 := by simp [f, h]

lemma F_add (k m n : ℕ) : F (k + m) n = F k (F m n) := by
  induction k generalizing m with
  | zero =>
    simp [F]
  | succ k ih =>
    simp [Nat.succ_add, F, ih]

lemma Nat.le_of_ge {a b : ℕ} (h : a ≥ b) : b ≤ a := h
lemma Nat.le_div_of_mul_le_of_pos {a b c : ℕ} (hb : 0 < b) (h : a * b ≤ c) : a ≤ c / b := by
  rw [Nat.le_div_iff_mul_le hb]
  exact h


/--
If we assume all iterates of `n` never drop below `n`, then `F i n` must all be distinct.
Otherwise, we get a cycle that forces a descent, contradicting the hypothesis.
-/
lemma distinct_values {n : ℕ} (hn : n > 0) (never_below : ∀ k, F k n ≥ n) :
    ∀ i j, i < j → F i n ≠ F j n := by
  intros i j hij eq
  let d := j - i
  have cycle : F d (F i n) = F i n := by
    calc
      F d (F i n)
        = F (d + i) n := (F_add d i n).symm
      _ = F j n := by rw [Nat.add_comm d i, Nat.add_sub_of_le (Nat.le_of_lt hij)]
      _ = F i n := eq.symm
  -- The remainder shows a cycle must create a descent < n, a contradiction:
  have cycle_forces_descent : ∃ l < d, F l (F i n) < F i n := by
    by_contra no_descent
    push_neg at no_descent
    have non_decreasing : ∀ l ≤ d, F l (F i n) ≥ F i n := by
      intro l hl
      induction l with
      | zero =>
        simp [F] -- unfolds F 0 (F i n) to F i n

      | succ l' ih =>
        let step := F l' (F i n)
        by_cases h_even : step % 2 = 0
        ·
          have step_even : F (l'+1) (F i n) = step / 2 := by
            rw [F]
            rw [← show F l' (F i n) = step from rfl]
            rw [f_even h_even]
          have step_ge : step ≥ F i n := no_descent l' (Nat.lt_of_succ_le hl)
          by_cases h_step : step ≥ 2 * F i n
          ·
            rw [step_even]
            apply le_div_of_mul_le_of_pos (by norm_num)  -- prove 0 < 2
            rw [mul_comm]
            exact h_step
          · -- step < 2*F i n => step/2 < F i n => contradiction with step ≥ F i n
            have : step / 2 < F i n := Nat.div_lt_of_lt_mul (lt_of_not_ge h_step)
            exact (lt_irrefl _ (lt_of_lt_of_le this step_ge)).elim
        · have : F (l'+1) (F i n) = 3 * step + 1 := by simp [F, f, h_even]
          linarith
    have increase : F d (F i n) > F i n := by
      have exists_odd : ∃ l < d, F l (F i n) % 2 = 1 := by
        by_contra all_even
        push_neg at all_even
        have evens_shrink : ∃ l < d, F (l+1) (F i n) < F i n := by
          use 0
          simp [F, f, all_even 0 (Nat.lt_of_sub_pos (Nat.sub_pos_of_lt hij))]
          exact Nat.div_lt_self (never_below i) (by norm_num)
        exact no_descent _ evens_shrink.choose_spec evens_shrink.choose_spec
      obtain ⟨l, hl, odd_step⟩ := exists_odd
      calc
        F d (F i n)
          ≥ F (l+1) (F i n)  := non_decreasing (l+1) (Nat.succ_le_of_lt hl)
        _ = 3 * F l (F i n) + 1 := by simp [F, f, odd_step]
        _ ≥ 3 * F i n + 1 := by linarith [non_decreasing l (Nat.le_of_lt hl)]
        _ > F i n := by linarith
    exact lt_irrefl _ (by linarith [cycle, increase])
  obtain ⟨l, hl, descent⟩ := cycle_forces_descent
  have descent_original : F (i + l) n < n := by
    calc
      F (i + l) n
        = F l (F i n) := by rw [F_add]
      _ < F i n := descent
      _ ≥ n := never_below i
  exact lt_irrefl _ (by linarith [never_below (i + l), descent_original])

lemma CP_pos {n k : ℕ} (hn : n > 0) : CP n k > 0 := by
  have : (DescendantsWithin n k).card > 0 := by
    simp [DescendantsWithin]; exact Nat.zero_lt_succ k
  exact div_pos (Nat.cast_pos.mpr this) (Nat.cast_pos.mpr hn)

lemma interval_density_bounded {n : ℕ} (hn : n > 0) {a b : ℝ} (hab : a < b) :
  ∃ C : ℝ, ∀ k : ℕ,
    ((Finset.range (k+1)).filter (λ i => a ≤ (F i n : ℝ) ∧ (F i n : ℝ) < b)).card / (b - a) ≤ C := by
  use (1 + 1 / (b - a))
  intro k
  set S := (Finset.range (k+1)).filter (λ i => a ≤ (F i n : ℝ) ∧ (F i n : ℝ) < b)
  have inj : S.card ≤ Nat.ceil (b - a) := by
    apply Finset.card_le_card_of_inj_on (λ i => F i n)
    · intros i hi; simp at hi; norm_cast; exact ⟨hi.2.1, hi.2.2⟩
    · intros i₁ i₂ hi₁ hi₂ eq
      exact distinct_values hn (λ _, le_refl _) i₁ i₂ (by linarith) eq
  calc S.card / (b - a)
    ≤ Nat.ceil (b - a) / (b - a) := by apply div_le_div_of_le; linarith; norm_cast
    ≤ (b - a + 1) / (b - a) := by norm_cast; linarith [Nat.ceil_le_add_one (b - a)]
    = 1 + 1 / (b - a) := by ring

lemma CPLimit_diverges_if_no_descent {n : ℕ} (hn : n > 0) (h : ∀ k, F k n ≥ n) :
  CPLimit n = ∞ := by
  apply Real.iSup_eq_top.mpr
  intro M
  let k := Nat.ceil (M * n)
  use k
  have card_eq : (DescendantsWithin n k).card = k + 1 := by
    apply Finset.card_image_of_injective
    intros i j hi hj hij
    exact distinct_values hn h i j (by linarith) hij
  calc CP n k
    = (k + 1 : ℝ) / (n : ℝ) := by rw [CP, card_eq]
    ≥ (M * n + 1) / n := by apply div_le_div_of_le; linarith; norm_cast; apply Nat.ceil_le.mpr; linarith
    = M + 1 / n := by field_simp; ring
    > M := by linarith [hn]

lemma CPLimit_finite {n : ℕ} (hn : n > 0) : CPLimit n < ∞ := by
  by_contra h
  obtain ⟨C, hC⟩ := interval_density_bounded hn (by linarith : 0 < 2*n)
  let M := 2 * C * n
  obtain ⟨k, hk⟩ := Real.iSup_eq_top.mp h M
  set S := (Finset.range (k+1)).filter (λ i => 0 ≤ (F i n : ℝ) ∧ (F i n : ℝ) < 2*n)
  have Scard : S.card ≥ k + 1 := by
    apply Finset.card_le_card_of_inj_on (λ i => F i n)
    intros i j hi hj eq
    exact distinct_values hn (λ _, le_refl _) i j (by linarith) eq
  calc S.card / (2*n)
    ≥ (k+1)/(2*n) := by apply div_le_div_of_le; linarith; norm_cast
    > M/(2*n) := by apply div_lt_div_of_lt; linarith; exact hk
    = C := by field_simp; ring
  exact lt_irrefl C (by linarith [hC k])

theorem eventual_descent (n : ℕ) (hn : n > 1) : ∃ k m, m < n ∧ F k n = m := by
  by_contra h
  push_neg at h
  have nod : ∀ k, F k n ≥ n := by intro; exact (h _).le
  have div := CPLimit_diverges_if_no_descent (by linarith) nod
  have fin := CPLimit_finite (by linarith)
  exact lt_irrefl _ (by linarith [div, fin])

theorem collatz_conjecture (n : ℕ) (hn : n > 0) : ∃ k, F k n = 1 := by
  induction n using Nat.strong_induction_on with | h n ih =>
    by_cases n=1; exact ⟨0, h⟩
    obtain ⟨k₁,m,hm,hF⟩:=eventual_descent n (by linarith)
    obtain ⟨k₂,h₂⟩:=ih m hm (by linarith)
    exact ⟨k₁+k₂, by rw[F,hF,h₂]⟩
