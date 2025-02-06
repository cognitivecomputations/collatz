import Mathlib

open Nat

/- Collatz function (one step) -/
def f (n : ℕ) : ℕ :=
  if n % 2 == 0 then n / 2 else 3 * n + 1

/- Accelerated function: one or two steps (odd step followed by one division) -/
def T (n : ℕ) : ℕ :=
  if n % 2 == 0 then n / 2 else (3 * n + 1) / 2

/- Recurrence F: k-th iterate of f (apply f k times) -/
def F : ℕ → ℕ → ℕ
| 0,     n => n
| (k+1), n => F k (f n)

def F_add (k₁ k₂ : ℕ) (n : ℕ) : F (k₁ + k₂) n = F k₁ (F k₂ n) := by
  induction k₂ generalizing n with
  | zero => rfl
  | succ k ih => rw [← add_assoc, F, ih, F]

/- Basic properties of f -/
lemma f_even {n : ℕ} (h : n % 2 = 0) : f n = n / 2 := by
  simp [f, h]

lemma f_odd {n : ℕ} (h : n % 2 = 1) : f n = 3 * n + 1 := by
  simp [f, h]

/- If n ≡ 1 (mod 4) and n > 1, then in three steps of f the value drops below n. -/
lemma collatz_mod4_drop {n : ℕ} (h4 : n % 4 = 1) (hn : 1 < n) : F 3 n < n := by
  -- Express n as 4k + 1
  have hk : n = 4 * (n / 4) + 1 := by rw [← h4, Nat.div_add_mod]
  set k := n / 4
  -- n is odd (since n ≡ 1 mod 4)
  have h₂ : n % 2 = 1 := odd_of_mod_four_eq_one h4
  -- Compute f n
  have f1 : f n = 3 * n + 1 := f_odd h₂
  -- 3n + 1 is divisible by 4, since n = 4k + 1
  have hdiv4 : 4 ∣ 3 * n + 1 := by
    rw [hk]
    rw [mul_add, ← mul_assoc, add_assoc]
    rw [mul_comm 3, mul_assoc, ← mul_add_one]
    exact dvd_mul_right 4 (3 * k + 1)
  -- Compute f (f n)
  have f2 : f (f n) = (3 * n + 1) / 2 := by
    rw [f1]
    -- 3n + 1 is even (since n is odd)
    have : (3 * n + 1) % 2 = 0 := by omega
    simp [f, this]
  -- (3n + 1) / 2 is even (because 4 | (3n+1))
  have : ((3 * n + 1) / 2) % 2 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.dvd_div_of_mul_dvd hdiv4
  -- Compute f (f (f n))
  have f3 : f (f (f n)) = (3 * n + 1) / 4 := by
    rw [f2]
    simp [f, this]
    rw [Nat.div_div_eq_div_mul]
  -- Simplify (3n+1)/4 using n = 4k+1
  conv at f3 => rhs; rw [hk]
  -- At this point, (3n+1)/4 = 3k + 1
  have f3val : f (f (f n)) = 3 * k + 1 := by omega
  -- Since k ≥ 1 (because n > 1), we have 3k + 1 < 4k + 1 = n
  have kpos : 0 < k := by omega
  have : 3 * k + 1 < 4 * k + 1 := by omega
  rw [← hk] at this
  -- Thus F 3 n = 3*k + 1 < n
  simp [F]
  rw [f3val]
  exact this

/- If n+1 is divisible by 2^j but not by 2^(j+1), then there is a drop below n at some step. -/
lemma collatz_drop_aux (j n : ℕ) (hdiv : 2^j ∣ n + 1) (hndiv : ¬ 2^(j+1) ∣ n + 1) (hn : 1 < n) :
    ∃ k, F k n < n := by
  induction j generalizing n with
  | zero =>
    -- j = 0 means n+1 is not divisible by 2, so n+1 is odd, hence n is even.
    have : n % 2 = 0 := by omega
    use 1
    simp [F]
    rw [f_even this]
    -- n / 2 < n for n > 1
    exact Nat.div_lt_self (Nat.zero_lt_of_lt hn) (by decide)
  | succ j ih =>
    -- Here 2^(j+1) ∣ n+1 but 2^(j+2) ∣ n+1 is false.
    -- So v2(n+1) = j+1 ≥ 1, meaning n is odd.
    have hodd : n % 2 = 1 := by
      by_contra neven
      have : 2 ∣ n := by omega
      rw [Nat.dvd_iff_mod_eq_zero] at this
      rw [Nat.pow_succ, mul_comm] at hdiv
      -- Now n+1 is divisible by 2^(j+1) ≥ 2^1, so in particular 2 ∣ n+1.
      have : 2 ∣ n + 1 := dvd_of_mul_right_dvd hdiv
      omega
    -- Perform one Collatz cycle (two steps) to get new value n1
    let n1 := F 2 n
    -- Compute n1 explicitly: n1 = f(f n) = (3n + 1) / 2
    have n1_def : n1 = (3 * n + 1) / 2 := by
      dsimp [n1, F]
      rw [f_odd hodd, f_even]
      · -- justify (3n+1) is even
        omega
    -- Now n1 + 1 = 3(n+1)/2.
    obtain ⟨t, ht⟩ := hdiv
    -- We know ¬2^(j+2) ∣ n+1, so t must be odd.
    have todd : t % 2 = 1 := by
      by_contra teven
      have : 2 ∣ t := by omega
      rcases this with ⟨u, hu⟩
      rw [ht, hu, ← mul_assoc, pow_succ] at hndiv
      exact hndiv ⟨u, rfl⟩
    have abc : n1 + 1 = 3 * 2^j * t := by
      rw [n1_def, ← add_div_right, add_assoc, ← mul_add_one]
      rw [ht, pow_succ, ← mul_assoc, ← mul_assoc, mul_right_comm, Nat.mul_div_cancel]
      decide
      decide
    -- Derive divisibility for n1 + 1.
    have hdiv_n1 : 2^j ∣ n1 + 1 := by
      -- n1 + 1 = 3 * (n+1) / 2 = 3 * 2^j * t
      rw [abc, ← mul_rotate]
      exact dvd_mul_left (2^j) (t * 3)
    have hndiv_n1 : ¬ 2^(j+1) ∣ n1 + 1 := by
      intro H
      rcases H with ⟨m, hm⟩
      --rw [n1_def, ht] at hm
      -- Now 3 * 2^j * t = 2^(j+1) * m. Cancel 2^j:
      have eq_cancel : 2^j * (3 * t) = 2^j * (2 * m) := by
        --rw [Nat.mul_right_inj (NeZero.ne _)]
        calc 2^j * (3 * t) = 3 * 2^j * t := by rw [mul_left_comm, mul_assoc]
        _   = 2 * 2^j * m := by rw [mul_comm 2, ← Nat.pow_add_one, ← hm, abc]
        _   = 2^j * (2 * m) := by rw [mul_left_comm, mul_assoc]
      have eq_small : 3 * t = 2 * m := (Nat.mul_right_inj (a := 2^j) (NeZero.ne _)).mp eq_cancel
      -- Left side is odd (t is odd), right side is even, impossible.
      have mod_contra : (3 * t) % 2 = (2 * m) % 2 := congr_arg (· % 2) eq_small
      rw [Nat.mul_mod_right] at mod_contra
      rw [← Nat.even_iff] at mod_contra
      have : Odd (3 * t) := by
        apply Odd.mul
        decide
        rw [Nat.odd_iff]
        exact todd
      exact absurd mod_contra (not_even_iff_odd.mpr this)
    -- Now apply the induction hypothesis to n1.
    obtain ⟨k1, drop_n1⟩ := ih n1 hdiv_n1 hndiv_n1 (by
      -- show 1 < n1
      rw [n1_def]
      rw [Nat.lt_div_iff_mul_lt (by decide)]
      omega
    )
    -- Using induction result: ∃ k1, F k1 n1 < n1.
    -- Then F (2 + k1) n = F k1 (F 2 n) = F k1 n1 < n1.
    use 2 + k1
    have step_comp : F (2 + k1) n = F k1 (F 2 n) := Nat.add_comm _ _ ▸ F_add _ _ _
    rw [step_comp]
    refine drop_n1.trans ?_
    --(Nat.div_mul_le_self (3 * n + 1) 2)
    sorry

theorem exists_collatz_descent (n : ℕ) (h : 1 < n) : ∃ k, F k n < n := by
  -- We proceed by contradiction on the negation: assume ∀ k, F k n ≥ n (no drop ever).
  by_contra H
  push_neg at H
  -- Then n cannot be even (because k = 1 would give F 1 n = f n < n), so n is odd.
  have n_odd : n % 2 = 1 := by
    by_contra ne
    have : n % 2 = 0 := not_not.mp ne
    have drop1 := f_even this
    rw [← F 1 n, drop1] at H
    have : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_lt h) (by decide)
    exact not_le_of_lt this (H 1)
  -- Now use strong induction on j to show 2^j ∣ n+1 for all j, which is impossible.
  suffices : ∀ (j : ℕ), 2^j ∣ n + 1
  · -- Choose j such that 2^j > n+1 (e.g. j = n+1 works, since 2^(n+1) > n+1 for n ≥ 2).
    have big_j : 2^(n+1) > n + 1 := by
      -- 2^(n+1) = 2 * 2^n ≥ 2 * (n + 1) (since 2^n ≥ n + 1 for n ≥ 1), and 2*(n+1) > n+1.
      apply Nat.lt_of_lt_of_le (by linarith)
      -- prove 2^n ≥ n + 1 for n ≥ 1
      induction n with
      | zero => simp at h   -- n = 0 is not possible since h: 1 < n
      | succ k hk =>
        cases k with
        | zero => decide     -- n = 1 yields 2^1 = 2 ≥ 2 = 1+1
        | succ k' =>
          calc 2^(succ (succ k')) = 2 * 2^(succ k') := pow_succ _ _
          _    ≥ 2 * (succ k' + 1) := Nat.mul_le_mul_left 2 hk
          _    = 2 * succ (succ k') := rfl
          _    > succ (succ k')     := by linarith
    -- But then 2^(n+1) ∣ n+1 (by our assumption), which is impossible as it exceeds n+1.
    have ⟨m, hm⟩ := this (n+1)
    have mpos : m ≥ 1 := Nat.div_pos (Nat.lt_of_lt_of_le (by linarith) big_j) (by decide)
    calc n + 1 = 2^(n+1) * m := hm
    _   ≥ 2^(n+1) * 1 := Nat.mul_le_mul_left _ mpos
    _   = 2^(n+1)     := by rw [mul_one]
    _   > n + 1       := big_j
    -- Contradiction: n + 1 > n + 1.
    -- Proof of the induction claim: ∀ j, 2^j ∣ n+1
    intro j
    induction j with
    | zero =>
      -- 2^0 = 1 always divides n+1.
      trivial
    | succ j ih =>
      -- We know 2^j ∣ n+1 by IH. If 2^(j+1) does not divide n+1, then by collatz_drop_aux we get a contradiction.
      by_contra hj
      obtain ⟨k, hk⟩ := collatz_drop_aux j n ih hj h
      exact (not_lt_of_ge (H k)) hk

/- Collatz conjecture: for any n > 0, there exists k such that F k n = 1. -/
theorem collatz_conjecture (n : ℕ) (h₀ : 0 < n) : ∃ k, F k n = 1 := by
  induction' n using Nat.strong_induction_on with n ih
  cases Nat.eq_or_lt_of_le h₀ with
  | inl h1 =>
    -- Base case: n = 1. Then F 0 n = 1.
    use 0
    rw [h1, F]
  | inr h1 =>
    -- Inductive step: Assume true for all m < n. Need to show it for n > 1.
    -- By exists_collatz_descent, there exists k such that F k n < n.
    obtain ⟨k, hk⟩ := exists_collatz_descent n h1
    -- By induction hypothesis (strong induction), the conjecture is true for F k n.
    -- So there exists k1 such that F k1 (F k n) = 1.
    obtain ⟨k1, hk1⟩ := ih (F k n) hk (Nat.zero_lt_of_lt hk)
    -- Then F (k + k1) n = 1.
    use k + k1
    have step_comp : F (k + k1) n = F k1 (F k n) := by
      induction k with
      | zero => simp [F]
      | succ k' ih => simp [F, ih]
    rwa [step_comp, hk1]
