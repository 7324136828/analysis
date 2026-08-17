import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

theorem Rat.pre_between_int(x:ℚ) : ↑((x.num / (x.den:ℤ))) ≤ x ∧ x < ↑((x.num / (x.den:ℤ))) + 1 := by
    constructor
    . have h1 : 1 = 1 := rfl
      have h2 := (Rat.num_div_den x).symm
      conv =>
        rhs
        rw [h2]
      have hden : (x.den : ℤ) ≠ 0 := by
        exact_mod_cast x.den_nz

      have h1 : x.num / (x.den : ℤ) * (x.den : ℤ) ≤ x.num := by
        simpa [mul_comm] using (Int.mul_ediv_self_le (x := x.num) (k := (x.den : ℤ)) hden)

      have h2 : ((x.num / (x.den : ℤ) : ℤ) : ℚ) * (x.den : ℚ) ≤ (x.num : ℚ) := by
        exact_mod_cast h1

      have hden_pos : (0 : ℚ) < (x.den : ℚ) := by
        exact_mod_cast Nat.pos_of_ne_zero x.den_nz

      exact (le_div_iff₀ hden_pos).2 h2
    . have h2 := (Rat.num_div_den x).symm
      conv =>
        lhs
        rw [h2]
      have hden : (x.den : ℤ) ≠ 0 := by
        exact_mod_cast x.den_nz

      have hden_pos : 0 < x.den := by
        omega

      have hden_pos_int : 0 < (x.den: ℤ) := by
        exact_mod_cast hden_pos

      have hden_pos_rat : (0 : ℚ) < (x.den : ℚ) := by
        exact_mod_cast hden_pos_int

      have h3 := Int.mul_ediv_self_le (x := x.num) (k := (x.den : ℤ)) hden
      have h4 := Int.lt_mul_ediv_self_add (x := x.num) (k := (x.den : ℤ)) hden_pos_int
      set q : ℤ := x.num / (x.den : ℤ)
      have h1 : x.num < (q + 1) * (x.den : ℤ) := by
        dsimp [q]
        grind
      have h2 : (x.num : ℚ) < ((q : ℚ) + 1) * (x.den : ℚ) := by
        exact_mod_cast h1
      exact (div_lt_iff₀ hden_pos_rat).2 h2


/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  apply ExistsUnique.intro (x.num / x.den)
  . exact pre_between_int x
  . intro y hy
    have ⟨ha1, ha2⟩ := pre_between_int x
    set a := (x.num / x.den)
    have h1 := lt_trichotomy y a
    rcases h1 with h1 | h1 | h1
    . have h_0 : 1 = 1 := by rfl
      have hy1 : y + 1 ≤ a := by omega
      have hy2 : ↑(y + 1) ≤ (a:ℚ) := by
        exact_mod_cast hy1
      have hy3 : ↑(y + 1) = (y:ℚ) + 1 := by
        grind
      have hy4 : ↑(y + 1) ≤ x := by grind
      rw [hy3] at hy4
      have hy5 := hy.2
      linarith
    . simp_all
    . have h_0 : 1 = 1 := by rfl
      have hy1 : y ≥ a + 1 := by omega
      have hy2 : (y:ℚ) ≥ ↑(a + 1) := by
        exact_mod_cast hy1
      have hy3 : ↑(a + 1) = (a:ℚ) + 1 := by
        grind
      have hy4 : (y:ℚ) > x := by grind
      have hy5 := hy.1
      linarith




theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  have h1 := Rat.between_int x
  obtain ⟨a, ⟨⟨ha11, ha12⟩, ha2⟩⟩ := h1
  by_cases h : a ≥ -1
  . use (a+1).toNat
    have h1: (a+1) ≥ 0 := by omega
    have h2 := Int.toNat_of_nonneg h1
    have h3 : (((a + 1).toNat : ℕ) : ℚ) = ((a + 1 : ℤ) : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg h1
    rw [h3]
    simp_all
  . use 0
    push_neg at h
    have h1 : a + 1 < 0 := by omega
    have h2 : ↑(a + 1) < (0 : ℚ) := by exact_mod_cast h1
    simp at h2
    grind


/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Exercise 4.4.2 (a) -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  sorry

/-- Exercise 4.4.2 (b) -/
def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 4.4.2 (b) -/
def Rat.pos_infinite_descent : Decidable (∃ a:ℕ → {x: ℚ // 0 < x}, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  sorry

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  sorry

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . apply this _ _ _ (show -x>0 by simp; order) <;> grind
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx; norm_cast at hx; grind
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q; constructor
      . sorry
      exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    have h1 : Odd (p^2) := by
      sorry
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
