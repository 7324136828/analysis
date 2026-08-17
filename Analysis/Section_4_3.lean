import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers {lean}`ℚ` rather than the Section 4.2 rational numbers).

Note: to avoid notational conflict, we are using the standard Mathlib definitions of absolute
value and exponentiation.  As such, it is possible to solve several of the exercises here rather
easily using the Mathlib API for these operations.  However, the spirit of the exercises is to
solve these instead using the API provided in this section, as well as more basic Mathlib API for
the rational numbers that does not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
theorem abs_eq_abs (x: ℚ) : abs x = |x| := by grind


abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by grind

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by grind

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by grind

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by grind

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by grind

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by grind

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by simp_all

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by grind

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by grind

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by grind

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by grind

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff]
  grind

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff]
  grind

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by
  rw [close_iff]
  grind

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by
  rw [close_iff]
  grind

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  constructor <;> intro h
  . intro e he
    rw [close_iff]
    grind
  . by_contra hc
    set z := |x - y| /2
    have hz : z > 0 := by
      grind
    have h1 := h z hz
    rw [close_iff] at h1
    unfold z at h1
    have hw : 1 ≤ 1 / 2 := by
      grind
    have hw' : 1 / 2 <  1 := by
      grind
    have ww :  1 < 1 := by
      grind
    contradiction

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  rw [close_iff, close_iff]
  constructor <;> intro h
  . grind
  . grind

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
      rw [close_iff] at *
      grind

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by
      rw [close_iff] at *
      grind

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by
      rw [close_iff] at *
      grind


/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by
      rw [close_iff] at *
      grind


/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
      rw [close_iff] at *
      grind

theorem close_mul_right_induction {x y z :ℚ} (hxz: |x| ≤ |z|) (hy : 0 ≤ y) : |x| * y ≤ |z| * y := by
  rw [← abs_eq_abs]
  rw [← abs_eq_abs] at hxz
  unfold abs at *
  split_ifs with h1 h2
  . simp [h1] at hxz
    rw [← abs_eq_abs]
    rw [← abs_eq_abs] at hxz
    unfold abs at *
    split_ifs with h3 h4
    . simp [h3] at hxz
      nlinarith
    . simp [h3] at hxz
      simp [h4] at hxz
      nlinarith
    . simp [h3] at hxz
      simp [h4] at hxz
      nlinarith
  . simp [h1, h2] at hxz
    rw [← abs_eq_abs]
    rw [← abs_eq_abs] at hxz
    unfold abs at *
    split_ifs with h3 h4
    . simp [h3] at hxz
      nlinarith
    . simp [h3] at hxz
      simp [h4] at hxz
      nlinarith
    . simp [h3] at hxz
      simp [h4] at hxz
      nlinarith
  . simp_all
    rw [← abs_eq_abs]
    unfold abs at *
    split_ifs with h3 h4
    all_goals nlinarith


/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by
      rw [close_iff] at *
      have h1 := abs_mul (x - y) z
      have h2 : (x - y)*z = x * z - y * z := by
        grind
      rw [← h2]
      rw [h1]
      have hz : 0 ≤ |z| := by
        grind
      have he : |x - y| ≤ |ε| := by
        grind
      have hee : |ε| = ε := by
        grind
      have h3 := close_mul_right_induction he hz
      rw [hee] at h3
      exact h3


/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
  have h_simp : (x * z  - y * w) = (x - y) * z + (z - w) * y := by ring
  rw [close_iff] at *
  rw [h_simp]
  calc
  _ ≤  |(x - y) * z| + |(z - w) * y| := abs_add _ _
  _ =  |x - y| * |z| + |(z - w)| * |y| := by grind [abs_mul]
  _ ≤ _ := by gcongr

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := _root_.pow_zero x

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by
 grind

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  rw [← pow_mul']
  have : n * m = m * n := by grind
  simp_all

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with n hn;
  . simp_all
  . have h1 := (pow_add (x * y) 1 n).symm
    rw [h1]
    rw [hn]
    simp_all
    grind


/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  constructor <;> intro h
  . simp_all
  . rw [h]
    simp_all
    grind

theorem mul_non_neg {x y:ℚ} (hx : 0 ≤ x) (hy: 0 ≤ y) : 0 ≤ x * y := by
  exact mul_nonneg hx hy

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n hn;
  . simp_all
  . have r_318 : 1 = 1 := by rfl
    simp at hx hn ⊢
    have hxxn :  x ^ n * x = x ^ (n + 1)  := by grind
    have h1 := mul_non_neg hn hx
    rw [hxxn] at h1
    exact h1


/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with n hn;
  . simp_all
  . simp at hx hn ⊢
    have h1 := mul_pos hn hx
    have h2 :  x ^ n * x = x ^ (n+1) := by grind
    rw [h2] at h1
    exact h1

theorem pow_all_greater_than_pow {x y : ℚ} (hy: 0 ≤ y) (hxy2 : y < x) : ∀m:ℕ, y ^ (m+1) < x ^ (m+1) := by
  intro m
  induction' m with m hm
  . simp_all
  . have h3 := pow_nonneg (m+1) hy
    simp at h3
    have h2 := mul_lt_mul_of_nonneg hm hxy2 h3 hy
    have h4 :  y ^ (m + 1 + 1) =  y ^ (m + 1) * y := by grind
    have h5 :  x ^ (m + 1 + 1) =  x ^ (m + 1) * x := by grind
    rw [h4, h5]
    exact h2

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  simp_all
  induction' n with n hn;
  . simp_all
  . have hxy2 : y < x ∨ y = x := by
      grind
    rcases hxy2 with hxy2 | hxy2
    . have h1 : 1 = 1 := by grind
      have hyxm := pow_all_greater_than_pow hy hxy2 n
      grind
    . rw [hxy2]


/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  simp_all
  set m := n - 1
  have hm : m + 1 = n := by omega
  have h_pos := pow_all_greater_than_pow hy hxy m
  simp [hm] at h_pos
  exact h_pos

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := by
  simp_all
/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by
  convert zpow_neg x 3;
  ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  exact (Rat.zpow_add hx n m).symm

theorem zpow_neg_2 (x:ℚ) (n:ℤ) : (x ^ n)⁻¹ = x ^ (-n) := by
  rcases n with n | n
  . simp_all
  . simp_all
    rfl

theorem negSucc_elim (m : ℕ): Int.negSucc m = -(m+1) := by
  omega

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  rcases n with n | n
  . rcases m with m | m
    . simp_all
      exact pow_mul x m n
    . simp_all
      have h1 := pow_mul x (m+1) n
      rw [h1]
      have h2 := negSucc_elim m
      rw [h2]
      have h3 : n * (-(m + 1):ℤ) = -(n * (m + 1):ℤ) := by
        grind
      rw [h3]
      rw [← zpow_neg_2]
      rfl
  . rcases m with m | m
    . simp_all
      have h0 := pow_mul x m (n+1)
      rw [h0]
      have h1 := negSucc_elim n
      rw [h1]
      have h2 : (-((n + 1):ℤ) * m) = (- ((n+1) * m)) := by
        grind
      rw [h2]
      rw [← zpow_neg_2]
      rfl
    . simp_all
      have h0 := pow_mul x (m+1) (n+1)
      rw [h0]
      have h1 := negSucc_elim n
      have h2 := negSucc_elim m
      rw [h1, h2]
      have h3 : -((n + 1):ℤ) * (-((m + 1):ℤ)) = (n + 1) * (m+1) := by
        grind
      rw [h3]
      rfl



/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := by
  rcases n with n | n
  . simp_all
    exact mul_pow x y n
  . simp_all
    have hxy : ((x * y) ^ (n + 1))⁻¹ = 1 / ((x * y) ^ (n + 1)) := by grind
    have hx : (x ^ (n + 1))⁻¹ = 1 / (x ^ (n + 1)) := by grind
    have hy : (y ^ (n + 1))⁻¹ = 1 / (y ^ (n + 1)) := by grind
    rw [hxy, hx, hy]
    have hz : 1 / x ^ (n + 1) * (1 / y ^ (n + 1)) = 1 / (x ^ (n + 1) * y ^ (n + 1)) := by grind
    rw [hz]
    have hw := mul_pow x y (n+1)
    rw [hw]


/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  rcases n with n | n
  . simp_all
  . simp_all

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  simp_all
  have hn1 : n ≥ 0 := by grind
  have hny : y ≥ 0 := by grind
  have h1 := Int.toNat_of_nonneg hn1
  -- pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  have h2 := pow_ge_pow x y n.toNat  hxy hny
  simp at h2
  rw [← h1]
  set z := n.toNat
  rw [pow_eq_zpow, pow_eq_zpow]
  exact h2

-- theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
theorem zpow_gt_zpow {x y:ℚ} {n:ℤ} (hxy: x > y) (hy: y > 0) (hn: n > 0): x^n > y^n := by
  simp_all
  have hn1 : n ≥ 0 := by grind
  have hny : y ≥ 0 := by grind
  have h1 := Int.toNat_of_nonneg hn1
  -- pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  have h2 := pow_gt_pow x y n.toNat  hxy hny (by aesop)
  simp at h2
  rw [← h1]
  set z := n.toNat
  rw [pow_eq_zpow, pow_eq_zpow]
  exact h2


theorem q_mul_pos {a b c:ℚ} (hc: c > 0) (hxy : a ≤ b) : a * c ≤ b * c := by
  simp_all

theorem qpow_ge_simp_neg {x y:ℚ} (hx: x > 0) (hy: y > 0) (hxy : x⁻¹ ≥ y⁻¹) : x ≤ y := by
  simp_all
  have h1 := q_mul_pos hy (q_mul_pos hx hxy)
  have h2 : y⁻¹ * x * y = x := by
    grind
  have h3 : x⁻¹ * x * y = y := by
    grind
  rw [h2, h3] at h1
  exact h1

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  have hnn : (-n) > 0 := by grind
  have h1 := zpow_ge_zpow hxy hy hnn
  iterate 2 rw [← zpow_neg_2] at h1
  have hx : x > 0 := by grind
  have hxn := zpow_pos n hx
  have hyn := zpow_pos n hy
  exact qpow_ge_simp_neg hxn hyn h1

theorem pow_inj {x y:ℚ} (hx: x > 0) (hy : y > 0)(n:ℕ)(hxy: x^(n+1) = y^(n+1)): x = y := by
  have h1 := lt_trichotomy x y
  have h2 : (n+1) > 0 := by omega
  rcases h1 with h1 | h1 | h1
  . have ha : y > x := by omega
    replace h2 := pow_gt_pow y x (n+1) ha (by grind) h2
    simp at h2
    linarith
  . simp_all
  . replace h2 := pow_gt_pow x y (n+1) h1 (by grind) h2
    simp at h2
    linarith




/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  rcases n with n | n
  . simp_all
    set m := n - 1
    have hm : m + 1 = n := by omega
    have h1 := pow_inj hx hy m
    rw [hm] at h1
    exact h1 hxy
  . simp_all
    have h1 := pow_inj hx hy n
    exact h1 hxy


/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : |x|^n = |x^n| := by
  simp_all

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by
  induction' N with N hN;
  . simp_all
  . have h1 :  2 ^ (N + 1) = 2 ^ N * 2 := by
      grind
    by_cases h2 : N = 0
    . rw [h2]
      simp_all
    . have h_ : 1 = 1 := by rfl
      have h3 : N * 2≥ N + 1 := by omega
      rw [h1]
      have h4 : 2 ^ N * 2 ≥ N * 2 := by omega
      grind
