import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of {lean}`ℕ`.

- Equivalence with the Mathlib integers {name}`_root_.Int` (or {lean}`ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by
      intro x
      rfl
    symm := by
      intro x y hxy
      exact hxy.symm
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2;
      simp_all
      have h3 := congrArg₂ (· + ·) h1 h2;
      simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by
    apply n.ind _;
    intro ⟨ a, b ⟩;
    use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [eq] at *
    omega)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1]
  rw [mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    have hx1 := Quotient.eq.mpr h1
    have hx2 := (Quotient.eq.mpr h2)
    exact mul_congr hx1 hx2
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq];
  simp only [eq];
  simp only [add_zero];
  rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq];
  simp only [eq];
  simp only [add_zero];


example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by
  rw [Int.ofNat_eq]
  rw [Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  refine ⟨?_, by aesop⟩
  intro h
  exact (natCast_inj n 0).mp h

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ hab
    simp
    simp at hab
    apply (Int.eq _ _ _ _).mpr
    calc
      _  =  b1 + a2 := by abel
      _  =  a1 + b2 := hab.symm
      _  =  b2 + a1 := by abel
  )

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right;
    right;
    refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq];
    simp_rw [neg_eq];
    simp_rw [eq]
    abel
  . left;
    simp_rw [ofNat_eq];
    simp_rw [eq];
    simp_rw [add_zero];
    simp_rw [zero_add];
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left;
  refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq];
  simp_rw [eq];
  abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, h1, h2 ⟩ ⟩;
  simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩;
  simp_rw [←natCast_ofNat] at hn
  simp_rw [natCast_eq] at hn
  simp_rw [neg_eq] at hn
  simp_rw [eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩;
  simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms (by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩
    change ((a1 + b1) —— (a2 + b2)) + (c1 —— c2) = (a1 ——  a2) + (( (b1 + c1) —— (b2 + c2)))
    change ((a1 + b1 + c1) ——  (a2 + b2 + c2) ) = ((a1 + (b1 + c1)) ——  (a2 + (b2 + c2)) )
    have h1 : (a1 + b1 + c1) = (a1 + (b1 + c1)) := by abel
    have h2 : (a2 + b2 + c2) = (a2 + (b2 + c2)) := by abel
    rw [h1, h2]
  ) (by
      rintro ⟨a1, a2⟩
      change ((0 + a1) —— (0 + a2)) = a1 —— a2
      have h1 : 0 + a1 = a1 := by omega
      have h2 : 0 + a2 = a2 := by omega
      rw [h1, h2]
  ) (by
      rintro ⟨a1, a2⟩
      change -(a1 —— a2) + (a1 —— a2) = 0 —— 0
      simp_rw [neg_eq]
      simp_rw [add_eq]
      simp_rw [eq]
      simp
      abel
  )

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩
    change (a1 —— a2) + (b1 —— b2) = (b1 —— b2) + (a1 —— a2)
    simp_rw [add_eq]
    simp_rw [eq]
    abel

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩
    change (a1 —— a2) * (b1 —— b2) = (b1 —— b2) * (a1 —— a2)
    simp_rw [mul_eq]
    simp_rw [eq]
    -- a1 * b1 + a2 * b2 + (b1 * a2 + b2 * a1) = b1 * a1 + b2 * a2 + (a1 * b2 + a2 * b1)
    ring
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq];
    congr 1 <;>
    ring
  one_mul := by
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    change (1 —— 0) * (a —— b) = (a —— b)
    simp_rw [mul_eq];
    congr 1 <;>
    ring
  mul_one := by
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    change  (a —— b) * (1 —— 0) = (a —— b)
    simp_rw [mul_eq];
    congr 1 <;>
    ring

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    intro a b c
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
    simp_rw [mul_eq];
    simp_rw [add_eq];
    simp_rw [mul_eq];
    simp_rw [eq];
    ring
  right_distrib := by
    intro a b c
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
    simp_rw [mul_eq];
    simp_rw [add_eq];
    simp_rw [mul_eq];
    simp_rw [eq];
    ring
  zero_mul := by
    intro a
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    change  (0 —— 0) * (a1 —— a2) = (0 —— 0)
    simp_rw [mul_eq];
    simp_rw [eq];
    ring
  mul_zero := by
    intro a
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    change  (a1 —— a2) * (0 —— 0) = (0 —— 0)
    simp_rw [mul_eq];
    simp_rw [eq];
    ring

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
    simp_rw [natCast_eq];
    have h1 : a —— 0 = a —— b + (b —— 0) := by
      rw [add_eq]
      rw [eq]
      simp
    rw [h1]
    simp

-- theorem Int.distribution_law {a1 a2 b1 b2 : ℕ} : (a1 - a2) * (b1 - b2)  = (a1 * b1 + a2 * b2 - a1 * b2 - a2 * b1) := by
--   simp_rw [Nat.mul_sub_left_distrib]
--   simp_rw [Nat.mul_sub_right_distrib]








/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases h_eq : a = 0
  . left
    exact h_eq
  . right
    have h1 := trichotomous a
    have h2 := trichotomous b
    simp [h_eq] at h1
    unfold IsPos at *
    unfold IsNeg at *
    rcases h1 with h1 | h1
    . rcases h2 with h2 | h2 | h2
      . exact h2
      . obtain ⟨n1, hn1⟩ := h1
        obtain ⟨n2, hn2⟩ := h2
        rw [hn1.2, hn2.2] at h
        change ((n1 —— 0) * (n2 —— 0) = 0 —— 0) at h
        simp_rw [mul_eq] at h
        simp_rw [eq] at h
        simp at h
        rcases h with h | h
        . simp [h] at hn1
        . simp [h] at hn2
      . obtain ⟨n1, hn1⟩ := h1
        obtain ⟨n2, hn2⟩ := h2
        rw [hn1.2, hn2.2] at h
        change ((n1 —— 0) * (0 —— n2) = 0 —— 0) at h
        simp_rw [mul_eq] at h
        simp_rw [eq] at h
        simp at h
        rcases h with h | h
        . simp [h] at hn1
        . simp [h] at hn2
    . rcases h2 with h2 | h2 | h2
      . exact h2
      . obtain ⟨n1, hn1⟩ := h1
        obtain ⟨n2, hn2⟩ := h2
        rw [hn1.2, hn2.2] at h
        change ((0 —— n1) * (n2 —— 0) = 0 —— 0) at h
        simp_rw [mul_eq] at h
        simp_rw [eq] at h
        simp at h
        rcases h with h | h
        . simp [h] at hn1
        . simp [h] at hn2
      . obtain ⟨n1, hn1⟩ := h1
        obtain ⟨n2, hn2⟩ := h2
        rw [hn1.2, hn2.2] at h
        change ((0 —— n1) * (0 —— n2) = 0 —— 0) at h
        simp_rw [mul_eq] at h
        simp_rw [eq] at h
        simp at h
        rcases h with h | h
        . simp [h] at hn1
        . simp [h] at hn2


/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    have h1 := trichotomous c
    simp [hc] at h1
    unfold IsPos at *
    unfold IsNeg at *
    rcases h1 with h1 | h1 <;> obtain ⟨n, ⟨hn1, hn2⟩⟩ := h1;
    . change c = (n —— 0) at hn2
      simp [hn2] at h
      simp_rw [mul_eq] at h
      simp_rw [eq] at *
      simp at h
      simp_rw [← right_distrib] at h
      exact Nat.mul_right_cancel hn1 h
    . change c = (0 —— n) at hn2
      simp [hn2] at h
      simp_rw [mul_eq] at h
      simp_rw [eq] at *
      simp at h
      simp_rw [← right_distrib] at h
      have h1 := Nat.mul_right_cancel hn1 h
      conv at h1 =>
        lhs
        rw [add_comm]
      rw [h1]
      rw [add_comm]



/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  constructor <;> intro h; simp only [lt_iff] at h;
  . obtain ⟨⟨t, ht⟩, hne⟩ := h
    use t
    constructor
    . intro h1
      rw [h1] at ht
      simp at ht
      symm at ht
      contradiction
    . exact ht
  . obtain ⟨n, ⟨hn1, hn2⟩⟩ := h
    apply (lt_iff _ _).mpr
    constructor
    . use n
    . intro hab
      rw [hab] at hn2
      simp at hn2
      simp at hn1
      have hn1' := (natCast_inj _ _).mp hn2
      contradiction

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  simp only [lt_iff] at *
  obtain ⟨⟨t, ht⟩, hne⟩ := h
  constructor
  . use t
    conv =>
      lhs
      rw [add_comm]
    conv =>
      rhs
      rw [add_comm]
      rhs
      rw [add_comm]
    conv =>
      rhs
      rw [add_comm]
    rw [ht]
    rw [add_assoc]
  . intro hab
    have h1 := add_right_cancel hab
    contradiction


/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  simp only [lt_iff] at *
  obtain ⟨⟨t, ht1⟩, ht2⟩ := hab
  obtain ⟨⟨m, hm1⟩, hm2⟩ := hc
  constructor
  . use (t * m)
    rw [ht1]
    rw [right_distrib]
    conv =>
      lhs
      rhs
      rw [hm1]
    simp
  . intro hm3
    have h := mul_right_cancel₀ a b c hm3 (hm2.symm)
    contradiction

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  simp only [lt_iff] at *
  obtain ⟨⟨t, ht1⟩, ht2⟩ := h
  constructor
  . use t
    rw [ht1]
    simp
  . intro hab
    simp at hab
    simp [hab] at ht2

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  simp only [le_iff] at *
  obtain ⟨t, ht2⟩ := h
  use t
  rw [ht2]
  simp

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  simp only [lt_iff] at *
  obtain ⟨⟨ab, hab1⟩, hab2⟩ := hab
  obtain ⟨⟨bc, hbc1⟩, hbc2⟩ := hbc
  constructor
  . use (ab + bc)
    rw [hbc1]
    rw [hab1]
    simp
    rw [add_assoc]
  . intro hac
    rw [hac] at hab1
    rw [hab1] at hbc1
    have h1 : c + 0 = c := by simp
    conv at hbc1 =>
      lhs
      rw [← h1]
    have hbc1' : c + 0 = c + (↑ab + ↑bc) := by
        simpa [add_assoc] using hbc1
    have h2 : (0:Int) =  ↑(ab + bc) := by
      exact add_left_cancel hbc1'
    have h3 := (natCast_inj _ _).mp h2
    have ⟨h4,h5⟩ := add_eq_zero.mp h3.symm
    simp [h4] at hab1
    rw [← hab1] at hac
    contradiction


/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  simp only [lt_iff] at *
  have h1 := trichotomous (b - a)
  rcases h1 with h1 | h1 | h1
  . right; right;
    change b - a = 0  ——  0 at h1
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    simp_rw [sub_eq] at *
    simp_rw [neg_eq] at *
    simp_rw [add_eq] at *
    simp_rw [eq] at *
    simp at h1
    simp [h1]
    rw [add_comm]
  . obtain ⟨t, ⟨ht1, ht2⟩⟩ := h1
    right; left;
    constructor
    . use t
      rw [← ht2]
      simp
    . intro hab
      rw [hab] at ht2
      simp at ht2
      replace ht2 := (natCast_inj _ _).mp ht2
      simp [← ht2] at ht1
  . obtain ⟨t, ⟨ht1, ht2⟩⟩ := h1
    change b - a = -(t —— 0) at ht2
    simp_rw [neg_eq] at *
    left;
    constructor
    . use t
      change a = b + (t —— 0)
      obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
      obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
      simp_rw [sub_eq] at *
      simp_rw [neg_eq] at *
      simp_rw [add_eq] at *
      simp_rw [eq] at *
      simp_all
      conv at ht2 =>
        rhs
        rw [add_comm]
      rw [← ht2]
      ring
    . intro hab
      simp [hab] at ht2
      change  0 —— 0 = 0 —— t at ht2
      rw [eq] at ht2
      simp at ht2
      rw [ht2] at ht1
      omega

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  rintro ⟨⟨⟨c, hc1⟩, hc2⟩, ⟨⟨d, hd1⟩, hd2⟩⟩
  simp [hc1] at hd1
  have h1 : b + 0 = b := by simp
  conv at hd1 =>
    lhs
    rw [← h1]
  have hd1' : b + 0 = b + (↑c + ↑d) := by
      simpa [add_assoc] using hd1
  have h2 : (0:Int) =  ↑(c + d) := by
    exact add_left_cancel hd1'
  have h3 := (natCast_inj _ _).mp h2
  have ⟨h4,h5⟩ := add_eq_zero.mp h3.symm
  simp [h4] at hc1
  contradiction

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  rintro ⟨⟨⟨c, hc1⟩, hc2⟩, hab⟩
  rw [hab] at hc2
  contradiction


/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  rintro ⟨⟨⟨c, hc1⟩, hc2⟩, hab⟩
  rw [hab] at hc2
  contradiction


/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        simp only [le_iff] at *
        simp only [le_iff_exists_add] at *
        obtain ⟨e, he⟩ := h
        use e
        change  c —— d = a —— b + (e —— 0)
        simp_rw [add_eq]
        simp_rw [eq]
        simp
        rw [add_comm]
        rw [he]
        ring
      | isFalse h =>
        apply isFalse
        rintro ⟨e, he⟩
        change c —— d = a —— b + (e —— 0) at he
        simp_rw [add_eq] at he
        simp_rw [eq] at he
        simp at he
        conv at he =>
          lhs
          rw [add_comm]
        simp only [le_iff_exists_add] at *
        push_neg at h
        have he' := h e
        rw [he] at he'
        omega
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by simp


/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by
    intro a
    use 0
    simp
  le_trans := by
    intro a b c hab hbc
    obtain ⟨d, hd⟩ := hab
    obtain ⟨e, he⟩ := hbc
    simp [hd] at he
    use (d + e)
    rw [he]
    simp
    rw [add_assoc]
  lt_iff_le_not_ge := by
    intro a b
    simp only [lt_iff] at *
    constructor <;> rintro ⟨⟨m, hm⟩, h2⟩
    . constructor
      . use m
      . intro h3
        obtain ⟨n, hn⟩ := h3
        simp [hn] at hm
        have hd1' : b + 0 = b + (↑n + ↑m) := by
            simpa [add_assoc] using hm
        have h4 : (0:Int) =  ↑(n + m) := by
          exact add_left_cancel hd1'
        have h5 := (natCast_inj _ _).mp h4
        have ⟨h6,h7⟩ := add_eq_zero.mp h5.symm
        simp [h6] at hn
        contradiction
    . constructor
      . use m
      . intro hx
        simp [hx] at h2
        simp only [le_iff] at *
        push_neg at h2
        have h3 := h2 0
        simp at h3
  le_antisymm := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    simp [hc] at hd
    have hd1' : a + 0 = a + (↑c + ↑d) := by
        simpa [add_assoc] using hd
    have h4 : (0:Int) =  ↑(c + d) := by
      exact add_left_cancel hd1'
    have ⟨h6,h7⟩ := add_eq_zero.mp ((natCast_inj _ _).mp h4).symm
    simp [h6] at hc
    exact hc.symm
  le_total := by
    intro a b
    have hab := trichotomous' a b
    simp only [lt_iff] at *
    simp only [le_iff] at *
    rcases hab with hab | hab | hab
    . right
      obtain ⟨⟨e, he⟩, he2⟩ := hab
      use e
    . left
      obtain ⟨⟨e, he⟩, he2⟩ := hab
      use e
    . right
      use 0
      simp
      exact hab
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  change (-(1 —— 0) * a = -a)
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  simp_rw [neg_eq]
  simp_rw [mul_eq]
  simp_rw [eq]
  simp


/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  set P : Int → Prop := fun x ↦ x ≥ 0
  use P
  constructor
  . constructor
    . unfold P
      rfl
    . intro n hn
      unfold P at *
      simp only [le_iff] at *
      obtain ⟨t, ht⟩ := hn
      use (t + 1)
      rw [ht]
      simp
  . push_neg
    use (0 —— 1)
    unfold P
    push_neg
    simp only [lt_iff] at *
    constructor
    . use 1
      change (0 —— 0) = 0 —— 1 + (1 —— 0)
      rw [add_eq]
      rw [eq]
    . intro h
      change 0 —— 1 = (0 —— 0) at h
      rw [eq] at h
      simp at h

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  simp only [le_iff] at *
  obtain ⟨t, ht⟩ := h
  use (t * t)
  simp at *
  rw [ht]

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  have h1 := le_total 0 n
  rcases h1 with h1 | h1
  . exact sq_nonneg_of_pos n h1
  . simp only [le_iff] at *
    obtain ⟨t, ht⟩ := h1
    use (t * t)
    simp at *
    have h2 : n = -t := by
      obtain ⟨ a1, a2, rfl ⟩ := eq_diff n
      change (a1 —— a2) = (0 —— t)
      change  0 —— 0 = a1 —— a2 + (t —— 0 ) at ht
      rw [add_eq] at *
      rw [eq] at *
      simp at ht
      simp
      rw [ht]
    rw [h2]
    simp

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have ⟨t, ht⟩ := sq_nonneg n
  use t
  simp at ht
  exact ht

/--
  Not in textbook: create an equivalence between {name}`Int` and {lean}`ℤ`.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    sorry)
  invFun := sorry
  left_inv n := sorry
  right_inv n := sorry

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by sorry
  map_mul' := by sorry
  map_le_map_iff' := by sorry

end Section_4_1
