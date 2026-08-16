import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.2" rationals, `Section_4_2.Rat`, as formal quotients `a // b` of
  integers `a b:ℤ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_2.PreRat`, which consists of formal quotients without any equivalence imposed.)

- Field operations and order on these rationals, as well as an embedding of {lean}`ℕ` and {lean}`ℤ`.

- Equivalence with the Mathlib rationals {name}`_root_.Rat` (or {lean}`ℚ`), which we will use going forward.

Note: here (and in the sequel) we use Mathlib's natural numbers {lean}`ℕ` and integers {lean}`ℤ` rather than
the Chapter 2 natural numbers and Section 4.1 integers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by
      rintro ⟨a, b⟩
      rfl
    symm := by
      rintro ⟨a, b⟩ ⟨c, d⟩
      simp
      intro hadcb
      exact hadcb.symm
    trans := by
      rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
      simp
      intro hadcb hcded
      have h1 := congr(f * $hadcb)
      rw [← mul_assoc, ← mul_assoc] at h1
      conv at h1 =>
        rhs
        rw [mul_comm]
        rhs
        rw [mul_comm]
      rw [hcded] at h1
      conv at h1 =>
        rhs
        rw [← mul_assoc]
      simp at h1
      rcases h1 with h1 | h1
      . conv at h1 =>
          lhs
          rw [mul_comm]
        rw [h1]
        rw [mul_comm]
      . contradiction
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [formalDiv]
  simp [hb]
  simp [hd]
  simp [Quotient.eq]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n;
  intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv]
  simp [h]

/--
  Decidability of equality. Hint: modify the proof of {lean}`DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the {name}`Quotient` API.

-/
instance Rat.decidableEq : DecidableEq Rat := by
  intro a b
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n = Quotient.mk PreRat.instSetoid m) := by
        intro ⟨ a,b, hab⟩ ⟨ c,d, hcd ⟩
        simp [Quotient.eq]
        exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this



/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Quotient.eq]
    linear_combination d * d' * h3 + b * b' * h4
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Quotient.eq]
    have h5 := congr($h4 * (a * b'))
    conv at h5 =>
      rhs
      rw [h3]
    linear_combination h5
  )

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩
    simp_all [Quotient.eq]
  )

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by
  change ((n + 1) // 1) = (n // 1) + (1 // 1)
  rw [add_eq]
  simp
  omega
  omega


/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  change (a // 1) + (b // 1) = ((a+b) // 1)
  rw [add_eq]
  simp
  omega
  omega



/-- intCast distributes over multiplication -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  change (a // 1) * (b // 1) = (a*b // 1)
  rw [mul_eq]
  simp
  change (a * b) // 1 = (a // 1) * b // 1
  rw [mul_eq]
  simp
  omega
  omega
  omega
  omega


/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro a1 a2 ha12
  simp at ha12
  change a1 // 1 = a2 // 1 at ha12
  simp [Quotient.eq] at ha12
  exact ha12

/--
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    -- hint: split into the `a=0` and `a≠0` cases
    intro ⟨a1,a2, ha12⟩ ⟨b1,b2,hb12⟩ hab
    simp_all
    simp [formalDiv]
    split_ifs with h1 h2 h3
    . simp
    . simp [h1, h2] at hab
      contradiction
    . simp [Quotient.eq]
      simp [h1, h3] at hab
      contradiction
    . simp [Quotient.eq]
      conv =>
        lhs
        rw [mul_comm]
      rw [← hab]
      rw [mul_comm]
)

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- can also use `observe hbd : b*d ≠ 0` here
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- can also use `observe hdf : d*f ≠ 0` here
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- can also use `observe hbdf : b*d*f ≠ 0` here
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
)
 (by
  intro a
  obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
  change  (0 // 1) + a1 // a2 = a1 // a2
  rw [add_eq]
  simp
  omega
  exact ha12
 ) (by
    intro a
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    rw [neg_eq]
    rw [add_eq]
    simp_all
    have h1 := Int.mul_comm a1 a2
    rw [h1]
    simp
    change  0 // (a2 * a2) = 0 // 1
    rw [eq]
    simp
    simp [ha12]
    omega
    omega
    omega
    omega
 )

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by
    intro a b
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, hb12, rfl ⟩ := eq_diff b
    rw [add_eq]
    rw [add_eq]
    rw [eq]
    ring
    simp [ha12, hb12]
    simp [ha12, hb12]
    simp [hb12]
    simp [ha12]
    simp [ha12]
    simp [hb12]

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := by
    intro a b
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, hb12, rfl ⟩ := eq_diff b
    rw [mul_eq]
    rw [mul_eq]
    rw [eq]
    ring
    simp [ha12, hb12]
    simp [ha12, hb12]
    simp [hb12]
    simp [ha12]
    simp [ha12]
    simp [hb12]
  mul_assoc := by
    intro a b c
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, hb12, rfl ⟩ := eq_diff b
    obtain ⟨ c1, c2, hc12, rfl ⟩ := eq_diff c
    rw [mul_eq]
    rw [mul_eq]
    rw [mul_eq]
    rw [mul_eq]
    rw [eq]
    ring
    all_goals aesop
  one_mul := by
    intro a
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    change (1 // 1) * a1 // a2 = a1 // a2
    rw [mul_eq]
    rw [eq]
    simp
    simp [ha12]
    simp [ha12]
    omega
    simp [ha12]
  mul_one := by
    intro a
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    change a1 // a2 * (1//1) = a1 // a2
    rw [mul_eq]
    rw [eq]
    simp
    simp [ha12]
    simp [ha12]
    omega
    omega

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := by
    intro a b c
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, hb12, rfl ⟩ := eq_diff b
    obtain ⟨ c1, c2, hc12, rfl ⟩ := eq_diff c
    rw [mul_eq]
    rw [mul_eq]
    rw [add_eq]
    rw [mul_eq]
    rw [add_eq]
    rw [eq]
    ring
    simp [ha12, hb12, hc12]
    simp [ha12, hb12, hc12]
    simp [ha12, hb12]
    simp [ha12, hc12]
    omega
    simp [hb12, hc12]
    omega
    omega
    omega
    omega
    omega
    omega

  right_distrib := by
    intro a b c
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, hb12, rfl ⟩ := eq_diff b
    obtain ⟨ c1, c2, hc12, rfl ⟩ := eq_diff c
    rw [mul_eq]
    rw [mul_eq]
    rw [add_eq]
    rw [mul_eq]
    rw [add_eq]
    rw [eq]
    ring
    simp [ha12, hb12, hc12]
    simp [ha12, hb12, hc12]
    simp [ha12, hc12]
    simp [hc12, hb12]
    simp [ha12, hb12]
    omega
    omega
    omega
    omega
    omega
    omega
    omega
  zero_mul := by
    intro a
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    change ((0 // 1) * a1 // a2 = (0 // 1))
    rw [mul_eq]
    rw [eq]
    simp
    omega
    omega
    omega
    omega
  mul_zero := by
    intro a
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    change ((a1 // a2) * (0 // 1) = (0 // 1))
    rw [mul_eq]
    rw [eq]
    simp
    omega
    omega
    omega
    omega
  mul_assoc := by
    intro a b c
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, hb12, rfl ⟩ := eq_diff b
    obtain ⟨ c1, c2, hc12, rfl ⟩ := eq_diff c
    rw [mul_eq]
    rw [mul_eq]
    rw [mul_eq]
    rw [mul_eq]
    rw [eq]
    ring
    all_goals aesop
  -- Usually CommRing will generate a natCast instance and a proof for this.
  -- However, we are using a custom natCast for which `natCast_succ` cannot
  -- be proven automatically by `rfl`. Luckily we have proven it already.
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by
  intro a1 a2 ha12
  simp at ha12
  obtain ⟨q1, q2, hq1, hq2⟩ := a1
  obtain ⟨p1, p2, hp1, hp2⟩ := a2
  simp_all
  change q1 // q2 = p1 // p2 at ha12
  rw [eq] at ha12
  unfold Nat.Coprime  Nat.gcd at hq2 hp2
  by_cases h : q1 = p1
  . simp [h] at ha12
    rcases ha12 with ha12 | ha12
    . exact And.intro h ha12.symm
    . simp [ha12] at hp2
      simp [ha12] at h
      simp [h] at hq2
      omega
  . split_ifs at hp2 hq2 with hi1 hi2 hi3
    . simp_all
    . simp_all
    . simp_all
    . simp_all
      have ha12' := congrArg Int.natAbs ha12
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at ha12'

      have hq2_dvd : q2 ∣ p2 := by
        apply (hq2.dvd_mul_left).mp
        rw [ha12']
        exact Nat.dvd_mul_left q2 p1.natAbs

      have hp2_dvd : p2 ∣ q2 := by
        apply (hp2.dvd_mul_left).mp
        rw [← ha12']
        exact Nat.dvd_mul_left p2 q1.natAbs

      have hden : q2 = p2 :=
        Nat.dvd_antisymm hq2_dvd hp2_dvd

      have hp2z : (p2 : ℤ) ≠ 0 := by omega

      have hnum : q1 = p1 := by
        apply mul_right_cancel₀ hp2z
        simpa [hden] using ha12

      simp_all
  omega
  omega


theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq
  <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by
    use 0
    use 1
    intro h
    change 0 // 1 = 1 // 1 at h
    rw [eq] at h
    simp at h
    all_goals omega
  mul_inv_cancel := by
    intro a ha
    change a ≠ 0 // 1 at ha
    change  a * a⁻¹ = 1 // 1
    obtain ⟨ a1, a2, ha12, rfl ⟩ := eq_diff a
    rw [inv_eq]
    rw [mul_eq]
    rw [eq]
    simp
    ring
    . intro hb
      simp [ha12] at hb
      simp [hb] at ha
      rw [eq] at ha
      push_neg at ha
      simp at ha
      . omega
      . omega
    . omega
    . omega
    . intro hb
      simp [hb] at ha
      rw [eq] at ha
      push_neg at ha
      simp at ha
      . omega
      . omega
    . omega
  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den:ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    rw [coe_Int_eq]
    rw [coe_Nat_eq]
    rw [div_eq]
    rw [inv_eq, mul_eq, eq]
    <;>
    simp [num, den, q.den_nz]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by
    rw [Rat.div_eq, Rat.inv_eq, Rat.mul_eq, Rat.eq]
    all_goals omega

/-- Definition of subtraction -/
theorem Rat.sub_eq (a b:Rat) : a - b = a + (-b) := by rfl

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by
    intro x y
    change ((x + y) // 1) = (x // 1) + (y // 1)
    rw [add_eq, eq]
    all_goals omega
  map_mul' := by
    intro x y
    change ((x * y) // 1) = (x // 1) * (y // 1)
    rw [mul_eq, eq]
    all_goals omega

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by
    obtain ⟨ a, b, hab, rfl ⟩ := eq_diff x
    obtain h_lt_b | rfl_b | h_gt_b := _root_.trichotomous (r := LT.lt) b 0
    . obtain h_lt_a | rfl_a | h_gt_a := _root_.trichotomous (r := LT.lt) a 0
      . right; left;
        use (-a)
        use (-b)
        constructor
        . omega
        . constructor
          . omega
          . change a // b = ((-a) // 1) / ((-b) // 1)
            rw [div_eq, inv_eq, mul_eq, eq]
            simp
            all_goals omega
      . left
        change a // b = 0 // 1
        rw [eq]
        all_goals omega
      . right; right;
        use (a // (-b))
        constructor
        . use a
          use (-b)
          simp_all
          change  a // (-b) = (a // 1) / (-(b // 1))
          rw [div_eq, neg_eq, inv_eq, mul_eq, eq]
          simp_all
          all_goals omega
        . rw [neg_eq, eq]
          simp_all
          all_goals omega
    . contradiction
    . obtain h_lt_a | rfl_a | h_gt_a := _root_.trichotomous (r := LT.lt) a 0
      . right; right;
        use ( (-a) // b)
        constructor
        . use (-a)
          use b
          simp_all
          change  (-a) // b = -(a // 1) / (b // 1)
          rw [div_eq, neg_eq, inv_eq, mul_eq, eq]
          simp_all
          all_goals omega
        . rw [neg_eq, eq]
          simp_all
          all_goals omega
      . left
        change a // b = 0 // 1
        rw [eq]
        all_goals omega
      . right; left;
        use a
        use b
        simp_all
        change a // b = ((a) // 1) / ((b) // 1)
        rw [div_eq, inv_eq, mul_eq, eq]
        simp_all
        all_goals omega

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  unfold isPos at h2
  obtain ⟨a, b, ⟨hab1, hab2, hab3⟩⟩ := h2
  change 0 // 1 = (a // 1) / (b // 1) at hab3
  rw [div_eq, inv_eq, mul_eq, eq] at hab3
  simp at hab3
  all_goals omega


/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  unfold isNeg at h2
  obtain ⟨r, hr⟩ := h2
  have h3 := not_zero_and_pos (r)
  push_neg at h3
  have h4 : r = 0 := by
    aesop
  have h5 := h3 h4
  have h6 := hr.1
  contradiction

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by
  obtain ⟨x1, x2, hx12, rfl ⟩ := eq_diff x
  rintro ⟨h1, h2⟩
  unfold isPos at h1
  unfold isNeg at h2
  obtain ⟨a, b, ⟨hab1, hab2, hab3⟩⟩ := h1
  obtain ⟨r, ⟨hr1, hr2⟩⟩ := h2
  obtain ⟨r1, r2, hr12, rfl ⟩ := eq_diff r
  unfold isPos at hr1
  obtain ⟨c, d, ⟨hcd1, hcd2, hcd3⟩⟩ := hr1
  change x1 // x2 = (a // 1) / (b // 1) at hab3
  change r1 // r2 = (c // 1) / (d // 1) at hcd3
  rw [div_eq, neg_eq, inv_eq, mul_eq, eq] at *
  simp_all
  obtain h_lt_r1 | rfl_r1 | h_gt_r1 := _root_.trichotomous (r := LT.lt) r1 0
  . have hr2_neg_1 : (c * r2) < 0 := by nlinarith
    have hr2_neg : r2 < 0 := by nlinarith [hr2_neg_1, hcd1]
    obtain h_lt_x1 | rfl_x1 | h_gt_x1 := _root_.trichotomous (r := LT.lt) x1 0
    . have hx2_pos : x2 > 0 := by nlinarith
      have hx2_neg : x2 < 0 := by nlinarith
      omega
    . simp [rfl_x1] at hab3
      rcases hab3 with hab3 | hab3
      . omega
      . omega
    . have hx2_pos : x2 > 0 := by nlinarith
      have hx2_neg : x2 < 0 := by nlinarith
      omega
  . simp [rfl_r1] at hcd3
    rcases hcd3 with hcd3 | hcd3
    . omega
    . omega
  . have hr2_pos : r2 > 0 := by nlinarith
    obtain h_lt_x1 | rfl_x1 | h_gt_x1 := _root_.trichotomous (r := LT.lt) x1 0
    . have hx2_pos : x2 > 0 := by nlinarith
      have hx2_neg : x2 < 0 := by nlinarith
      omega
    . simp [rfl_x1] at hab3
      rcases hab3 with hab3 | hab3
      . omega
      . omega
    . have hx2_pos : x2 > 0 := by nlinarith
      have hx2_neg : x2 < 0 := by nlinarith
      omega
  all_goals aesop

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.neg_dist (x y : Rat) : -(x - y) = (y-x) := by simp

theorem Rat.neg_iff_pos (x: Rat) : x.isPos ↔ (-x).isNeg := by
  constructor <;> intro h
  . use x
  . obtain ⟨r, ⟨hr1, hr2⟩⟩ := h
    simp at hr2
    rw [← hr2] at hr1
    exact hr1

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by
  simp_all
  change (y - x).isNeg ↔ (x - y).isPos
  have h1 := neg_dist x y
  rw [← h1]
  exact (neg_iff_pos (x - y)).symm

theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  simp_all
  constructor <;> intro h
  . have h1 := (le_iff y x).mp h
    rcases h1 with h1 | h1
    . left
      exact h1
    . right
      rw [h1]
  . have h1 : y < x ∨ y = x := by
      rcases h with h | h
      . simp [h]
      . simp [h]
    exact (le_iff y x).mpr h1

theorem Rat.add_left_cancel (x y z : Rat) : z + x = z + y  ↔ x = y := by
  constructor <;> intro h
  . have h1 := congr((-z) + $h)
    simp at h1
    exact h1
  simp [h]

theorem Rat.add_right_cancel (x y z : Rat) : x + z = y + z  ↔ x = y := by
  constructor <;> intro h
  . have h1 := congr((-z) + $h)
    simp at h1
    exact h1
  simp [h]

theorem Rat.x_sub_y_eq_0_iff_x_eq_y (x y : Rat) : x - y = 0 ↔ x = y := by
  constructor <;> intro h
  . have h1 := congr(y + $h)
    simp at h1
    exact h1
  . rw [h]
    simp

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by
    set z := (x - y)
    have hz := trichotomous z
    rcases hz with hz | hz | hz
    . unfold z at hz
      have h1 := (x_sub_y_eq_0_iff_x_eq_y x y).mp hz
      simp [h1]
    . unfold z at hz
      have h1 := (gt_iff x y).mpr hz
      simp [h1]
    . have h1 := (lt_iff x y).mpr hz
      simp [h1]

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y):= by
  rintro ⟨h1, h2⟩
  replace h1 := (gt_iff x y).mp h1
  replace h2 := (lt_iff x y).mp h2
  set z := x - y
  have h3 := not_pos_and_neg z
  aesop

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by
  rintro ⟨h1, h2⟩
  replace h1 := (gt_iff x y).mp h1
  replace h2 := (x_sub_y_eq_0_iff_x_eq_y x y).mpr h2
  set z := x - y
  have h3 := not_zero_and_pos z
  aesop

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by
  rintro ⟨h1, h2⟩
  replace h1 := (lt_iff x y).mp h1
  replace h2 := (x_sub_y_eq_0_iff_x_eq_y x y).mpr h2
  set z := x - y
  have h3 := not_zero_and_neg z
  aesop


/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ y > x := by simp

theorem Rat.add_pos_is_pos {x y: Rat} (hx : x.isPos) (hy : y.isPos) : (x+y).isPos := by
  obtain ⟨a1, a2, ⟨ha1, ha2, ha3⟩⟩ := hx
  obtain ⟨b1, b2, ⟨hb1, hb2, hb3⟩⟩ := hy
  set z := x + y
  set c := a1 * b2 +  a2 * b1
  set d := a2 * b2
  set w : Rat := c / d
  have hz : z = w := by
    unfold z
    rw [ha3]
    rw [hb3]
    change ((a1 // 1)/(a2 // 1) + (b1 // 1) / (b2 // 1)) = (c // 1) / (d//1)
    rw [div_eq, div_eq, inv_eq, inv_eq, mul_eq, mul_eq, add_eq]
    rw [div_eq, inv_eq, mul_eq]
    rw [eq]
    ring
    all_goals aesop
  use c
  use d
  constructor
  . unfold c
    nlinarith
  . constructor
    . nlinarith
    . exact hz


/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by
  obtain ⟨a, ⟨ha1, ha2⟩⟩ := hxy
  obtain ⟨b, ⟨hb1, hb2⟩⟩ := hyz
  use (a + b)
  constructor
  . exact add_pos_is_pos ha1 hb1
  replace ha2 := congr(- $ha2)
  simp at ha2
  replace hb2 := congr(- $hb2)
  simp at hb2
  rw [← ha2, ← hb2]
  simp

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by
  obtain ⟨a, ⟨ha1, ha2⟩⟩ := hxy
  use a
  constructor
  . tauto
  . simp
    exact ha2

theorem Rat.add_lt_add_right_rev {x y:Rat} (z:Rat) (hxy: x + z < y + z) : x < y := by
  obtain ⟨a, ⟨ha1, ha2⟩⟩ := hxy
  use a
  constructor
  . tauto
  . simp_all


theorem Rat.mul_pos_is_pos {x y: Rat} (hx : x.isPos) (hy : y.isPos) : (x*y).isPos := by
  obtain ⟨a1, a2, ⟨ha1, ha2, ha3⟩⟩ := hx
  obtain ⟨b1, b2, ⟨hb1, hb2, hb3⟩⟩ := hy
  set c := a1 * b1
  set d := a2 * b2
  set w : Rat := c / d
  set z := x * y
  have hz : z = w := by
    unfold z
    rw [ha3]
    rw [hb3]
    change (((a1 // 1)/(a2 // 1)) * ((b1 // 1) / (b2 // 1))) = (c // 1) / (d // 1)
    rw [div_eq, div_eq, inv_eq, inv_eq, mul_eq, mul_eq, mul_eq, div_eq, inv_eq, mul_eq]
    rw [eq]
    ring
    all_goals aesop
  use c
  use d
  constructor
  . unfold c
    nlinarith
  . constructor
    . nlinarith
    . exact hz

theorem Rat.add_sub_is_add (x y:Rat) : x + (-y) = x - y := by
  obtain ⟨x1, x2, hx12, rfl ⟩ := eq_diff x
  obtain ⟨y1, y2, hy12, rfl ⟩ := eq_diff y
  rw [neg_eq, add_eq, sub_eq, neg_eq, add_eq]
  all_goals aesop

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  have hyx : y > x := by simpa
  replace hyx := (gt_iff y x).mp hyx
  have hxyz := mul_pos_is_pos hyx hz
  have h1 := add_sub_is_add y x
  rw [← h1] at hxyz
  have hw : (y + (-x)) * z = y * z + (-x) * z := by
    have h1 := right_distrib y (-x) z
    exact h1
  conv at hw =>
    rhs
    simp
  have h2 := add_sub_is_add (y*z) (x*z)
  rw [h2] at hw
  rw [hw] at hxyz
  have hresult := (gt_iff (y * z) (x * z)).mpr hxyz
  simp at hresult
  exact hresult

theorem Rat.simplify_div {b : ℤ} (a: ℤ) (hb : b ≠ 0):  a // b = a / b := by
  change a // b = (a // 1) / (b // 1)
  rw [div_eq, inv_eq, mul_eq, eq]
  simp
  all_goals aesop


theorem Rat.div_cancellation {a : ℤ} (ha : a ≠ 0): (a:Rat)⁻¹ * (a:Rat) = 1 := by
  change (a // 1)⁻¹ * (a // 1) = (1 // 1)
  rw [inv_eq, mul_eq, eq]
  simp_all
  all_goals aesop

-- (a:Rat) / (b:Rat) ≤ c / d ↔ a * d ≤ c * b so big to fail

theorem Rat.div_le_than_iff {b d: ℤ} (a c: ℤ) (hb : b ≠ 0) (hd : d ≠ 0) (hbd : b * d ≥  0): a * d < b * c → (a:Rat) / (b:Rat) < c / d  := by
  have h3 : d * b ≠ 0 := by
    aesop
  have h6 : d * b ≥ 0 := by
    grind
  intro h
  have h1 : a * d ≠  c * b := by
    grind
  have hneg0 : c * b = b * c := by simp [mul_comm]
  have h2 : a * d < c * b := by omega
  use ((c * b - a * d) // (d * b))
  constructor
  . use (c * b - a * d)
    use (d * b)
    constructor
    . omega
    . constructor
      . omega
      . change (c * b - a * d) // (d * b) = ((c * b - a * d) // 1) / ((d * b) // 1)
        rw [div_eq, inv_eq, mul_eq, eq]
        simp_all
        all_goals aesop
  have h3 := simplify_div a hb
  have h4 := simplify_div c hd
  rw [← h3, ← h4]
  rw [sub_eq, neg_eq, add_eq, neg_eq, eq]
  simp_all
  ring
  all_goals aesop

theorem Rat.div_less_than_iff {b d: ℤ} (a c: ℤ) (hb : b ≠ 0) (hd : d ≠ 0) (hbd : b * d ≥  0): a * d ≤ b * c → (a:Rat) / (b:Rat) ≤ c / d  := by
  have h3 : d * b ≠ 0 := by
    aesop
  have h6 : d * b ≥ 0 := by
    grind
  intro h
  . by_cases h1 :  a * d = c * b
    . have ht : (c:Rat) / (d:Rat) - (a:Rat) / (b:Rat) = 0 := by
        change (c // 1) / (d // 1) - (a // 1) / (b // 1) = (0 // 1)
        rw [div_eq, div_eq, inv_eq, inv_eq, mul_eq, mul_eq, sub_eq, neg_eq, add_eq, eq]
        simp_all
        rw [← h1]
        ring
        all_goals aesop
      right;
      exact ((x_sub_y_eq_0_iff_x_eq_y _ _).mp ht).symm
    . left
      push_neg at h1
      have h2 : c * b = b * c := by
        rw [mul_comm]
      rw [h2] at h1
      have h3 : a * d < b * c := by
        omega
      exact div_le_than_iff a c hb hd hbd h3

theorem Rat.not_less_than_equal_iff_less_than(x y:Rat): ¬ ( x ≤ y) ↔ y < x := by
  constructor <;> intro h
  . rw [le_iff] at h
    push_neg at h
    obtain ⟨h3, h4⟩ := h
    have h1 := trichotomous' x y
    rcases h1 with h1 | h1 | h1
    . simp at h1
      exact h1
    . contradiction
    . contradiction
  . rw [le_iff]
    intro h1
    rcases h1 with h1 | h1
    . have h2 := not_gt_and_lt y x
      have h3 : y > x := by aesop
      have h4 := And.intro h3 h
      contradiction
    . have h2 : x > y := by aesop
      have h3 := not_gt_and_eq x y
      have h4 := And.intro h2 h1
      contradiction

theorem Rat.not_less_than_equal_iff_greater(x y:Rat): ¬ ( x ≤ y) ↔ x > y := by
  simp_all
  exact not_less_than_equal_iff_less_than x y

theorem Rat.neg_reflection {b :  ℤ} (a : ℤ) (hb : b ≠ 0) : a // b = (-a) // (-b) := by
  rw [eq]
  simp
  all_goals aesop

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    have hab : ⟦{ numerator := a, denominator := b, nonzero := hb }⟧ = a // b := by
      apply Quotient.sound
      simp_all
    have hcd : ⟦{ numerator := c, denominator := d, nonzero := hd }⟧ = c // d := by
      apply Quotient.sound
      simp_all
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            rw [hab, hcd]
            have h1 := simplify_div a hb
            have h2 := simplify_div c hd
            simp [h1, h2]
            exact div_less_than_iff a c hb hd hbd h
          | isFalse h =>
            apply isFalse
            rw [hab, hcd]
            have h1 := simplify_div a hb
            have h2 := simplify_div c hd
            simp [h1, h2]
            simp at h
            have h3 := (not_less_than_equal_iff_less_than ((a:Rat)/(b:Rat)) ((c:Rat)/(d:Rat))).mpr
            apply h3
            have hdb : 0 ≤ d * b := by
              grind
            have h4 : b * c = c * b := by rw [mul_comm]
            have h5 : a * d = d * a := by rw [mul_comm]
            rw [h4, h5] at h
            exact div_le_than_iff c a hd hb hdb h
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            rw [hab, hcd]
            have h_refl := neg_reflection a hb
            rw [h_refl]
            have hnegb : -b ≠ 0 := by
              simp [hb]
            have h1 := simplify_div (-a) hnegb
            have h2 := simplify_div c hd
            rw [h1, h2]
            have hnegbd : 0 ≤   (-b) * d := by
              grind
            have hneg :  (-a) * d ≤ (-b) * c := by
              grind
            exact div_less_than_iff (-a) c hnegb hd hnegbd hneg
          | isFalse h =>
            apply isFalse
            rw [hab, hcd]
            have h_refl := neg_reflection a hb
            have hnegb : -b ≠ 0 := by
              simp [hb]
            have h1 := simplify_div (-a) hnegb
            have h2 := simplify_div c hd
            rw [h_refl, h1, h2]
            have h3 := (not_less_than_equal_iff_less_than (((-a):Rat)/((-b):Rat)) ((c:Rat)/(d:Rat))).mpr
            apply h3
            have hdbneg : 0 ≤ d * (-b) := by
              grind
            push_neg at h
            have hneg : c * -b < d * -a := by
              grind
            exact div_le_than_iff c (-a) hd hnegb hdbneg hneg

  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := by
    intro a
    right;
    rfl
  le_trans := by
    intro a b c hab hbc
    rcases hab with hab | hab
    . rcases hbc with hbc | hbc
      . have habc := lt_trans hab hbc
        left;
        exact habc
      . rw [hbc] at hab
        left;
        exact hab
    . rw [← hab] at hbc
      exact hbc
  lt_iff_le_not_ge := by
    intro a b
    constructor <;> intro h
    . constructor
      . left;
        exact h
      . have h1 := (not_less_than_equal_iff_less_than b a).mpr
        apply h1
        exact h
    . obtain ⟨h1, h2⟩ := h
      exact (not_less_than_equal_iff_less_than b a).mp h2
  le_antisymm := by
    intro a b hab hba
    rcases hab with hab | hab
    . rcases hba with hba | hba
      . have haba := lt_trans hab hba
        have haea : a = a := by rfl
        have he3 := not_lt_and_eq a a
        have he4 := And.intro haba haea
        contradiction
      . exact hba.symm
    . exact hab
  le_total := by
    intro a b
    have h1 := trichotomous' a b
    rcases h1 with h1 | h1 | h1
    . simp at h1
      right;left;
      exact h1
    . left;left;
      exact h1
    . left;right;
      exact h1
  toDecidableLE := decidableRel

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by
    intro a b hab c
    rcases hab with hab | hab
    . left;
      exact add_lt_add_right c hab
    . right;
      exact (add_right_cancel a b c).mpr hab
  add_le_add_right := by
    intro a b hab c
    have hca : c + a = a + c := by rw [add_comm]
    have hcb : c + b = b + c := by rw [add_comm]
    rw [hca, hcb]
    rcases hab with hab | hab
    . left;
      exact add_lt_add_right c hab
    . right;
      exact (add_right_cancel a b c).mpr hab
  mul_lt_mul_of_pos_left := by
    intro a ha b c hbc
    have h_to_a_pos := (gt_iff a 0).mp
    simp at h_to_a_pos
    have h_a_pos := h_to_a_pos ha
    have h_mul := mul_lt_mul_right hbc h_a_pos
    have hba : b * a = a * b := by rw [mul_comm]
    have hca : c * a = a * c := by rw [mul_comm]
    rw [hba, hca] at h_mul
    exact h_mul
  mul_lt_mul_of_pos_right := by
    intro a ha b c hbc
    have h_to_a_pos := (gt_iff a 0).mp
    simp at h_to_a_pos
    have h_a_pos := h_to_a_pos ha
    have h_mul := mul_lt_mul_right hbc h_a_pos
    exact h_mul
  le_of_add_le_add_left := by
    intro a b c habc
    have hab : a + b = b + a := by rw [add_comm]
    have hac : a + c = c + a := by rw [add_comm]
    rw [hab, hac] at habc
    rcases habc with habc | habc
    . left;
      exact (add_lt_add_right_rev a habc)
    . right;
      exact (add_right_cancel _ _ _).mp habc
    -- add_lt_add_right_rev
  zero_le_one := by
    left;
    use 1
    simp_all
    use 1
    use 1
    simp_all

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) : x * z > y * z := by
  have hzneg: (-(-z)) = z := by
    simp
  rw [← hzneg] at hz
  -- neg_iff_pos
  have h1 := (neg_iff_pos (-z)).mpr hz
  simp_all
  have h2 := mul_lt_mul_right hxy h1
  simp at h2
  exact h2


theorem Rat.quotient {b: ℤ}(a : ℤ) (hB : b ≠ 0): (Quotient.lift (fun ⟨ a, b, h ⟩ ↦ (a:ℚ) / (b:ℚ)) (by
    rintro ⟨a1, a2, ha12⟩ ⟨b1, b2, hb12⟩ hab
    simp_all
    have ha2 : (a2 : ℚ) ≠ 0 := by
      exact_mod_cast ha12
    have hb2 : (b2 : ℚ) ≠ 0 := by
      exact_mod_cast hb12
    apply (div_eq_div_iff ha2 hb2).2
    exact_mod_cast hab
  )) (a // b) = (a:ℚ) / (b:ℚ) := by
    simp_all


/--
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    rintro ⟨a1, a2, ha12⟩ ⟨b1, b2, hb12⟩ hab
    simp_all
    have ha2 : (a2 : ℚ) ≠ 0 := by
      exact_mod_cast ha12
    have hb2 : (b2 : ℚ) ≠ 0 := by
      exact_mod_cast hb12
    apply (div_eq_div_iff ha2 hb2).2
    exact_mod_cast hab
  )
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv n := by
      obtain ⟨ a, b, hb, rfl ⟩ := eq_diff n
      simp_all
      have h1 := simplify_div a hb
      rw [h1]
  right_inv n := by
    have h1 : (fun n: ℚ ↦ (n:Rat)) n = (n.num) // (n.den) := by
      obtain ⟨num, den, den_nz, co_prime⟩ := n
      apply Quotient.sound
      simp_all
    rw [h1]
    simp_all
    exact Rat.num_div_den n


-- obtain ⟨num, den, den_nz, co_prime⟩ := n


/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by sorry




/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := by sorry
  map_mul' := by sorry

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
