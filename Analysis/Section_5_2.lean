import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.closeSeq_def]
  intro n hn1 hn2
  simp_all [Rat.Close]
  lift n to ℕ using hn1
  simp
  by_cases h1: Even n
  . have h_0 : 1 = 1 := by rfl
    simp [h1.neg_one_pow]
    grind
  observe h2: Odd n
  simp [h2.neg_one_pow]
  grind


/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h;
  specialize h 0 1;
  simp [Rat.Close] at h
  norm_num at h


/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h;
  specialize h 0 1;
  simp [Rat.Close] at h
  norm_num at h


/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔ ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
      rw [eventuallyClose_def]
      constructor <;> rintro ⟨N, hN⟩
      . set A := (max N 0).toNat
        use A
        intro n hn
        unfold A at hn
        have hNA : N ≤ n := by grind
        rw [closeSeq_def] at hN
        specialize hN n _ _
        <;> try grind
        . unfold Sequence.from
          simp_all
        . unfold Sequence.from
          simp_all
        . simp [hNA] at hN
          exact hN
      . use N
        rw [closeSeq_def]
        intro n hn1 hn2
        simp_all
        have hn2 : 0 ≤ n := by grind
        simp [hn2]
        lift n to ℕ using hn2
        exact hN n (by exact_mod_cast hn1)


/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
    rw [Rat.closeSeq_def]
    intro h
    simp_all
    have h1 := h 0 (by aesop)
    simp [Rat.Close] at h1
    grind

theorem h_simplify_10_n {n : ℕ} : |(10:ℚ) ^ (-(n: ℤ) - 1) + (10:ℚ) ^ (-(n: ℤ) - 1)| = 2 * ((10:ℚ) ^ (-(n: ℤ))) * ((10:ℚ) ^ (-(1: ℤ))) := by
  calc |(10:ℚ) ^ (-(n: ℤ) - 1) + (10:ℚ) ^ (-(n: ℤ) - 1)| = |2 * (10:ℚ) ^ (-(n: ℤ) - 1)| := by
          congr
          ring
    _ = 2 * |(10:ℚ) ^ (-(n: ℤ) - 1)| := by
      rw [abs_mul]
      norm_num
    _ = 2 * |(10:ℚ) ^ (-(n: ℤ)) * ((10:ℚ) ^ (-(1: ℤ)))| := by
      congr
      apply zpow_add₀
      linarith
    _ = 2 * |(10:ℚ) ^ (-(n: ℤ))| * |((10:ℚ) ^ (-(1: ℤ)))| := by
      rw [abs_mul]
      rw [mul_assoc]
    _ = 2 * (10:ℚ) ^ (-(n: ℤ)) * ((10:ℚ) ^ (-(1: ℤ))) := by
      norm_num

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
    use 2
    rw [Rat.closeSeq_def]
    intro n hn1 hn2
    lift n to ℕ using (by grind)
    simp_all
    simp [Rat.Close]
    rw [h_simplify_10_n]
    have h2 : (0.1: ℚ) = (2: ℚ) * (0.5 : ℚ) * ((10:ℚ) ^ (-(1: ℤ))) := by
      norm_num
    rw [h2]
    gcongr
    have h3 : (10:ℚ) ^ (-(n: ℤ)) ≤ (10:ℚ) ^ (-(2: ℤ)) := by
      gcongr <;> try grind
    have h4 : (10:ℚ) ^ (-(2: ℤ)) ≤ 0.5 := by
      nlinarith
    grind


example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
    use 3
    rw [Rat.closeSeq_def]
    intro n hn1 hn2
    lift n to ℕ using (by grind)
    simp_all
    simp [Rat.Close]
    rw [h_simplify_10_n]
    have h2 : (1e-2: ℚ) = (2: ℚ) * (0.05 : ℚ) * ((10:ℚ) ^ (-(1: ℤ))) := by
      norm_num
    rw [h2]
    gcongr
    have h3 : (10:ℚ) ^ (-(n: ℤ)) ≤ (10:ℚ) ^ (-(2: ℤ)) := by
      gcongr <;> try grind
    have h4 : (10:ℚ) ^ (-(2: ℤ)) ≤ 0.5 := by
      nlinarith
    grind

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  rw [equiv_def]
  constructor <;> intro h ε he;
  . have h1 := h ε he
    rw [Rat.eventuallyClose_def] at h1
    obtain ⟨N, hN⟩ := h1
    set A := (max 0 N).toNat
    use A
    intro n hn
    rw [Rat.closeSeq_def] at hN
    simp at hN
    specialize hN n (by aesop) (by aesop) (by aesop) (by aesop)
    simp_all
    have h1 : N ≤ n := by
      grind
    simp [h1] at hN
    exact hN
  . have ⟨N, hN⟩ := h ε he
    use N
    rw [Rat.closeSeq_def]
    simp_all
    intro n hn
    lift n to ℕ using (by omega)
    have hn0 : 0 ≤ (n:ℤ) := by grind
    simp [hn0]
    simp_all
    exact hN n hn

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn;
    rw [hab n];
    gcongr;
    norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [←Section_4_3.pow_eq_zpow]
        simp [←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1))
        using 1 <;>
        try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN;
  use N;
  intro n hn
  linarith [hab' N n hn]

theorem Sequence.Equiv_Is_Symm {a b: ℕ → ℚ} (hab: Equiv a b)  :
  Equiv b a := by
    simp [equiv_iff] at *
    peel hab with e he
    intro he1
    have ⟨N, hN⟩ := he he1
    simp_all
    use N
    intro n hN1
    have hN2 := hN n hN1
    grind

theorem Sequence.isCauchy_of_equiv_one_side {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy → (b:Sequence).IsCauchy := by
      simp [Sequence.isCauchy_def]
      simp [equiv_def] at hab
      intro h ε he
      have ⟨N, hN⟩ := hab (ε/3) (by aesop)
      have ⟨M, ⟨hM1,hM2⟩⟩ := h (ε/3) (by aesop)
      use (max N M)
      constructor
      . simp_all
      . simp only [Rat.closeSeq_def, Rat.Steady] at *
        simp_all
        intro n hn1 hn2 m hm1 hm2
        have hN2 := hN m (by grind) (by grind)
        replace hN := hN n (by grind) (by grind)
        replace hM2 := hM2 n (by grind) m (by grind)
        have hn3 : 0 ≤ n := by grind
        have hm3 : 0 ≤ m := by grind
        simp [hn3, hm3] at *
        simp [Rat.Close] at *
        lift n to ℕ using (by omega)
        lift m to ℕ using (by omega)
        simp_all
        calc _ = |b n - a n + a n - a m + a m - b m| := by grind
              _ ≤ |b n - a n| + |a n - a m + a m - b m| := by grind
              _ ≤ |b n - a n| + |a n - a m| + |a m - b m| := by grind
              _ ≤ (ε/3) + |a n - a m| + |a m - b m| := by grind
              _ ≤ (ε/3) + (ε/3) + |a m - b m| := by grind
              _ ≤ (ε/3) + (ε/3) + (ε/3) := by grind
              _ ≤ ε := by grind


/-- Exercise 5.2.1 -/
theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
      constructor
      . exact Sequence.isCauchy_of_equiv_one_side hab
      . exact Sequence.isCauchy_of_equiv_one_side (Equiv_Is_Symm hab)


theorem Sequence.EventuallyClose_Is_Symm {ε:ℚ}{a b: ℕ → ℚ} (hab: ε.EventuallyClose a b): ε.EventuallyClose b a := by
    simp [Rat.eventuallyClose_def] at *
    obtain ⟨M, hM⟩ := hab
    use M
    simp [Rat.closeSeq_def] at *
    simp_all
    peel hM with n hA hB hC
    simp [Rat.Close] at *
    grind

theorem Sequence.isBounded_of_eventuallyClose_one_side {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded → (b:Sequence).IsBounded := by
      intro h
      simp only [Rat.eventuallyClose_def, isBounded_def] at *
      obtain ⟨A, hA⟩ := hab
      obtain ⟨B, ⟨hB1, hB2⟩⟩ := h
      set n := (max 0 A).toNat
      let c : Fin n → ℚ := fun m ↦ b m
      have ⟨W, ⟨hW1, hW2⟩⟩ := IsBounded.finite c
      use max W (B + ε)
      constructor
      . simp_all
      simp only [boundedBy_def] at *
      unfold Chapter5.BoundedBy at hW2
      intro m
      have h1 : m < 0 ∨ (0 ≤ m ∧ m < n) ∨ n ≤ m := by grind
      rcases h1 with h1 | h1 | h1
      . simp_all
        have h2 : ¬ 0 ≤ m := by aesop
        simp [h2]
        grind
      . have h_0 : 1 = 1 := by rfl
        lift m to ℕ using h1.1
        have hm : m < n := by
          simp_all
        set E : Fin n := ⟨m, hm⟩
        have hE := hW2 E
        unfold E at hE
        unfold c at hE
        simp_all
      . have h_0 : 1 = 1 := by rfl
        simp only [Rat.closeSeq_def] at hA
        simp_all
        have hB := hA m (by aesop) (by aesop)
        have hC : 0 ≤ m := by aesop
        have hD := hB2 m
        simp [hC] at hD
        simp [hC]
        lift m to ℕ using hC
        simp_all [Rat.Close]
        rw [abs_sub_comm] at hB
        right;
        calc _ = |b m - a m + a m| := by grind
            _  ≤ |b m - a m| + |a m| := by grind
            _  ≤ ε + B := by grind
            _  ≤ B + ε := by grind

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
    constructor
    . exact Sequence.isBounded_of_eventuallyClose_one_side hab
    . exact Sequence.isBounded_of_eventuallyClose_one_side (EventuallyClose_Is_Symm hab)

end Chapter5
