import Mathlib.Tactic
import Analysis.Section_3_3
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro;
    aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  set Ev := nat.specify (fun x ↦ Even (x:ℕ))
  let f : nat → Ev := fun x ↦ by
    let y := nat_equiv (x + x)
    have hy : y.val ∈ Ev := by
      unfold Ev
      rw [specification_axiom'']
      unfold Even
      use y.property
      use x
      unfold y
      simp
    exact ⟨y, hy⟩
  use f
  constructor
  . intro a1 a2 h
    unfold f at h
    simp at h
    rw [Subtype.val_inj] at h
    simp at h
    set x := nat_equiv.symm a1
    set y := nat_equiv.symm a2
    have hxy : x = y := by
      omega
    unfold x at hxy
    unfold y at hxy
    simp at hxy
    exact hxy
  intro n
  have h1 := n.property
  unfold Ev at h1
  rw [specification_axiom''] at h1
  unfold Even at h1
  obtain ⟨h2, ⟨r, hr⟩⟩ := h1
  use r
  unfold f
  simp
  replace hr := congr(nat_equiv $hr.symm)
  simp at hr
  set y := (nat_equiv (r + r))
  have h :  y.val ∈ Ev := by
      unfold Ev
      rw [specification_axiom'']
      unfold Even
      use y.property
      use r
      unfold y
      simp
  rw [← Subtype.val_inj] at hr
  simp at hr
  have h1 : ⟨y, h⟩ = n := by
    rw [← Subtype.val_inj]
    rw [hr]
  exact h1




@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  let f : X → X := fun x ↦ x
  use f
  constructor
  . intro a1 a2 ha
    unfold f at ha
    exact ha
  intro y
  use y

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  obtain ⟨g, hf⟩ := h
  have h1 := hf.surjective
  unfold Function.Surjective at h1
  let f : Y → X := fun y ↦ (h1 y).choose
  use f
  constructor
  . intro a1 a2 ha
    unfold f at ha
    have ha1 := (h1 a1).choose_spec
    have ha2 := (h1 a2).choose_spec
    simp at ha1
    simp at ha2
    rw [ha] at ha1
    rw [ha1] at ha2
    exact ha2
  intro x
  use (g x)
  unfold f
  generalize_proofs pf
  have h2 := pf.choose_spec
  have h3 := hf.injective
  unfold  Function.Injective at h3
  replace h3 := h3 h2
  exact h3

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  let fg : X → Z := fun x ↦ (g (f x))
  use fg
  have h1 := hf.surjective
  have h2 := hg.surjective
  have h3 := hf.injective
  have h4 := hg.injective
  unfold Function.Surjective at *
  unfold Function.Injective at *
  constructor
  . intro a1 a2 ha
    unfold fg at ha
    exact h3 (h4 ha)
  intro z
  obtain ⟨y, hy⟩ := h2 z
  obtain ⟨x, hx⟩ := h1 y
  use x
  unfold fg
  aesop


/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card]
  simp [HasEquiv.Equiv]
  simp [instHasEquivOfSetoid]
  simp [Setoid.r, EqualCard]

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
      set y := (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n))
      have h1 := (has_card_iff y n).mpr
      apply h1
      set f : y.toSubtype → Fin n := fun u ↦ by
        have h2 := u.property
        unfold y at h2
        simp at h2
        set a := nat_equiv ((nat_equiv.symm ⟨u.val, h2.1⟩).pred)
        have h3 := h2.2.2
        have h4 : a.val ∈ Fin n := by
          unfold Fin
          simp
          constructor
          . exact a.property
          unfold a
          simp
          omega
        exact ⟨a, h4⟩
      use f
      constructor
      . intro a1 a2 ha
        unfold f at ha
        simp at ha
        rw [Subtype.val_inj] at ha
        simp at ha
        have h7 := a1.property
        have h8 := a2.property
        unfold y at h7 h8
        simp at h7 h8
        obtain ⟨h9, ⟨h100, h101⟩⟩ := h7
        obtain ⟨h11, ⟨h120, h121⟩⟩ := h8
        have h5 : (⟨↑a1, (Eq.mp (specification_axiom''._simp_1 (fun x ↦ 1 ≤ nat_equiv.symm x ∧ nat_equiv.symm x ≤ n) ↑a1) a1.property).1⟩:nat) = ⟨↑a1, h9⟩ := by
          simp
        have h6 : (⟨↑a2, (Eq.mp (specification_axiom''._simp_1 (fun x ↦ 1 ≤ nat_equiv.symm x ∧ nat_equiv.symm x ≤ n) ↑a2) a2.property).1⟩:nat) = ⟨↑a2, h11⟩ := by
          simp
        rw [h5] at ha
        rw [h6] at ha
        have h13 :  nat_equiv.symm ⟨↑a1, h9⟩  = nat_equiv.symm ⟨↑a2, h11⟩ := by
          omega
        simp at h13
        rw [Subtype.val_inj] at h13
        exact h13
      intro z
      have h1 := z.property
      unfold Fin at h1
      simp at h1
      obtain ⟨h2, h3⟩ := h1
      set x := nat_equiv (nat_equiv.symm ⟨↑z, h2⟩ + 1)
      have h4 : x.val ∈ y := by
        unfold y
        simp
        constructor
        . unfold x
          simp
        . constructor
          . exact x.property
          unfold x
          simp
          exact h3
      use ⟨x, h4⟩
      unfold f
      simp
      unfold x
      simp


/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf
    have h1 := x1.property
    have h2 := x2.property
    simp at h1
    simp at h2
    rw [← Subtype.val_inj]
    rw [h1, h2]
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp
  omega

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  classical

  set fx : ({a, b, c, d} : Set).toSubtype → ℕ :=
    fun x ↦
      if x.val = a then 0
      else if x.val = b then 1
      else if x.val = c then 2
      else 3

  have h1 {x : ({a, b, c, d} : Set).toSubtype} : fx x < 4 := by
    have h2 := x.property
    simp at h2
    unfold fx
    rcases h2 with h2 | h2 | h2 | h2
    . rw [h2]
      simp
    . rw [h2]
      simp
      by_cases h3 : b = a
      . simp [h3]
      . simp [h3]
    . rw [h2]
      simp
      by_cases h4 : c = a
      . simp [h4]
      . simp [h4]
        by_cases h5 : c = b
        . simp [h5]
        . simp [h5]
    . rw [h2]
      simp
      by_cases h6 : d = a
      . simp [h6]
      . simp [h6]
        by_cases h7 : d = b
        . simp [h7]
        . simp [h7]
          by_cases h8 : d = c
          . simp [h8]
          . simp [h8]
  use fun x ↦ Fin_mk _ (fx x) h1
  constructor
  · intro x1 x2 hf
    simp at hf
    unfold fx at hf
    have h1 := x1.property
    simp at h1
    aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0);
    rw [mem_Fin];
    use 0, (by omega);
    rfl
  rw [has_card_iff] at hX
  choose f hf using hX
  obtain ⟨h1, h2⟩ := hf
  have h3 : 0 ∈ Fin n := by
    rw [mem_Fin]
    use 0, (by omega);
    rfl
  have h4 := h2 ⟨0, h3⟩
  obtain ⟨a, hfa⟩ := h4
  have h5 := a.property
  have h6 := nonempty_of_inhabited h5
  contradiction
  -- obtain a contradiction from the fact that `f` is a bijection from the empty set to a
  -- non-empty set.

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  constructor <;> intro h
  . rw [has_card_iff] at h
    obtain ⟨f, hf⟩ := h
    by_contra h1
    push_neg at h1
    obtain ⟨x, hx⟩ := nonempty_def h1
    have y := f ⟨x, hx⟩
    have h2 := y.property
    simp at h2
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by aesop)
  constructor
  . intro a1 a2 hf
    aesop
  intro b
  have h1 := b.property
  simp at h1


/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  rw [has_card_iff] at hX;
  choose f hf using hX
  set X' : Set := X \ {x.val}
  set inj : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by aesop ⟩
  observe hinj : ∀ x:X', (inj x:Object) = x
  have h1 := (mem_Fin _ _).mp (f x).property
  choose m₀ hm₀ hm₀f using h1
  set g : X' → Fin (n-1) := fun x' ↦ by
    have h2:= Fin.toNat_lt (f (inj x'))
    let h3: (f (inj x'):ℕ) ≠ m₀ := by
      by_contra! h4
      simp [←h4, Subtype.val_inj, hf.1.eq_iff] at hm₀f
      simp [inj] at hm₀f
      have h4 := x'.property;
      unfold X' at h4
      simp at h4
      have h5 := h4.2
      push_neg at h5
      rw [← Subtype.val_inj] at hm₀f
      rw [← hm₀f] at h5
      contradiction
    if h' : f (inj x') < m₀ then exact Fin_mk _ (f (inj x')) (by omega)
    else exact Fin_mk _ (f (inj x') - 1) (by omega)
  have hg_def (x':X') : if (f (inj x'):ℕ) < m₀ then (g x':ℕ) = f (inj x') else (g x':ℕ) = f (inj x') - 1 := by
    split_ifs with h' <;>
    simp [g,h']
  have hg : Function.Bijective g := by
    constructor
    have hnem₀ (x : X'.toSubtype): (f (inj x):ℕ) ≠ m₀ := by
      by_contra! h4
      simp [←h4, Subtype.val_inj, hf.1.eq_iff] at hm₀f
      simp [inj] at hm₀f
      have h4 := x.property;
      unfold X' at h4
      simp at h4
      have h5 := h4.2
      push_neg at h5
      rw [← Subtype.val_inj] at hm₀f
      rw [← hm₀f] at h5
      contradiction
    . intro a1 a2 ha12
      unfold g at ha12
      simp only [] at ha12
      split_ifs at ha12 with h1 h2 h3
      . unfold Fin_mk at ha12
        simp at ha12
        rw [Subtype.val_inj] at ha12
        have h4 := hf.1 ha12
        unfold inj at h4
        simp at h4
        rw [Subtype.val_inj] at h4
        exact h4
      . unfold Fin_mk at ha12
        simp at ha12
        have h3 : f (inj a1) < ((f (inj a2)):ℕ) - 1 := by
          push_neg at h2
          have h4 := hnem₀ a2
          have : m₀ ≤  ((f (inj a2)):ℕ) - 1 := by omega
          omega
        rw [ha12] at h3
        simp at h3
      . unfold Fin_mk at ha12
        replace ha12 := ha12.symm
        simp at ha12
        replace ha12 := ha12.symm
        have h5 : f (inj a2) < ((f (inj a1)):ℕ) - 1 := by
          push_neg at h1
          have h4 := hnem₀ a1
          have : m₀ ≤  ((f (inj a1)):ℕ) - 1 := by omega
          omega
        rw [ha12] at h5
        simp at h5
      . unfold Fin_mk at ha12
        simp at ha12
        have h5 : m₀ ≥ 0 := by omega
        have h51 := hnem₀ a1
        have h52 := hnem₀ a2
        push_neg at h1
        push_neg at h3
        have h53 : 1 ≤ (f (inj a1) : ℕ) := by omega
        have h54 : 1 ≤ (f (inj a2) : ℕ) := by omega
        have h6 : ((f (inj a1)):ℕ) = ((f (inj a2)):ℕ) := by omega
        have h7 : (f (inj a1)) = (f (inj a2)) := by
          simp
          exact h6
        have h4 := hf.1 h7
        unfold inj at h4
        simp at h4
        rw [Subtype.val_inj] at h4
        exact h4
    . intro m
      have h2 := hf.2
      have hcase_1 : m.val ∈ Fin n := by
        have h2 := m.property
        rw [mem_Fin] at *
        obtain ⟨x, ⟨h4, h5⟩⟩ := h2
        use x
        constructor
        . omega
        simpa using h5
      have hcase_2 : ↑((m:ℕ) + 1) ∈ Fin n := by
        have h3 := m.property
        rw [mem_Fin] at *
        obtain ⟨x, ⟨h4, h5⟩⟩ := h3
        use (x+1)
        constructor
        . omega
        simpa using h5
      set mm : ℕ := ((m:ℕ) + 1)
      by_cases hcase : m < m₀
      . have ⟨a, hfa⟩ := hf.2 ⟨m, hcase_1⟩
        have h2 : a.val ∈ X':= by
          unfold X'
          simp
          constructor
          . exact a.property
          intro hx
          rw [Subtype.val_inj] at hx
          rw [hx] at hfa
          rw [← Subtype.val_inj] at hfa
          rw [hm₀f] at hfa
          set b := (m:ℕ)
          simp at hfa
          have h3 : b = m.val := by
            unfold b
            simp
          rw [← h3] at hfa
          simp at hfa
          rw [hfa] at hcase
          simp at hcase
        use ⟨a, h2⟩
        unfold g
        simp
        have h4 := hinj ⟨↑a, h2⟩
        rw [Subtype.val_inj] at h4
        have h3 : f (inj ⟨↑a, h2⟩) < m₀ := by
          rw [h4]
          rw [hfa]
          simp
          exact hcase
        conv =>
          lhs
          simp [h3]
        rw [h4]
        rw [hfa]
        simp
      . push_neg at hcase
        have h1 : m₀ < mm := by omega
        set c : Object := ↑mm
        have ⟨a, hfa⟩ := hf.2 ⟨c, hcase_2⟩
        have h2 : a.val ∈ X':= by
          unfold X'
          simp
          constructor
          . exact a.property
          intro hx
          rw [Subtype.val_inj] at hx
          rw [hx] at hfa
          rw [← Subtype.val_inj] at hfa
          rw [hm₀f] at hfa
          simp at hfa
          have h3 : mm = c := by
            unfold c
            simp
          rw [← h3] at hfa
          simp at hfa
          rw [hfa] at hcase
          unfold mm at hcase
          simp at hcase
        use ⟨a, h2⟩
        unfold g
        simp
        have hval : (f a : ℕ) = mm := by
            rw [← Object.natCast_inj, Fin.coe_toNat, hfa];
        have h4 : m₀ < f a := by
          omega
        have heq := hinj ⟨↑a, h2⟩
        rw [Subtype.val_inj] at heq
        have h5 : ¬ f (inj ⟨↑a, h2⟩) < m₀ := by rw [heq]; omega
        conv =>
          lhs
          simp [h5]
        rw [heq, hfa]
        have hcval : (f a : ℕ) - 1 = ↑m := by
          rw [← Object.natCast_inj, Fin.coe_toNat]
          rw [hval]
          unfold mm
          simp
        rw [hfa] at hcval
        exact hcval
  use g

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m;
  induction' n with n hn
  . intro X m h1 h2;
    rw [has_card_zero] at h1;
    contrapose! h1
    apply pos_card_nonempty (by omega) h2;
  intro X m h1 h2
  have h3 : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def h3
  have : m ≠ 0 := by
    contrapose! h3;
    simpa [has_card_zero, h3] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;>
  omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  induction' n with n hn
  . use (nat_equiv.symm 0)
    intro x
    have hx := x.property
    simp at hx
  have h (x : (Fin n).toSubtype): x.val ∈ (Fin (n+1)) := by
    have h1 := x.property
    rw [mem_Fin] at *
    obtain ⟨m, ⟨h2, h3⟩⟩ := h1
    use m
    constructor
    . omega
    exact h3
  let g :  (Fin n).toSubtype → nat.toSubtype := fun x ↦ f ⟨x.val, h x⟩
  have ⟨M, hM⟩ := hn g
  set np := Fin_mk (n+1) n (by omega)
  set N := f np
  have hneg0 (x : (Fin (n + 1)).toSubtype) (h : x < n) : x.val ∈ (Fin n) := by
    rw [mem_Fin] at *
    use x
    constructor
    . exact h
    simp
  have hneg1 (x : (Fin (n + 1)).toSubtype) (h : x < n) : f x = g ⟨x.val, hneg0 x h⟩ := by
    unfold g
    simp
  have hneg2 (x : (Fin (n + 1)).toSubtype) (h : x < n) : (f x:ℕ) ≤ M := by
    have h1 := hneg1 x h
    rw [h1]
    exact hM ⟨x.val, hneg0 x h⟩
  by_cases h1 : M ≤ N
  . use N
    intro x
    by_cases h2 : x = np
    . rw [h2]
    . push_neg at h2
      simp at h2
      have h3 := x.property
      have h4 := Fin.toNat_lt x
      have h5 : ↑x < n  := by omega
      have h6 := hneg2 x h5
      have h7 := le_trans h6 h1
      exact h7
  . use M
    push_neg at h1
    intro x
    by_cases h2 : x = np
    . rw [h2]
      change nat_equiv.symm N ≤ M
      omega
    . push_neg at h2
      simp at h2
      have h3 := x.property
      have h4 := Fin.toNat_lt x
      have h5 : ↑x < n  := by omega
      have h6 := hneg2 x h5
      exact h6

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this;
  choose n hn using this
  simp [has_card] at hn;
  symm at hn;
  simp [HasEquiv.Equiv] at hn
  choose f hf using hn;
  choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1);
  contrapose! hf
  peel hM with a hi;
  contrapose! hi
  apply_fun nat_equiv.symm at hi;
  simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the "junk" cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card]
  simp [hX]
  simp [hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h;
  simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h];
  aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by
    intro h
    unfold card at h
    by_cases h1 : X.finite
    . simp [h1] at h
      have h2 := h1.choose_spec
      rw [← h]
      exact h2
    . simp [h1] at h
      symm at h
      contradiction

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h;
  let e := Equiv.ofBijective f hf
  rw [has_card_iff];
  constructor <;> (intro h'; choose g hg using h')
  . set x := e.symm.trans (.ofBijective g hg)
    use x;
    apply Equiv.bijective
  . set x := e.trans (.ofBijective g hg)
    use x;
    apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;>
  by_cases hY: Y.finite <;>
  try rw [finite] at hX hY
  . choose nX hXn using hX;
    choose nY hYn using hY;
    simp [has_card_to_card hXn] at *
    simp [has_card_to_card hYn] at *
    simp [EquivCard_to_has_card_eq h] at *
    exact card_uniq hXn hYn
  . choose nX hXn using hX;
    rw [EquivCard_to_has_card_eq h] at hXn;
    push_neg at hY
    have h1 := hY nX
    contradiction
  . choose nY hYn using hY;
    rw [←EquivCard_to_has_card_eq h] at hYn;
    push_neg at hX
    have h1 := hX nY
    contradiction
  simp [card]
  conv =>
    lhs
    simp [hX]
  conv =>
    rhs
    simp [hY]




/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  have emptySet {X:Set}: X = ∅ → X.finite := by
    intro h
    unfold finite
    use 0
    exact has_card_zero.mpr h
  constructor <;> intro h
  . constructor
    exact emptySet h
    . unfold card
      have h1 := emptySet h
      simp [h1]
      exact card_uniq (h1.choose_spec) (has_card_zero.mpr h)
  . contrapose h
    push_neg at *
    intro h1
    have h2 := h1
    have h3 := h1.choose_spec
    unfold finite at h2
    obtain ⟨n, nh⟩ := h2
    unfold card
    simp [h1]
    push_neg
    have h4 := card_uniq nh h3
    rw [← h4]
    by_cases h5 : n ≠ 0
    . exact h5
    . push_neg at h5
      rw [h5] at nh
      simp [has_card_zero] at nh
      contradiction


lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl

theorem SetTheory.Set.Fin_mv {n:ℕ}(y : (Fin n).toSubtype) : y.val ∈ Fin (n+1) := by
  have h1 := y.property
  rw [mem_Fin] at *
  obtain ⟨m, mh⟩ := h1
  use m
  constructor
  . omega
  . exact mh.2

theorem SetTheory.Set.Fin_narrow {n:ℕ}(y : (Fin (n+1)).toSubtype) (h : y ≠ n) : y.val ∈ Fin (n) := by
  have h1 := y.property
  rw [mem_Fin] at *
  obtain ⟨m, ⟨mh1, mh2⟩⟩ := h1
  use m
  simp at mh2
  rw [mh2] at h
  constructor
  . omega
  . simp
    exact mh2


theorem SetTheory.Set.card_add {n:ℕ} {X:Set} {x:Object} (hX: X.has_card n) (hY :x ∉ X) :
    (X ∪ {x}).has_card (n+1) := by
      classical
      rw [has_card_iff] at hX;
      choose f hf using hX
      set X' : Set := X ∪ {x}
      set g : X' → Fin (n + 1) := fun x ↦ by
        if h1 : x.val ∈ X then
          set y := f ⟨x.val, h1⟩
          exact ⟨y, Fin_mv y⟩
        else
          exact Fin_mk (n+1) n (by aesop)
      have hf_less_than_n (x:X) : (f x) < n := by
        set y := f x
        have h1 := y.property
        rw [mem_Fin] at h1
        obtain ⟨a, ⟨ha1, ha2⟩⟩ := h1
        simp at ha2
        rw [ha2]
        exact ha1
      have h_belong_to {a : Object} (h1 : a ∈ X') (h2 : a ∉ X) : a = x := by
        unfold X' at h1
        simp at h1
        rcases h1 with h1 | h1
        . contradiction
        . exact h1
      have h_add_x : x ∈ X'  := by
        unfold X'
        simp
      have h_add_xX (a : X) : a.val ∈ X' := by
        unfold X'
        simp
        apply Or.inl a.property
      have hg : Function.Bijective g := by
        constructor
        . intro a1 a2 ha12
          unfold g at ha12
          split_ifs at ha12 with h1 h2 h3
          . simp at ha12
            rw [Subtype.val_inj] at ha12
            have h1 := hf.1 ha12
            simp at h1
            rw [Subtype.val_inj] at h1
            exact h1
          . simp [] at ha12
            change ↑(f ⟨↑a1, h1⟩) = n at ha12
            have h2 := hf_less_than_n (⟨↑a1, h1⟩)
            omega
          . symm at ha12
            simp [] at ha12
            change ↑(f ⟨↑a2, h3⟩) = n at ha12
            have h2 := hf_less_than_n (⟨↑a2, h3⟩)
            omega
          . have h4 := h_belong_to a1.property h1
            have h5 := h_belong_to a2.property h3
            rw [← h5] at h4
            rw [Subtype.val_inj] at h4
            exact h4
        . intro z
          by_cases h : z = n
          . use ⟨x, h_add_x⟩
            unfold g
            simp
            simp [hY]
            symm
            exact h
          . push_neg at h
            have h1 := Fin_narrow z h
            obtain ⟨x, hx⟩ := hf.2 ⟨z, h1⟩
            use ⟨x, h_add_xX x⟩
            unfold g
            simp
            simp [x.property]
            simp at hx
            exact hx
      use g

/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
      have hi := hX
      unfold finite at hX
      obtain ⟨m, mh⟩ := hX
      have h1 := card_add mh hx
      have h2 := h1
      apply has_card_to_card at mh
      apply has_card_to_card at h1
      rw [← mh] at h1
      symm
      constructor
      . exact h1
      . unfold finite
        use (m+1)



theorem SetTheory.Set.card_add_union {X Y:Set} {n:ℕ} (hX: X.finite) (hdisj: Disjoint X Y)  (hA : Y.finite)(hY : Y.card = n) : (X ∪ Y).card = (X.card + n) := by
  by_cases hX_not_zero :  X.card = 0
  . have h2 := empty_iff_card_eq_zero.mpr (And.intro hX hX_not_zero)
    rw [hX_not_zero]
    rw [h2]
    simp
    exact hY
  revert Y
  induction' n with n hn
  . intro Y h1 h2 h3
    simp
    have h4 := empty_iff_card_eq_zero.mpr (And.intro h2 h3)
    rw [h4]
    simp
  . intro Y h1 h2 h3
    have h4 := card_to_has_card (by omega) h3
    have h5 := pos_card_nonempty (by aesop) h4
    obtain ⟨y, hy⟩ := nonempty_def h5
    rw [disjoint_iff] at *
    replace h5 :  Disjoint X (Y\({y}:Set)) := by
      rw [disjoint_iff] at *
      ext x
      simp
      intro h5 h6
      have h7 : x ∈ X ∩ Y := by
        simp
        exact And.intro h5 h6
      rw [h1] at h7
      have h8 := not_mem_empty x
      contradiction
    have h6 := card_erase (by aesop) h4 ⟨y, hy⟩
    change ((Y\({y}:Set))).has_card (n + 1 - 1) at h6
    simp at h6
    set Z := (Y\({y}:Set))
    have h7 : Z.finite := by
      unfold finite
      use n
    have h8 : Z.card = n := by
      unfold card
      simp [h7]
      have h9 := h7.choose_spec
      have h10:= card_uniq h9 h6
      exact h10
    have h9 := hn h5 h7 h8
    unfold Z at h6
    set A := X ∪ Z
    have h10 : y ∉ A ∧ (A ∪ ({y}:Set)) = X ∪ Y := by
      constructor
      . unfold A
        unfold Z
        simp
        by_contra h11
        have h12 : y ∈ X ∩ Y := by
          simp
          exact And.intro h11 hy
        rw [h1] at h12
        have h13 := not_mem_empty y
        contradiction
      . ext x
        unfold A
        unfold Z
        simp
        constructor <;> intro ch
        . rcases ch with ch | ch
          . rcases ch with ch | ch
            . tauto
            . tauto
          rw [ch]
          tauto
        . rcases ch with ch | ch
          . simp [ch]
          . simp [ch]
            by_cases hh : x = y
            . tauto
            . tauto
    have h11 : A.finite := by
      use (X.card + n)
      apply card_to_has_card
      . omega
      exact h9
    have h12 := (card_insert h11 h10.1).2
    rw [h10.2] at h12
    rw [h9] at h12
    exact h12

theorem SetTheory.Set.remove_finite  {Y:Set} {n:ℕ} (X:Set) (h1 : Y.card = n) (h2 : Y.finite) : (Y \ X).finite := by
  revert Y
  induction' n with n hn
  . intro Y h1 h2
    have h3 := empty_iff_card_eq_zero.mpr (And.intro h2 h1)
    rw [h3]
    have h4 : ∅ \ X =  ∅ := by
      ext x
      simp
    rw [h4]
    simp
  . intro Y h1 h2
    have h4 := card_to_has_card (by omega) h1
    have h5 := pos_card_nonempty (by aesop) h4
    obtain ⟨y, hy⟩ := nonempty_def h5
    have h6 := card_erase (by aesop) h4 ⟨y, hy⟩
    change (Y \ {y}).has_card (n) at h6
    set Z := (Y \ {y})
    have h7 : Z.finite := by
      unfold finite
      use n
    have h8 : Z.card = n := by
      unfold card
      simp [h7]
      have h9 := h7.choose_spec
      exact card_uniq h9 h6
    have h9 := hn h8 h7
    have ⟨m, hm⟩ := h9
    by_cases h11 : y ∈ X
    . have h12 : Z \ X = Y \ X := by
        ext x
        unfold Z
        simp
        intro h13 h14
        by_contra h15
        rw [← h15] at h11
        contradiction
      use m
      rw [← h12]
      exact hm
    . use (m+1)
      have h12 : y ∉ Z \ X := by
        unfold Z
        simp
      have h13 := (card_insert h9 h12).2
      have h14 : (Z \ X).card = m := by
        unfold card
        simp [h9]
        have h15 := h9.choose_spec
        exact card_uniq h15 hm
      rw [h14] at h13
      have h15 : (Z \ X ∪ {y}) = Y \ X := by
        ext x
        unfold Z
        simp
        constructor <;> intro h
        . rcases h with h | h
          . exact And.intro h.1.1 h.2
          . rw [h]
            tauto
        . obtain ⟨h1, h2⟩ := h
          by_cases h3 : x = y
          . tauto
          . tauto
      rw [h15] at h13
      apply card_to_has_card
      . omega
      . exact h13

theorem SetTheory.Set.remove_finite_v2  {Y:Set} {n} (X:Set) (h1 : Y.card = n) (h2 : Y.finite) : (Y \ X).card ≤ n := by
  revert Y
  induction' n with n hn
  . intro Y h1 h2
    have h3 := empty_iff_card_eq_zero.mpr (And.intro h2 h1)
    simp [h3]
    have h4 : ∅ \ X =  ∅ := by
      ext x
      simp
    simp [h4]
  . intro Y h1 h2
    have h4 := card_to_has_card (by omega) h1
    have h5 := pos_card_nonempty (by aesop) h4
    obtain ⟨y, hy⟩ := nonempty_def h5
    have h6 := card_erase (by aesop) h4 ⟨y, hy⟩
    change (Y \ {y}).has_card (n) at h6
    apply has_card_to_card at h6
    have h7 := Example_3_6_7a y
    apply has_card_to_card at h7
    have h8 := remove_finite ({y}:Set) h1 h2
    have h9 := hn h6 h8
    by_cases h11 : y ∈ X
    . have h12 : ((Y \ {y}) \ X) = Y \ X := by
        ext x
        simp
        intro h1 h2
        by_contra h3
        rw [h3] at h1
        contradiction
      rw [h12] at h9
      omega
    . have h12 : y ∉ ((Y \ {y}) \ X) := by
        simp
      have ⟨e, he⟩ := h8
      apply has_card_to_card at he
      have h13 := remove_finite X he h8
      have h14 := (card_insert h13 h12).2
      have h15 : (((Y \ {y}) \ X) ∪ {y}) = Y \ X := by
        ext x
        simp
        constructor <;> intro h
        . rcases h with h | h
          . tauto
          . rw [h]
            tauto
        . tauto
      rw [h15] at h14
      omega

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
      have simplify_X_U_Y : X ∪ Y = X ∪ (Y \ X) := by
        ext x
        simp
        constructor <;> intro h
        . rcases h with h | h
          . tauto
          . tauto
        . tauto
      have disjoint_X_U_Y: Disjoint X (Y \ X) := by
        rw [disjoint_iff]
        ext x
        simp
        intro h1 h2
        exact h1
      by_cases hX_not_zero :  X.card = 0
      . have h2 := empty_iff_card_eq_zero.mpr (And.intro hX hX_not_zero)
        rw [hX_not_zero]
        rw [h2]
        simp
        exact hY
      . by_cases hY_not_zero : Y.card = 0
        . have h2 := empty_iff_card_eq_zero.mpr (And.intro hY hY_not_zero)
          rw [hY_not_zero]
          rw [h2]
          simp
          exact hX
        . have ⟨m, hm⟩ := hY
          push_neg at hX_not_zero hY_not_zero
          have h1 := has_card_to_card hm
          have h2 := remove_finite X h1 hY
          have ⟨a, ha⟩ := h2
          replace ha := has_card_to_card ha
          have h3 := card_add_union hX disjoint_X_U_Y h2 ha
          rw [← simplify_X_U_Y] at h3
          rw [h3]
          constructor
          . use (X.card + a)
            apply card_to_has_card
            . omega
            . exact h3
          . have h4 := remove_finite_v2 X h1 hY
            omega



/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
    by_cases hX_not_zero :  X.card = 0
    . have h2 := empty_iff_card_eq_zero.mpr (And.intro hX hX_not_zero)
      rw [hX_not_zero]
      rw [h2]
      simp
    . by_cases hY_not_zero : Y.card = 0
      . have h2 := empty_iff_card_eq_zero.mpr (And.intro hY hY_not_zero)
        rw [hY_not_zero]
        rw [h2]
        simp
      . have ⟨e, he⟩ := hY
        apply has_card_to_card at he
        have h3 := card_add_union hX hdisj hY he
        rw [← he] at h3
        exact h3

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
      obtain ⟨n, ha⟩ := hX
      revert X Y
      induction' n with m hm
      . intro X Y h1 h2
        have h3 := has_card_zero.mp h2
        apply has_card_to_card at h2
        rw [h2]
        rw [h3] at h1
        have h4 : Y = ∅ := by
          ext x
          constructor <;> intro h
          . exact h1 x h
          . have h4 := not_mem_empty x
            contradiction
        rw [h4]
        simp
      . intro X Y h1 h2
        have h5 := pos_card_nonempty (by aesop) h2
        obtain ⟨y, hy⟩ := nonempty_def h5
        have h6 := card_erase (by aesop) h2 ⟨y, hy⟩
        change  (X \ {y}).has_card (m) at h6
        set B := X \ {y}
        set A := Y \ {y}
        have h7 : A ⊆ B := by
          intro x
          unfold A B
          simp
          intro ha1 ha2
          tauto
        have h8 := hm h7 h6
        apply has_card_to_card at h6
        apply has_card_to_card at h2
        rw [h6] at h8
        rw [h2]
        unfold A at h8
        obtain ⟨h9, h10⟩ := h8
        have h11 : y ∉ A := by
          unfold A
          simp
        have h12 := card_insert h9 h11
        by_cases h13 : y ∈ Y
        . have h14 :  (Y \ {y} ∪ {y}) = Y := by
            ext x
            simp
            constructor <;> intro h
            . rcases h with h | h
              . tauto
              . rw [h]
                tauto
            . tauto
          rw [h14] at h12
          constructor
          . tauto
          . omega
        . have h14 :  (Y \ {y}) = Y := by
            ext x
            simp
            intro ha
            by_contra ha1
            rw [← ha1] at h13
            contradiction
          rw [h14] at h9 h10
          constructor
          . tauto
          . omega


/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by
      have ⟨h1,h2⟩ := (card_subset hX hY.1)
      have ⟨a, ha⟩ := hX
      have ⟨b, hb⟩ := h1
      apply has_card_to_card at ha
      apply has_card_to_card at hb
      have h5 := remove_finite Y ha hX
      have ⟨c, hc⟩ := h5
      apply has_card_to_card at hc
      have h3 : X = Y ∪ (X \ Y) := by
        ext x
        simp
        constructor <;> intro h
        . tauto
        . rcases h with h | h
          . exact hY.1 x h
          . tauto
      have h4 : Disjoint Y (X \ Y) := by
        rw [disjoint_iff]
        ext x
        simp
        intro h1 h2
        tauto
      have h6 := card_add_union h1 h4 h5 hc
      rw [← h3] at h6
      by_cases h7 : X.card = Y.card
      . have h8 : c = 0 := by omega
        rw [← hc] at h8
        have h9 := empty_iff_card_eq_zero.mpr (And.intro h5 h8)
        have h10 : X = Y := by
          ext x
          constructor <;> intro h
          . by_contra ha1
            have ha2 : x ∈ X \ Y := by
              simp
              tauto
            rw [h9] at ha2
            have ha3 := not_mem_empty x
            contradiction
          . exact hY.1 x h
        have h11 := hY.2.symm
        contradiction
      . push_neg at h7
        omega


/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
      obtain ⟨n, nh⟩ := hX
      revert X Y
      induction' n with m hm
      . intro X Y f h1
        have h2 := has_card_zero.mp h1
        have h3 : (image f X) = ∅ := by
          ext x
          unfold image
          constructor <;> intro h
          . rw [replacement_axiom] at h
            obtain ⟨a, ⟨ha1, ha2⟩⟩ := h
            simp [h2] at ha2
          . have ha3 := not_mem_empty x
            contradiction
        rw [h3]
        simp
      . intro X Y f ha1
        have h5 := pos_card_nonempty (by aesop) ha1
        obtain ⟨y, hy⟩ := nonempty_def h5
        have h6 := card_erase (by aesop) ha1 ⟨y, hy⟩
        change  (X \ {y}).has_card (m) at h6
        set Z := (X \ {y})
        have h7 : Z ⊆ X := by
          intro x
          unfold Z
          simp
          intro ha1 ha2
          tauto
        set g : Z → Y := fun x ↦ f ⟨x.val, h7 x x.property⟩
        have hneg0 :  X \ Z = {y} := by
          ext x
          unfold Z
          simp
          constructor <;> intro h
          . exact h.2 h.1
          . rw [h]
            simp
            exact hy
        have h8 := hm g h6
        set A :=  (image g Z)
        set C :=  (image f X)
        set B : Set := {(f ⟨y, hy⟩).val}
        have h9 : A ∪ B = C := by
          ext x
          unfold A B C
          simp only [mem_union]
          constructor <;> intro h
          . rcases h with h | h
            . unfold image at *
              rw [replacement_axiom] at *
              obtain ⟨a, ha⟩ := h
              use ⟨a, h7 a a.property⟩
              unfold g at ha
              simp
              constructor
              . exact ha.1
              . exact h7 a a.property
            . unfold image at *
              rw [replacement_axiom] at *
              use ⟨y, hy⟩
              simp
              constructor
              . simp at h
                symm
                exact h
              . exact hy
          . unfold image at *
            rw [replacement_axiom] at *
            obtain ⟨a, ha⟩ := h
            by_cases hb : a.val ∈ Z
            . apply Or.inl
              use ⟨a, hb⟩
              unfold g
              simp
              constructor
              . exact ha.1
              . exact hb
            . apply Or.inr
              simp
              have ha1 : ↑a ∈ X \ Z := by
                simp
                tauto
              rw [hneg0] at ha1
              simp at ha1
              have ha2 : (⟨↑a, ha.2⟩ : X) = (⟨y, hy⟩ : X) := by
                rw [← Subtype.val_inj]
                exact ha1
              rw [← ha2]
              simp
              exact ha.1.symm
        set z := (f ⟨y, hy⟩).val
        have h10 := Example_3_6_7a z
        change B.has_card 1 at h10
        have h11 : B.finite := by
          use 1
        by_cases h12 : z ∈ A
        . have h13 : A ∪ B = A := by
            ext x
            simp
            intro h
            unfold B at h
            simp at h
            unfold z at h12
            rw [← h] at h12
            exact h12
          rw [h9] at h13
          rw [h13]
          constructor
          . exact h8.1
          . apply has_card_to_card at ha1
            apply has_card_to_card at h6
            rw [ha1]
            rw [h6] at h8
            omega
        . have h13 : Disjoint A B := by
            rw [disjoint_iff]
            ext x
            simp
            intro h
            by_contra h14
            unfold B at h14
            simp at h14
            rw [h14] at h
            contradiction
          have h14 := card_union_disjoint h8.1 h11 h13
          have h15 := card_union h8.1 h11
          rw [h9] at h14
          rw [h9] at h15
          rw [h14]
          constructor
          . exact h15.1
          . apply has_card_to_card at h10
            apply has_card_to_card at ha1
            apply has_card_to_card at h6
            rw [h10]
            rw [ha1]
            omega



/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by
      symm
      apply EquivCard_to_card_eq
      set g : X → (image f X) := fun x ↦ ⟨(f x).val, by aesop⟩
      use g
      constructor
      . intro a1 a2 ha12
        unfold g at ha12
        simp at ha12
        rw [Subtype.val_inj] at ha12
        exact hf ha12
      . intro y
        have hy := y.property
        simp at hy
        obtain ⟨a, ⟨ha, ha1⟩⟩ := hy
        use ⟨a, ha⟩
        unfold g
        simp_all

theorem SetTheory.Set.card_prod_fundation {X Y:Set} {w : Object}  (hX: X = {w}) (hY: Y.finite) : (X ×ˢ Y).finite ∧  (X ×ˢ Y).card = Y.card := by
  obtain ⟨n, nh⟩ := hY
  revert X Y
  induction' n with m hm
  . intro X Y h1 h2
    have h3 := has_card_zero.mp h2
    rw [h3]
    have h4 : (X ×ˢ (∅:Set)) = ∅ := by
          ext x
          constructor <;> intro h
          . rw [mem_cartesian] at h
            obtain ⟨a, ⟨b, hb⟩⟩ := h
            have h1 := b.property
            have h2 := not_mem_empty b
            contradiction
          . have h2 := not_mem_empty x
            contradiction
    rw [h4]
    simp
  . intro X Y h1 h2
    have h5 := pos_card_nonempty (by aesop) h2
    obtain ⟨y, hy⟩ := nonempty_def h5
    have h6 := card_erase (by aesop) h2 ⟨y, hy⟩
    change  (Y \ {y}).has_card (m) at h6
    have h7 := hm h1 h6
    set A := (Y \ {y})
    set B : Set := {y}
    have h8 : A ∪ B = Y := by
      unfold A B
      ext x
      simp
      constructor <;> intro h
      . rcases h with h | h
        . tauto
        . rw [h]
          tauto
      . tauto
    have h9 : Disjoint A B := by
      rw [disjoint_iff]
      ext x
      simp
      unfold A B
      simp
    have h10 := prod_union X A B
    rw [h8] at h10
    have h11 : Disjoint (X ×ˢ A) (X ×ˢ B) := by
      rw [disjoint_iff]
      ext x
      constructor <;> intro h
      . rw [mem_inter] at h
        obtain ⟨h1, h2⟩ := h
        rw [mem_cartesian] at h1 h2
        obtain ⟨a, ⟨b, hab⟩⟩ := h1
        obtain ⟨c, ⟨d, hcd⟩⟩ := h2
        rw [hcd] at hab
        simp at hab
        obtain ⟨hab1, hab2⟩ := hab
        have hab3 := d.property
        rw [hab2] at hab3
        have hab4 : b.val ∈ A ∩ B := by
          simp
          have := b.property
          tauto
        rw [disjoint_iff] at h9
        rw [h9] at hab4
        have := not_mem_empty b
        contradiction
      . have := not_mem_empty x
        contradiction
    have hneg0 : w ∈ X := by
      rw [h1]
      simp
    have hneg1 : y ∈ B := by
      unfold B
      simp
    have h12 :  (X ×ˢ B).has_card 1 := by
      set C := (X ×ˢ B)
      set d := mk_cartesian ⟨w, hneg0⟩ ⟨y, hneg1⟩
      have h13 : C = ({d.val}:Set) := by
        unfold C
        ext x
        simp
        constructor <;> intro h
        . obtain ⟨a, ⟨ha, ⟨b, ⟨hb, hab⟩⟩⟩⟩ := h
          rw [h1] at ha
          unfold B at hb
          simp at ha hb
          rw [ha, hb] at hab
          rw [hab]
          aesop
        . use w
          constructor
          . exact hneg0
          . use y
            constructor
            . exact hneg1
            . rw [h]
              aesop
      have h14 := Example_3_6_7a d
      rw [← h13] at h14
      exact h14
    have h13 : (X ×ˢ B).finite := by
      unfold finite
      use 1
    have ⟨h14, h15⟩ := hm h1 h6
    have h16 := card_union_disjoint h14 h13 h11
    apply has_card_to_card at h12
    apply has_card_to_card at h2
    apply has_card_to_card at h6
    rw [h2]
    rw [h12] at h16
    rw [h15] at h16
    rw [h6] at h16
    rw [← h10] at h16
    symm
    constructor
    . exact h16
    . use (m+1)
      apply card_to_has_card
      . omega
      . exact h16





/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
      obtain ⟨n, nh⟩ := hX
      revert X Y
      induction' n with m hm
      . intro X Y h1 h2
        have h3 := has_card_zero.mp h2
        rw [h3]
        simp
        have h4 : ((∅:Set) ×ˢ Y) = ∅ := by
          ext x
          constructor <;> intro h
          . rw [mem_cartesian] at h
            obtain ⟨a, ha⟩ := h
            have h1 := a.property
            have h2 := not_mem_empty a
            contradiction
          . have h2 := not_mem_empty x
            contradiction
        rw [h4]
        simp
      . intro X Y h1 h2
        have h5 := pos_card_nonempty (by aesop) h2
        obtain ⟨y, hy⟩ := nonempty_def h5
        have h6 := card_erase (by aesop) h2 ⟨y, hy⟩
        change  (X \ {y}).has_card (m) at h6
        set A := (X \ {y})
        set B := ({y}:Set)
        have h7 := hm h1 h6
        have h8 : A ∪ B = X := by
          unfold A
          unfold B
          ext x
          simp
          constructor <;> intro h
          . rcases h with h | h
            . tauto
            . rw [h]
              tauto
          . tauto
        have hneg0 : Disjoint A B := by
          unfold A
          unfold B
          rw [disjoint_iff]
          ext x
          simp
        have h9 := union_prod A B Y
        rw [h8] at h9
        have h10 : Disjoint (A ×ˢ Y) (B ×ˢ Y) := by
          rw [disjoint_iff]
          ext x
          constructor <;> intro h
          . rw [mem_inter] at h
            obtain ⟨h1, h2⟩ := h
            rw [mem_cartesian] at *
            obtain ⟨a, ⟨b, hab⟩⟩ := h1
            obtain ⟨c, ⟨d, hcd⟩⟩ := h2
            rw [hab] at hcd
            simp at hcd
            obtain ⟨h3, h4⟩ := hcd
            have ha := a.property
            rw [disjoint_iff] at hneg0
            rw [h3] at ha
            have hc := c.property
            have hac : c.val ∈ A ∩ B := by
              simp
              tauto
            rw [hneg0] at hac
            have h11 := not_mem_empty c
            contradiction
          . have h10 := not_mem_empty x
            contradiction
        have h11 := Example_3_6_7a y
        change B.has_card 1 at h11
        apply has_card_to_card at h2
        apply has_card_to_card at h6
        rw [h6] at h7
        have h13 : B = {y} := by
          rfl
        have h14 := card_prod_fundation h13 h1
        have h15 := card_union_disjoint h7.1 h14.1 h10
        rw [← h9] at h15
        rw [h7.2] at h15
        rw [h14.2] at h15
        have h16 := card_union h7.1 h14.1
        rw [← h9] at h16
        constructor
        . exact h16.1
        . rw [h2]
          rw [h15]
          have h17 : 1 * Y.card = Y.card := by
            omega
          nth_rewrite 2 [← h17]
          ring



noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun := fun x ↦ by
    have h1 := x.property
    rw [powerset_axiom] at h1
    exact h1.choose
  invFun := fun f ↦ by
    have h1 := (powerset_axiom f).mpr (by aesop)
    exact ⟨f, h1⟩
  left_inv := by
    intro x
    simp
    generalize_proofs pf1 pf2
    have h1 := pf1.choose_spec
    rw [← Subtype.val_inj]
    conv =>
      rhs
      rw [← h1]
  right_inv := by
    intro x
    simp



lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

theorem SetTheory.Set.card_pow_one (X:Set) : (X ^ (∅:Set)).finite ∧ (X ^ (∅:Set)).card = 1 := by
  set f : (∅:Set) → X := fun x ↦ False.elim (not_mem_empty _ x.property)
  have h4 : ∃z, z ∈ (X ^ (∅:Set)) := by
    use f
    rw [powerset_axiom]
    use f
  obtain ⟨a, ha⟩ := h4
  have h5 : (X ^ (∅:Set)) = {a} := by
    ext x
    simp
    constructor <;> intro h
    . obtain ⟨fa, hfa⟩ := h
      rw [← hfa]
      simp_all
      obtain ⟨fb, hfb⟩ := ha
      rw [←hfa, ← hfb]
      rw [coe_of_fun, coe_of_fun]
      simp
      ext x
      have h1 := x.property
      have h2 := not_mem_empty x
      contradiction
    . simp_all
  rw [h5]
  have h6 := Example_3_6_7a a
  constructor
  . use 1
  . apply has_card_to_card at h6
    exact h6

theorem SetTheory.Set.card_pow_eliminate {m :ℕ} {X:Set} (h : X.has_card (m + 1)) : ∃y ∈ X, (X \ {y}).has_card m ∧ (X \ {y}) ∪ {y} = X ∧ Disjoint (X \ {y}) {y} := by
    have h5 := pos_card_nonempty (by aesop) h
    obtain ⟨y, hy⟩ := nonempty_def h5
    have h6 := card_erase (by aesop) h ⟨y, hy⟩
    change  (X \ {y}).has_card (m) at h6
    use y
    constructor
    . tauto
    . constructor
      . tauto
      . constructor
        . ext x
          simp
          constructor <;> intro h
          . rcases h with h | h
            . tauto
            . rw [← h] at hy
              exact hy
          . by_cases h1 : x = y
            . tauto
            . tauto
        . rw [disjoint_iff]
          ext x
          simp

theorem SetTheory.Set.card_pow_equal_card (X:Set) (x:Object) : EqualCard (X ^ ({x}:Set)) X :=  by
    unfold EqualCard
    have h1 : x ∈ ({x}:Set) := by simp
    set a : ({x}:Set) := ⟨x, h1⟩
    have h2 (z : (X ^ ({x}:Set)).toSubtype) :   ∃f:({x}:Set) → X.toSubtype, f = z.val := by
      have hz := z.property
      rw [powerset_axiom] at hz
      exact hz
    set f : (X ^ ({x}:Set)).toSubtype → X.toSubtype := fun g ↦ (h2 g).choose a
    use f
    constructor
    . intro a1 a2 ha12
      unfold f at ha12
      rw [← Subtype.val_inj]
      have h3 := (h2 a1).choose_spec
      have h4 := (h2 a2).choose_spec
      rw [←h3, ← h4]
      simp
      ext z
      have hz := z.property
      simp at hz
      have h5 : z = a := by
        unfold a
        rw [← Subtype.val_inj]
        simp
        exact hz
      rw [h5]
      rw [ha12]
    . intro y
      set g : ({x}:Set) → X := fun b ↦ y
      set ag := function_to_object ({x}:Set) X g
      have hag : ag ∈ (X ^ ({x}:Set)) := by
        rw [powerset_axiom]
        use g
        unfold ag
        rfl
      use ⟨ag, hag⟩
      unfold ag
      unfold f
      simp
      generalize_proofs pf1
      have h1 := pf1.choose_spec
      have h2 := (coe_of_fun_inj pf1.choose g).mp h1
      rw [h2]

theorem SetTheory.Set.equal_card_means_equal_cardinality {X Y:Set} (hX: X.finite) : EqualCard X Y → X.card = Y.card := by
  have h0 := hX
  unfold finite at hX
  have ⟨n, hn⟩ := hX
  have h3 : X.card = n := by
    unfold card
    conv =>
      lhs
      simp [h0]
    generalize_proofs
    have h4 := hX.choose_spec
    exact card_uniq h4 hn
  unfold has_card at hn
  intro h
  . have h1 := h.symm.trans hn
    have h2 : Y.has_card n := by
      unfold has_card
      exact h1
    have hY : Y.finite := by
      unfold finite
      use n
    rw [h3]
    symm
    unfold card
    conv =>
      lhs
      simp [hY]
    generalize_proofs pf1
    have hpf1 := pf1.choose_spec
    exact card_uniq hpf1 h2



theorem SetTheory.Set.card_pow_id {X:Set} (hX: X.finite) (x:Object) : (X ^ ({x}:Set)).finite ∧ (X ^ ({x}:Set)).card = X.card := by
  have h1 := equal_card_means_equal_cardinality hX (card_pow_equal_card X x).symm
  symm
  constructor
  . exact h1.symm
  . by_cases h2 : X.card = 0
    . rw [h2] at h1
      replace h1 := h1.symm
      have h3 := empty_iff_card_eq_zero.mpr (And.intro hX h2)
      rw [h3]
      have h4 : ∀f, f∉ ((∅:Set) ^ ({x}:Set))  := by
        intro f
        by_contra hf
        rw [powerset_axiom] at hf
        obtain ⟨g, hg⟩ := hf
        set a := g ⟨x, by simp⟩
        have ha := a.property
        have hb := not_mem_empty a
        contradiction
      have h5 := eq_empty_iff_forall_notMem.mpr h4
      rw [h5]
      simp
    . push_neg at h2
      have h3 := card_to_has_card h2 h1.symm
      use X.card


theorem SetTheory.Set.fun_obj_in {A B:Set} {g : B → A} : (function_to_object B A g) ∈ A ^ B := by
  rw [powerset_axiom]
  use g
  rfl


noncomputable def SetTheory.Set.inj_of_fun {X Y:Set} (f: (Y ^ X).toSubtype) : X → Y := by
  have hf := f.property
  rw [powerset_axiom] at hf
  exact hf.choose

theorem SetTheory.Set.card_pow_existance {A B C : Set}
    (a : (A ^ (B ∪ C)).toSubtype) :
    ∃ b : ((A ^ B) ×ˢ (A ^ C)).toSubtype,
      (∀ (x : Object) (hx : x ∈ B),
        inj_of_fun (fst b) ⟨x, hx⟩ =
          inj_of_fun a ⟨x, by
            rw [mem_union]
            exact Or.inl hx⟩)
            ∧
      (∀ (x : Object) (hx : x ∈ C),
        inj_of_fun (snd b) ⟨x, hx⟩ =
          inj_of_fun a ⟨x, by
            rw [mem_union]
            exact Or.inr hx⟩)
            := by
    set l_inj : B → (B ∪ C).toSubtype := fun z ↦ ⟨z, by aesop⟩
    set r_inj : C → (B ∪ C).toSubtype := fun z ↦ ⟨z, by aesop⟩
    set a_fun := inj_of_fun a
    set l1 : B → A := fun z ↦ a_fun (l_inj z)
    set l2 : C → A := fun z ↦ a_fun (r_inj z)
    set r1 := function_to_object B A l1
    set r2 := function_to_object C A l2
    set a1 : (A^B).toSubtype := ⟨r1, fun_obj_in⟩
    set a2 : (A^C).toSubtype := ⟨r2, fun_obj_in⟩
    set lr := mk_cartesian a1 a2
    use lr
    have h1 := fst_of_mk_cartesian a1 a2
    have h2 := snd_of_mk_cartesian a1 a2
    constructor <;> intro x hx
    . unfold lr
      rw [h1]
      unfold a_fun
      unfold a1
      unfold r1
      unfold l1
      unfold inj_of_fun
      unfold a_fun
      unfold l_inj
      unfold inj_of_fun
      simp
      generalize_proofs pf1 pf2 pf3 pf4
      have hpf1 := pf1.choose_spec
      have hpf3 := pf3.choose_spec
      replace hpf3 := (coe_of_fun_inj _ _).mp hpf3
      set z : B := ⟨x, hx⟩
      have h2 := congr($hpf3 z)
      simp at h2
      unfold z at h2
      exact h2
    . unfold lr
      rw [h2]
      unfold a_fun
      unfold a2
      unfold r2
      unfold l2
      unfold inj_of_fun
      unfold a_fun
      unfold r_inj
      unfold inj_of_fun
      simp
      generalize_proofs pf1 pf2 pf3 pf4
      have hpf1 := pf1.choose_spec
      have hpf3 := pf3.choose_spec
      replace hpf3 := (coe_of_fun_inj _ _).mp hpf3
      set z : C := ⟨x, hx⟩
      have h2 := congr($hpf3 z)
      simp at h2
      unfold z at h2
      exact h2

theorem SetTheory.Set.cart_eq {A B:Set} {x y: A ×ˢB} :  x = y ↔ (fst x) = (fst y) ∧ (snd x) = (snd y) := by
  constructor <;> intro h
  . rw [h]
    simp
  . have h1 : mk_cartesian (fst x) (snd x) = x := by
      rw [cartesian_eq]
      tauto
    have h2 : mk_cartesian (fst y) (snd y) = y := by
      rw [cartesian_eq]
      tauto
    rw [← h1, ← h2, h.1, h.2]



theorem SetTheory.Set.card_pow_union_eq {B C:Set} (A:Set) (hDisjoint: Disjoint B C): EqualCard (A ^ (B ∪ C)) ((A ^ B) ×ˢ (A ^ C)) := by
  set f : (A ^ (B ∪ C)).toSubtype →  ((A ^ B) ×ˢ (A ^ C)).toSubtype := fun x ↦ (card_pow_existance x).choose
  use f
  constructor
  . intro a1 a2 ha12
    simp at f
    unfold f at ha12
    have hb1 := (card_pow_existance a1).choose_spec
    have hb2 := (card_pow_existance a2).choose_spec
    set b1 := (card_pow_existance a1).choose
    set b2 := (card_pow_existance a2).choose
    have ha1 := a1.property
    have ha2 := a2.property
    rw [powerset_axiom] at ha1 ha2
    obtain ⟨f1, hf1⟩ := ha1
    obtain ⟨f2, hf2⟩ := ha2
    rw [← Subtype.val_inj]
    rw [←hf1, ←hf2]
    have hef1 : inj_of_fun a1 = f1  := by
      ext x
      unfold inj_of_fun
      generalize_proofs pf1
      have hpf1 := pf1.choose_spec
      rw [← hpf1] at hf1
      rw [coe_of_fun_inj] at hf1
      have answer := congr($hf1 x)
      rw [answer]
    have hef2 : inj_of_fun a2 = f2 := by
      ext x
      unfold inj_of_fun
      generalize_proofs pf1
      have hpf1 := pf1.choose_spec
      rw [← hpf1] at hf2
      rw [coe_of_fun_inj] at hf2
      have answer := congr($hf2 x)
      rw [answer]
    rw [hef1] at hb1
    rw [hef2] at hb2
    simp
    ext x
    simp_all
    have hx := x.property
    simp at hx
    rcases hx with hx | hx
    . have h1 := hb1.1 x hx
      simp at h1
      rw [h1]
    . have h1 := hb1.2 x hx
      simp at h1
      rw [h1]
  . intro abac
    set abac1 := inj_of_fun (fst abac)
    set abac2 := inj_of_fun (snd abac)
    set g : (B ∪ C).toSubtype → A.toSubtype := fun bc ↦ by
      if bc.val ∈ B then
        exact abac1 ⟨bc, by aesop⟩
      else
        exact abac2 ⟨bc, by aesop⟩
    set gobj := (function_to_object (B ∪ C) A g)
    set m :  (A^(B ∪ C)).toSubtype := ⟨gobj, fun_obj_in⟩
    use m
    apply cart_eq.mpr
    constructor
    . unfold f
      generalize_proofs pf1 pf2 pf3
      have ⟨hpf31, hpf32⟩ := pf3.choose_spec
      have h2 := m.property
      rw [powerset_axiom] at h2
      obtain ⟨fm, hfm⟩ := h2
      have h3 : function_to_object _ _ g = fm := by
        rw [hfm]
      replace h3 := (coe_of_fun_inj _ _).mp h3
      have h4 : (inj_of_fun m) = fm := by
        ext x
        unfold inj_of_fun
        generalize_proofs pf4
        have hpf4 := pf4.choose_spec
        conv at hpf4 =>
          rhs
          rw [← hfm]
        replace hpf4 := (coe_of_fun_inj _ _).mp hpf4
        rw [hpf4]
      rw [← h3] at h4
      have h5 := (fst pf3.choose).property
      have h6 := (fst abac).property
      rw [powerset_axiom] at h5 h6
      obtain ⟨f5, hf5⟩ := h5
      obtain ⟨f6, hf6⟩ := h6
      rw [← Subtype.val_inj]
      rw [← hf5,← hf6]
      simp
      ext x
      replace hpf31 := hpf31 x x.property
      conv at hpf31 =>
        rhs
        rw [h4]
        unfold g
        simp [x.property]
        unfold abac1
      simp at hpf31
      set fa1 := (fst pf3.choose)
      set fa2 := (fst abac)
      have hfa1 : inj_of_fun fa1 = f5 := by
        ext z
        unfold inj_of_fun
        generalize_proofs pfa1
        have hpfa1 := pfa1.choose_spec
        conv at hpfa1 =>
          rhs
          rw [← hf5]
        rw [coe_of_fun_inj] at hpfa1
        rw [hpfa1]
      have hfa2 : inj_of_fun fa2 = f6 := by
        ext z
        unfold inj_of_fun
        generalize_proofs pfa1
        have hpfa1 := pfa1.choose_spec
        conv at hpfa1 =>
          rhs
          rw [← hf6]
        rw [coe_of_fun_inj] at hpfa1
        rw [hpfa1]
      rw [hfa1, hfa2] at hpf31
      rw [hpf31]
    . unfold f
      generalize_proofs pf1 pf2 pf3
      have ⟨hpf31, hpf32⟩ := pf3.choose_spec
      have h2 := m.property
      rw [powerset_axiom] at h2
      obtain ⟨fm, hfm⟩ := h2
      have h3 : function_to_object _ _ g = fm := by
        rw [hfm]
      replace h3 := (coe_of_fun_inj _ _).mp h3
      have h4 : (inj_of_fun m) = fm := by
        ext x
        unfold inj_of_fun
        generalize_proofs pf4
        have hpf4 := pf4.choose_spec
        conv at hpf4 =>
          rhs
          rw [← hfm]
        replace hpf4 := (coe_of_fun_inj _ _).mp hpf4
        rw [hpf4]
      rw [← h3] at h4
      have h5 := (snd pf3.choose).property
      have h6 := (snd abac).property
      rw [powerset_axiom] at h5 h6
      obtain ⟨f5, hf5⟩ := h5
      obtain ⟨f6, hf6⟩ := h6
      rw [← Subtype.val_inj]
      rw [← hf5,← hf6]
      simp
      ext x
      replace hpf32 := hpf32 x x.property
      have h5 : x.val ∉ B := by
        intro h6
        rw [disjoint_iff] at hDisjoint
        have h7 : x.val ∈ B ∩ C := by
          simp
          constructor
          . exact h6
          . exact x.property
        rw [hDisjoint] at h7
        have h8 := not_mem_empty x
        contradiction
      conv at hpf32 =>
        rhs
        rw [h4]
        unfold g
        simp [h5]
        unfold abac2
      simp at hpf32
      set fa1 := (snd pf3.choose)
      set fa2 := (snd abac)
      have hfa1 : inj_of_fun fa1 = f5 := by
        ext z
        unfold inj_of_fun
        generalize_proofs pfa1
        have hpfa1 := pfa1.choose_spec
        conv at hpfa1 =>
          rhs
          rw [← hf5]
        rw [coe_of_fun_inj] at hpfa1
        rw [hpfa1]
      have hfa2 : inj_of_fun fa2 = f6 := by
        ext z
        unfold inj_of_fun
        generalize_proofs pfa1
        have hpfa1 := pfa1.choose_spec
        conv at hpfa1 =>
          rhs
          rw [← hf6]
        rw [coe_of_fun_inj] at hpfa1
        rw [hpfa1]
      rw [hfa1, hfa2] at hpf32
      rw [hpf32]

-- theorem SetTheory.Set.card_pow_finite {A B: Set} (hA : A.finite) (hB : B.finite) : ((A ^ B).finite) := by
--   obtain ⟨n, nh⟩ := hB
--   revert A B
--   induction' n with m hm
--   . intro A B h1 h2
--     have h3 := has_card_zero.mp h2
--     rw [h3]
--     exact (card_pow_one A).1
--   . intro A B h1 h2
--     have h3 := card_pow_eliminate h2
--     obtain ⟨y, ⟨hy1, ⟨hy2, ⟨hy3, hy4⟩⟩⟩⟩ := h3
--     have hm1 := hm h1 hy2
--     have h2 := (card_pow_id h1 y).1
--     have h3 := (card_prod hm1 h2).1
--     have h31 := (card_prod hm1 h2).2
--     have h4 := (card_pow_union_eq A hy4).symm
--     have h1 := (equal_card_means_equal_cardinality h3 h4).symm
--     simp [hy3] at h1
--     by_cases not_zero : ((A ^ (B \ {y})) ×ˢ (A ^ ({y}:Set))).card = 0
--     . rw [h31] at not_zero
--       have h1 :  (A ^ (B \ {y})).card = 0 ∨ (A ^ ({y}:Set)).card = 0 := by
--         exact Nat.mul_eq_zero.mp not_zero
--       rcases h1 with h1 | h1
--       .




theorem SetTheory.Set.card_zero_pow {X:Set} (hX1 : X.card ≠ 0): ((∅:Set) ^ X).finite ∧ ((∅:Set) ^ X).card = 0 := by
  have h0: X ≠ ∅ := by
    intro h1
    have h2 := card_eq_zero_of_empty h1
    contradiction
  have ⟨y, hy⟩ := nonempty_def h0
  have h1: ∀f, f ∉ ((∅:Set) ^ X) := by
    intro f
    by_contra h1
    rw [powerset_axiom] at h1
    obtain ⟨g, hg⟩ := h1
    set z := g ⟨y, hy⟩
    have hz := z.property
    have hz1 := not_mem_empty z
    contradiction
  have h2 := eq_empty_iff_forall_notMem.mpr h1
  rw [h2]
  simp


/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
      obtain ⟨n, nh⟩ := hX
      revert X Y
      induction' n with m hm
      . intro X Y h1 h2
        have h3 := has_card_zero.mp h2
        rw [h3]
        simp
        exact (card_pow_one Y)
      . intro X Y h1 h2
        have h3 := card_pow_eliminate h2
        obtain ⟨y, ⟨hy1, ⟨hy2, ⟨hy3, hy4⟩⟩⟩⟩ := h3
        have hm1 := hm h1 hy2
        have hx2 := (card_pow_id h1 y)
        have h3 := (card_prod hm1.1 hx2.1)
        have h4 := (card_pow_union_eq Y hy4).symm
        have hxx1 := (equal_card_means_equal_cardinality h3.1 h4).symm
        simp [hy3] at hxx1
        have h_x_y_finite : (X \ {y}).finite := by
            unfold finite
            use m
        have h_x_y_card_m : (X \ {y}).card = m := by
            unfold card
            simp [h_x_y_finite]
            generalize_proofs pf1
            have hpf1 := pf1.choose_spec
            exact card_uniq hpf1 hy2
        have h_x_finite : X.finite := by
            unfold finite
            use (m+1)
        have h_x_card_m_1 : X.card = (m+1) := by
            unfold card
            simp [h_x_finite]
            generalize_proofs pf1
            have hpf1 := pf1.choose_spec
            exact card_uniq hpf1 h2
        have h_y_id := (card_pow_id h1 y).2
        by_cases not_zero : ((Y ^ (X \ {y})) ×ˢ (Y ^ ({y}:Set))).card = 0
        . have h_init : Y = ∅ := by
            rw [h3.2] at not_zero
            have hx1 := Nat.mul_eq_zero.mp not_zero
            rcases hx1 with hx1 | hx1
            . by_cases h2 : ((X \ {y})) = ∅
              . rw [h2] at hx1
                have h3 := (card_pow_one Y).2
                omega
              . rw [hm1.2] at hx1
                push_neg at h2
                have h : (X \ {y}) ≠ ∅ → ¬ (X \ {y}).has_card 0 := by
                  intro hX
                  contrapose! hX
                  exact has_card_zero.mp hX
                have h5 := h h2
                have h6 : (X \ {y}).card ≠ 0 := by
                  unfold card
                  simp [h_x_y_finite]
                  generalize_proofs pf1
                  have hpf1 := pf1.choose_spec
                  intro h1
                  rw [h1] at hpf1
                  contradiction
                have h7 : Y.card = 0 := eq_zero_of_pow_eq_zero hx1
                exact empty_iff_card_eq_zero.mpr (And.intro h1 h7)
            . rw [h_y_id] at hx1
              exact empty_iff_card_eq_zero.mpr (And.intro h1 hx1)
          simp [h_init]
          have h6 : X.card ≠ 0 := by
            omega
          have h7 := card_zero_pow h6
          constructor
          . exact h7.1
          . have h8 : 0 ^ X.card = 0 := by
              exact zero_pow h6
            rw [h8]
            exact h7.2
        . push_neg at not_zero
          set A := ((Y ^ (X \ {y})) ×ˢ (Y ^ ({y}:Set)))
          have h5 : A.card = A.card := by rfl
          have h6 := card_to_has_card not_zero h5
          have h7 : A.finite := by
            unfold finite
            use A.card
          have h8 := (equal_card_means_equal_cardinality h7 h4).symm
          simp [hy3] at h8
          have h9 :  (Y ^ X).card ≠ 0 := by
            rw [← h8] at not_zero
            exact not_zero
          rw [h3.2] at h8
          rw [hm1.2] at h8
          rw [h_x_y_card_m] at h8
          rw [h_y_id] at h8
          change ((Y ^ X).card = Y.card ^ (m + 1)) at h8
          rw [← h_x_card_m_1] at h8
          constructor
          . unfold finite
            use (Y ^ X).card
            exact card_to_has_card h9 (by rfl)
          . exact h8


/-- Exercise 3.6.5. You might find {name}`SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by
      unfold EqualCard
      set f : (A ×ˢ B) → (B ×ˢ A) := fun x ↦ mk_cartesian (snd x) (fst x)
      use f
      constructor
      . intro a1 a2 ha12
        unfold f at ha12
        unfold mk_cartesian at ha12
        simp at ha12
        ext
        have ha1 := pair_eq_fst_snd a1
        have ha2 := pair_eq_fst_snd a2
        rw [ha12.1, ha12.2] at ha1
        rw [← ha2] at ha1
        exact ha1
      . intro y
        use (mk_cartesian (snd y) (fst y))
        unfold f
        simp


noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

/-- Exercise 3.6.6. You may find {name}`SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
      unfold EqualCard
      have h1 := pow_fun_equiv' A B
      have h2 := pow_fun_equiv' (A ^ B) C
      have h3 :  ((A ^ B) ^ C).toSubtype ≃ (C.toSubtype → (B.toSubtype → A.toSubtype)) := by
         exact h2.trans ((Equiv.refl C.toSubtype).arrowCongr h1)
      have h4 := pow_fun_equiv'  A (B ×ˢ C)
      set f : ((A ^ B) ^ C :Set) → (A ^ (B ×ˢ C) : Set) := fun x ↦ h4.symm (SetTheory.Set.curry_equiv (fun b c ↦ h3 x c b))
      use f
      constructor
      . intro a1 a2 ha12
        unfold f at ha12
        simp at ha12
        have ha1 := a1.property
        have ha2 := a2.property
        simp at ha1
        simp at ha2
        apply h3.injective
        ext c b
        set a := mk_cartesian b c
        have ha34 := congr($ha12 a)
        simp at ha34
        rw [ha34]
      . intro y
        have h5 := h4.symm.surjective y
        obtain ⟨a, ha⟩ := h5
        have h6 := curry_equiv.surjective a
        obtain ⟨b, hb⟩ := h6
















theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by sorry

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by sorry

theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by sorry

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := sorry

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by sorry

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by  sorry

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by sorry

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by sorry

/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by sorry

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
    Function.Bijective (Permutations_toFun p) := by sorry

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by sorry

/-- This connects our concept of a permutation with Mathlib's {name}`Equiv` between {lean}`Fin n` and {lean}`Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
}

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any {lean}`Fin n` can be cast to {lean}`Fin (n + 1)`. Compare to Mathlib {name}`Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by sorry

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by sorry

/-- Any {lean}`Fin (n + 1)` except {lean}`n` can be cast to {lean}`Fin n`. Compare to Mathlib {name}`Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by sorry

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by sorry

/-- Any natural {lean}`n` can be cast to {lean}`Fin (n + 1)`. Compare to Mathlib {name}`Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by sorry

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some {lean}`x : Fin (n+1)` is never equal to {name}`i`, we can shrink it into {lean}`Fin n` by shifting all {lean}`(x : ℕ) > i` down by one.
  Compare to Mathlib {name}`Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by sorry)
  else
    Fin_mk _ ((x:ℕ) - 1) (by sorry)

/--
  We can expand {lean}`x : Fin n` into {lean}`Fin (n + 1)` by shifting all {lean}`(x : ℕ) ≥ i` up by one.
  The output is never {name}`i`, so it forms an inverse to the shrinking done by {name}`predAbove`.
  Compare to Mathlib {name}`Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by sorry) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by sorry)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by sorry

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by sorry

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by sorry

/-- Exercise 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    -- Hint: you might find `perm_equiv_equiv`, `Fin.succAbove`, and `Fin.predAbove` useful.
    have equiv : S i ≃ Permutations n := sorry
    use equiv, equiv.injective, equiv.surjective

  -- Hint: you might find `card_iUnion_card_disjoint` and `Permutations_finite` useful.
  sorry

/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by sorry

/-- Connections with Mathlib's {name}`Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Connections with Mathlib's {name}`Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Connections with Mathlib's {name}`Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's {name}`Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3

-- theorem SetTheory.Set.card_add_union {X Y:Set} (hX: X.finite) (hdisj: Disjoint X Y) {n:ℕ} (hY : Y.has_card n) : (X ∪ Y).has_card (X.card + n) := by
--   revert Y
--   induction' n with n hn
--   . intro Y h1 h2
--     simp
--     rw [has_card_zero] at h2
--     rw [h2]
--     simp
--     by_cases h : X.card = 0
--     . rw [h]
--       have h3 := empty_iff_card_eq_zero.mpr (And.intro hX h)
--       exact has_card_zero.mpr h3
--     . apply card_to_has_card
--       push_neg at h
--       exact h
--       . rfl
--   . intro Y h1 h2
--     have h3 := pos_card_nonempty (by aesop) h2
--     obtain ⟨y, hy⟩ := nonempty_def h3
--     have h4 :  Disjoint X (Y\({y}:Set)) := by
--       rw [disjoint_iff] at *
--       ext x
--       simp
--       intro h5 h6
--       have h7 : x ∈ X ∩ Y := by
--         simp
--         exact And.intro h5 h6
--       rw [h1] at h7
--       have h8 := not_mem_empty x
--       contradiction
--     have h5 := card_erase (by aesop) h2 ⟨y, hy⟩
--     change ((Y\({y}:Set))).has_card (n + 1 - 1) at h5
--     set Z := (Y\({y}:Set))
--     have h6 := hn h4 h5
--     unfold Z at h6
--     have h7 := card_add h6 ⟨y, by aesop⟩
