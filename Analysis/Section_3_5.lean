import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 3.5: Cartesian products

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples.
- Cartesian products and n-fold products.
- Finite choice.
- Connections with Mathlib counterparts such as {name}`Set.pi` and {name}`Set.prod`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Definition 3.5.1 (Ordered pair).  One could also have used {lean}`Object × Object` to
define {name}`OrderedPair` here. -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Helper lemma for Exercise 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
    a = c ∧ b = c := by
  have h1 : c ∈ ({c}: Set) := by simp_all
  have h2 : a ∈ ({a, b}: Set) := by simp_all
  have h3 : b ∈ ({a, b}: Set) := by simp_all
  constructor
  . intro h
    rw [h] at h2 h3
    simp_all
  intro ⟨h1, h2⟩
  rw [h1, h2]
  simp_all

lemma SetTheory.Set.singleton_eq_iff (a b : Object) : {a} = ({b}:Set) ↔
  a = b := by
    have h1 : a ∈ ({a}:Set) := by simp
    constructor
    . intro h2
      rw [h2, mem_singleton] at h1
      exact h1
    intro h2
    rw [h2]


lemma SetTheory.Set.pair_eq_singleton (a : Object) : {a, a} = ({a}:Set) := by simp

lemma SetTheory.Set.pair_comm_eq (a b: Object) : {a, b} = ({b, a}:Set) := by
  ext x;
  refine ⟨by aesop, by aesop ⟩;

lemma SetTheory.Set.pair_eq_pair_iff {a b c d: Object}: ({a, b} :Set) = ({c, d}: Set) ↔
    (a = c ∧  b = d) ∨  (b = c ∧ a = d) := by
      have h1: a ∈ ({a, b} :Set) := by simp
      have h2: b ∈ ({a, b} :Set) := by simp
      constructor
      . intro h3
        rw [h3] at h1 h2
        rw [mem_pair] at *
        rcases h1 with h1 | h1
        . rcases h2 with h2 | h2
          . rw [h1, h2] at h3
            replace h3 := by simpa only [pair_eq_singleton, pair_eq_singleton_iff] using h3.symm
            obtain ⟨h4, h5⟩ := h3
            grind
          grind
        . rcases h2 with h2 | h2
          . grind
          rw [h1, h2] at h3
          replace h3 := by simpa only [pair_eq_singleton, pair_eq_singleton_iff] using h3.symm
          obtain ⟨h4, h5⟩ := h3
          grind
      intro h3
      rcases h3 with h3 | h3
      . obtain ⟨h4, h5⟩ := h3
        grind
      obtain ⟨h4, h5⟩ := h3
      rw [h4, h5]
      exact pair_comm_eq d c

lemma simplify_or_1 {a b c : Object} : {a} = ({b}:Set) ∨ {a} =  ({b, c}:Set) → a = b ∨ (b = a ∧  c = a) := by
  intro h1
  rcases h1 with h1 | h1
  . rw [singleton_eq_iff] at h1
    exact Or.inl h1
  replace h1 := pair_eq_singleton_iff.mp h1.symm
  exact Or.inr h1

lemma simplify_or_2 {a b c d: Object} : {a, b} =  ({c}:Set) ∨ {a, b} =  ({c, d}:Set) → (a = c ∧ b = c) ∨ ((a = c ∧ b = d) ∨ (b = c ∧ a = d)) := by
  intro h1
  rcases h1 with h1 | h1
  . rw [pair_eq_singleton_iff] at h1
    exact Or.inl h1
  rw [pair_eq_pair_iff] at h1
  exact Or.inr h1


/-- Exercise 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst}:Set):Object), (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    intro a b h
    apply (OrderedPair.eq a.fst a.snd b.fst b.snd).mpr
    simp at h
    have h1 : SetTheory.set_to_object {a.fst} ∈ ({SetTheory.set_to_object {a.fst}, SetTheory.set_to_object {a.fst, a.snd}}:Set) := by simp
    have h2 : SetTheory.set_to_object {a.fst, a.snd} ∈ ({SetTheory.set_to_object {a.fst}, SetTheory.set_to_object {a.fst, a.snd}}:Set) := by simp
    have h3 : SetTheory.set_to_object {b.fst} ∈ ({SetTheory.set_to_object {b.fst}, SetTheory.set_to_object {b.fst, b.snd}}:Set) := by simp
    have h4 : SetTheory.set_to_object {b.fst, b.snd} ∈ ({SetTheory.set_to_object {b.fst}, SetTheory.set_to_object {b.fst, b.snd}}:Set) := by simp
    rw [h] at h1 h2
    rw [← h] at h3 h4
    rw [mem_pair] at h1 h2 h3 h4
    replace h1 :  {a.fst} = ({b.fst}:Set) ∨ {a.fst} =  ({b.fst, b.snd}:Set) := by simpa using h1
    replace h2 :  {a.fst, a.snd} =  ({b.fst}:Set) ∨ {a.fst, a.snd} =  ({b.fst, b.snd}:Set) := by simpa using h2
    replace h3 :  {b.fst} =  ({a.fst}:Set) ∨  {b.fst} =  ({a.fst, a.snd}:Set) := by simpa using h3
    replace h4 :  {b.fst, b.snd} =  ({a.fst}:Set) ∨  {b.fst, b.snd} =  ({a.fst, a.snd}:Set) := by simpa using h4
    replace h1 := simplify_or_1 h1
    replace h2 := simplify_or_2 h2
    replace h3 := simplify_or_1 h3
    replace h4 := simplify_or_2 h4
    rcases h1 with h1 | h1
    rcases h2 with h2 | h2
    rcases h3 with h3 | h3
    grind
    rcases h4 with h4 | h4
    . grind
    obtain ⟨⟨h5, h6⟩, ⟨h7, h8⟩ ⟩ := h2, h4
    grind
    grind
    grind
    grind



instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/--
  A technical operation, turning a object $`x` and a set $`Y` to a set $`{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by grind)

@[simp]
theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _


theorem SetTheory.order_set_theorem {Y : Set} {a b c : Object}: (fun x z ↦ z = set_to_object (slice (↑x) Y)) a b ∧ (fun x z ↦ z = set_to_object (slice (↑x) Y)) a c → b = c := by
  intro ⟨h1, h2⟩
  have h3 := by simpa using h1
  simp_all


/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod];
  simp only [union_axiom];
  constructor
  . intro ⟨ S, hz, hS ⟩;
    rw [replacement_axiom] at hS;
    obtain ⟨ x, hx ⟩ := hS
    use x;
    simp_all
  rintro ⟨ x, y, rfl ⟩;
  use slice x Y;
  refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom];
  use x

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X :=
  ((mem_cartesian z X Y).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian z X Y).mp z.property)).choose

theorem SetTheory.Set.pair_eq_fst_snd {X Y:Set} (z:X ×ˢ Y) :
    z.val = (⟨ fst z, snd z ⟩:OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy: z.val = (⟨ fst z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, snd z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  simp_all

/-- This equips an {name}`OrderedPair` with proofs that $`x ∈ X` and $`y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by simp⟩

@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y;
  have := (mem_cartesian z X Y).mp z.property
  obtain ⟨ y', hy: z.val = (⟨ fst z, y' ⟩:OrderedPair) ⟩ := this.choose_spec
  simp [z] at *;
  simp [mk_cartesian] at *;
  simp [Subtype.val_inj] at *;
  rw [←hy.1]

@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y;
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx: z.val = (⟨ x', snd z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *;
  rw [←hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian]
  rw [Subtype.mk.injEq]
  rw [pair_eq_fst_snd]

/--
  {given -show}`x : X, y : Y`
  Connections with the Mathlib set product, which consists of Lean pairs like {lean}`(x, y)`
  equipped with a proof that {name}`x` is in the left set, and {name}`y` is in the right set.
  Lean pairs like {lean}`(x, y)` are similar to our {name}`OrderedPair`, but more general.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun z := ⟨(fst z, snd z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Example 3.5.5 -/
example : ({1, 2}: Set) ×ˢ ({3, 4, 5}: Set) = ({
  ((mk_cartesian (1: Nat) (3: Nat)): Object),
  ((mk_cartesian (1: Nat) (4: Nat)): Object),
  ((mk_cartesian (1: Nat) (5: Nat)): Object),
  ((mk_cartesian (2: Nat) (3: Nat)): Object),
  ((mk_cartesian (2: Nat) (4: Nat)): Object),
  ((mk_cartesian (2: Nat) (5: Nat)): Object)
}: Set) := by ext; aesop

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between {lean}`X ×ˢ Y` and {lean}`Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun := fun z ↦ mk_cartesian (snd z) (fst z)
  invFun := fun z ↦ mk_cartesian (snd z) (fst z)
  left_inv := by
    unfold Function.LeftInverse
    intro x
    simp_all
  right_inv := by
    unfold Function.RightInverse
    intro x
    simp_all

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f (mk_cartesian x y)
  left_inv _ := by ext; simp
  right_inv _ := by simp

/-- Definition 3.5.6.  The indexing set {name}`I` plays the role of $`{ i : 1 ≤ i ≤ n }` in the text.
    See Exercise 3.5.10 below for some connections between this concept and the preceding notion
    of Cartesian product and ordered pair.  -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩):I → iUnion I X)

/-- Definition 3.5.6 -/
abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

/-- Definition 3.5.6 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x := by
  simp only [iProd];
  simp only [specification_axiom'']
  constructor
  . intro ⟨ ht, x, h ⟩;
    use x
  intro ⟨ x, hx ⟩
  have h : t ∈ (I.iUnion X)^I := by simp [hx]
  use h, x

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by
    rw [mem_iProd];
    use x

@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
    tuple x = tuple y ↔ x = y := by
      refine ⟨?_, by aesop⟩
      intro h
      ext z;
      simp_all
      have h1 := congr($h z)
      simp_all

/-- Example 3.5.8. There is a bijection between {lean}`(X ×ˢ Y) ×ˢ Z` and {lean}`X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp


-- theorem x1 {i:Object} {X:Set}{x : Object} : x ∈ iProd (fun _:({i}:Set) ↦ X) → ∃y, y ∈ X := by
--   intro h
--   unfold iProd at h
--   rw [specification_axiom''] at h
--   obtain ⟨h1, h2⟩ := h
--   obtain ⟨y, h3⟩ := h2
--   rw [tuple] at h3
--   simp at h3
--   have hy : x = _ := h3
--   let f := fun i_1 ↦ y i_1
--   have h4 : f = f := by rfl
--   have h5 : i ∈ ({i}:Set) := by simp
--   have h6 := congr($h4 ⟨i, h5⟩)
--   unfold f at h6
--   let z : X.toSubtype := y ⟨i, h5⟩
--   use z
--   exact z.property

-- abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : I → iUnion I X :=
--   ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩):I → iUnion I X)

-- /-- Definition 3.5.6 -/
-- abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
--   ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)


/--
  Example 3.5.10. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
-- from: https://github.com/gaearon/analysis-solutions/blob/e6967c4dba422e0e8596063fff4b8ceba65aa568/analysis/Analysis/Section_3_5.lean#L237
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun := fun t ↦ ((mem_iProd t).mp t.property).choose ⟨i, by simp⟩
  invFun := fun x ↦ ⟨tuple fun i ↦ x, by apply tuple_mem_iProd⟩
  left_inv := by
    intro x
    have h := (mem_iProd x).mp x.property
    obtain hx := h.choose_spec
    ext
    rw [hx]
    rw [tuple_inj]
    ext ⟨t,ht⟩
    rw [mem_singleton] at ht
    simp_rw [ht]
  right_inv := by
    intro x
    simp_all
    generalize_proofs h pf
    have hx := h.choose_spec
    rw [tuple_inj] at *
    rw [← hx]

/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun := fun t ↦ ()
  invFun := fun x ↦ ⟨tuple fun i ↦ False.elim (not_mem_empty _ i.property), by apply tuple_mem_iProd⟩
  left_inv := by
    intro x
    simp_all
    ext
    have h := (mem_iProd x).mp x.property
    obtain hx := h.choose_spec
    rw [hx]
    rw [tuple_inj]
    ext ⟨i, hi⟩
    have h1 := not_mem_empty i
    contradiction
  right_inv := by
    intro x
    simp_all

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun _:I ↦ X) ≃ (I → X) where
  toFun := fun t ↦ ((mem_iProd t).mp t.property).choose
  invFun := fun x ↦ ⟨tuple x, by apply tuple_mem_iProd⟩
  left_inv := by
    intro x
    simp_all
    ext
    have h := (mem_iProd x).mp x.property
    obtain hx := h.choose_spec
    conv =>
      rhs
      rw [hx]
  right_inv := by
    intro x
    simp_all
    generalize_proofs pf1 pf2 pf3
    ext i
    have h1 := pf1 i
    rw [mem_iUnion] at h1
    obtain ⟨a, ha⟩ := h1
    have h2 := pf2 x i
    have h3 := pf3.choose_spec
    have h4 := congrFun h3 i
    exact (congrArg Subtype.val h4).symm

theorem SetTheory.Set.cartesian_eq {X Y:Set} {x:X} {y:Y} {z : X ×ˢ Y}: mk_cartesian (x) (y) = z ↔  (fst z) = x ∧ (snd z) = y := by
  constructor
  . intro h
    rw [← h]
    exact And.intro (fst_of_mk_cartesian x y) (snd_of_mk_cartesian x y)
  intro ⟨h1, h2⟩
  rw [← h1, ← h2]
  exact mk_cartesian_fst_snd_eq z

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun := fun t ↦
    let x := ((mem_iProd t).mp t.property).choose
    (mk_cartesian (x ⟨ 0, by simp ⟩) (x ⟨ 1, by simp ⟩))
  invFun := fun z ↦ ⟨tuple (X:=X) (fun i ↦ by
    have : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ := by aesop
    if h : i = ⟨0, by simp⟩ then
      rw [h];
      exact (fst z)
    else if h : i = ⟨1, by simp⟩ then
      rw [h];
      exact (snd z)
    else aesop
  ), by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    have h := (mem_iProd _).mp t.property
    have ht := h.choose_spec
    ext
    rw [ht, tuple_inj]
    ext i
    have : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ := by aesop
    if h : i = ⟨0, by simp⟩ then
      subst h;
      simp_all
    else if h : i = ⟨1, by simp⟩ then
      subst h;
       simp_all
    else tauto
  right_inv := by
    intro x
    simp_all
    generalize_proofs pf1 pf2 pf3 pf4 pf5 pf6
    apply cartesian_eq.mpr
    have h1 := pf6.choose_spec
    rw [tuple_inj] at h1
    rw [← h1]
    simp_all


/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun := fun t ↦
    let x := ((mem_iProd t).mp t.property).choose
    (mk_cartesian (x ⟨ 0, by simp ⟩) (mk_cartesian (x ⟨ 1, by simp ⟩) (x ⟨ 2, by simp ⟩)))
  invFun := fun z ↦ ⟨tuple (X:=X) (fun i ↦ by
    have : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ ∨ i = ⟨2, by simp⟩ := by aesop
    if h : i = ⟨0, by simp⟩ then
      rw [h];
      exact (fst z)
    else if h : i = ⟨1, by simp⟩ then
      rw [h];
      exact (fst (snd z))
    else if h : i = ⟨2, by simp⟩ then
      rw [h];
      exact (snd (snd z))
    else aesop
  ), by apply tuple_mem_iProd⟩
  left_inv := by
    intro t
    have h := (mem_iProd _).mp t.property
    have ht := h.choose_spec
    ext
    rw [ht, tuple_inj]
    ext i
    have : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ ∨ i = ⟨2, by simp⟩ := by aesop
    if h : i = ⟨0, by simp⟩ then
      subst h;
      simp_all
    else if h : i = ⟨1, by simp⟩ then
      subst h;
      simp_all
    else if h : i = ⟨2, by simp⟩ then
      subst h;
      simp_all
    else tauto
  right_inv := by
    intro x
    simp_all
    generalize_proofs pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8
    have h1 := pf8.choose_spec
    rw [tuple_inj] at h1
    rw [← h1]
    simp_all

lemma to_fun_iProd_equiv_pi {I:Set} {X: I → Set} (x: iProd X) : ∃y, y ∈ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) := by
  let h1 := ((mem_iProd _).mp x.property).choose
  let fi :  I.toSubtype → Object  := fun i ↦ h1 i
  use fi
  grind

-- theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
--     tuple x ∈ iProd X := by
--     rw [mem_iProd];
--     use x
lemma inv_fun_iProd_equiv_pi {I:Set} {X: I → Set}  (x : Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object))): ∃y, y ∈ iProd X := by
  have hx := x.property
  unfold Set.univ at hx
  unfold Set.pi at hx
  simp only [Set.mem_setOf_eq] at hx
  have hy : ∀ (i : I.toSubtype), x.val i ∈ X i := by
    intro i
    have h1 := hx i
    simp at h1
    exact h1
  let hz : ∀ (i : I.toSubtype), X i := fun i ↦ ⟨x.val i, by exact hy i⟩
  let ip := tuple_mem_iProd hz
  use tuple hz

/-- Connections with Mathlib's {name}`Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by
    have h := ((mem_iProd _).mp t.property)
    have ht := h.choose_spec
    ext;
    rw [ht]
  right_inv x := by
    ext y
    simp_all
    generalize_proofs pf1 pf2
    have h1 := pf2.choose_spec
    rw [tuple_inj] at h1
    rw [← h1]



/-
remark: there are also additional relations between these equivalences, but this begins to drift
into the field of higher order category theory, which we will not pursue here.
-/

/--
  Here we set up some an analogue of Mathlib {lean}`Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/
abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom''];
  constructor
  . intro ⟨ h1, h2 ⟩;
    use (⟨ x, h1 ⟩:nat)
    simp_all
  intro ⟨ m, hm, h ⟩
  -- ∃ (h : x ∈ nat), nat_equiv.symm ⟨x, h⟩ < n
  have h1 : x ∈ nat := by
    rw [h]
    have h2 := (m:nat).property
    exact (m:nat).property
  use h1
  simp_all

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  have h1 := (mem_Fin n x).mp x.property
  obtain ⟨m, hm, this⟩ := h1;
  use m
  use hm
  unfold Fin_mk
  rw [←Subtype.val_inj]
  exact this

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec


theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n := by
  obtain ⟨h1, h2⟩ := toNat_spec i
  exact h1

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  obtain ⟨h1,h2⟩ := toNat_spec i;
  conv =>
    rhs
    rw [h2]




@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n:ℕ} {i j: Fin n} : i = j ↔ (i:ℕ) = (j:ℕ) := by
  constructor
  · simp_all
  obtain ⟨li, hi⟩ := toNat_spec i
  obtain ⟨lj, hj⟩ := toNat_spec j
  intro h
  rw [hi]
  simp only [Fin_mk]
  simp only [←Subtype.val_inj]
  rw [h]
  simp


@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n:ℕ} (i: Fin n) {j:ℕ} : (i:Object) = (j:Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨w, rfl⟩ := h
    simp [←Object.natCast_inj]
  intro h
  rw [←h]
  simp


@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m:ℕ} (i: Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m):ℕ) = (i:ℕ) := by
  obtain ⟨val, property⟩ := i
  rw [toNat, toNat]
  simp only [Subtype.mk.injEq]
  simp only [exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose: Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property;
  rw [mem_Fin] at *;
  grind
⟩

/-- Connections with Mathlib's {lean}`Fin n` -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := by
    have h1 := (toNat_spec m)
    have h2 := h1.2.symm
    simp_all
  right_inv m := by simp

/-- Lemma 3.5.11 (finite choice) -/
theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom'']
    have empty (i:Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty);
    rw [mem_iProd];
    use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  have xxx := nonempty_def (hn hX')
  choose x'_obj hx' using xxx
  rw [mem_iProd] at hx';
  obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by
        ext;
        simpa [←Fin.coe_toNat]
      ⟨a, by grind⟩
    else
      have h1 := Fin.toNat_lt i
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp h1) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by
        simp [X']
        simp [i']
        simp [Fin_embed]
      ⟨x' i', by grind⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

-- lemma simplify_or_3 {a b:Set} {c : Object} : a = b ∨ a =  (SetTheory.set_to_object {b, c}:Set) → a = b ∨ (SetTheory.set_to_object b ∈ a ∧  c ∈ a) := by
--   intro h1
--   rcases h1 with h1 | h1
--   . exact Or.inl h1
--   apply Or.inr
--   rw [h1]
--   simp


-- lemma simplify_or_4 {c:Set} {a b d: Object} : {a, b} =  c ∨ {a, b} =  ({SetTheory.set_to_object c, d}:Set) → (a ∈ c ∧ b ∈ c) ∨ ((a = c ∧ b = d) ∨ (b = c ∧ a = d)) := by
--   intro h1
--   rcases h1 with h1 | h1
--   . apply Or.inl
--     rw [← h1]
--     simp
--   rw [pair_eq_pair_iff] at h1
--   exact Or.inr h1

lemma simplify_or_6 {a b c: Object} : (SetTheory.set_to_object ({a, b}:Set)) =  (SetTheory.set_to_object ({a, c}:Set)) → b = c := by
  intro h
  have h1 : b ∈ ({a, b}:Set) := by simp
  have h2 := SetTheory.set_to_object.injective h
  rw [h2] at h1
  rw [mem_pair] at h1
  rcases h1 with h1 | h1
  . rw [h1] at h2
    simp_all
    have h3 : c ∈ ({a, c}:Set) := by simp
    rw [← h2] at h3
    rw [mem_singleton] at h3
    exact h3.symm
  exact h1

lemma simplify_or_5 {a b c d: Object} : ({a, b}:Set) =  ({c, d}:Set) → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  intro h
  have h1 : a ∈ ({a, b}:Set) := by simp
  rw [h] at h1
  rw [mem_pair] at h1
  rcases h1 with h1 | h1
  . rw [h1] at h
    have h2 := congrArg SetTheory.set_to_object h
    replace h2 := simplify_or_6 h2
    exact Or.inl (And.intro h1 h2)
  rw [h1] at h
  conv at h =>
    rhs
    rw [pair_comm_eq]
  have h2 := congrArg SetTheory.set_to_object h
  replace h2 := simplify_or_6 h2
  exact Or.inr (And.intro h1 h2)

lemma simplify_not_1 (a1 a2 b1 b2: Object) : ¬ (a1 = SetTheory.set_to_object {b1, b2} ∧ b1 = SetTheory.set_to_object {a1, a2}) := by
  intro ⟨h1, h2⟩
  let A : Set := {a1, b1}
  have h3 : a1 ∈ A := by
    unfold A
    simp
  have h4 := SetTheory.Set.axiom_of_regularity (nonempty_of_inhabited h3)
  obtain ⟨x, hx⟩ := h4
  have px := x.property
  unfold A at px
  rw [mem_pair] at px
  rcases px with px | px
  . simp [h1] at px
    have h5 := (hx ({b1, b2}:Set)) px
    unfold A at h5
    rw [disjoint_iff] at h5
    have h6 : b1 ∈  ({b1, b2}:Set) ∩ {a1, b1} := by
      simp
    rw [h5] at h6
    have h7 := not_mem_empty b1
    contradiction
  simp [h2] at px
  have h5 := (hx ({a1, a2}:Set)) px
  unfold A at h5
  rw [disjoint_iff] at h5
  have h6 : a1 ∈  ({a1, a2}:Set) ∩ {a1, b1} := by
    simp
  rw [h5] at h6
  have h7 := not_mem_empty a1
  contradiction


/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    unfold Function.Injective
    rintro a b h
    simp at h
    apply (OrderedPair.eq a.fst a.snd b.fst b.snd).mpr
    have h1 := simplify_or_5 h
    rcases h1 with h1 | h1
    . obtain ⟨h2, h3⟩ := h1
      rw [h2] at h3
      replace h3 := simplify_or_6 h3
      exact And.intro h2 h3
    obtain ⟨h2, h3⟩ := h1
    replace h3 := h3.symm
    have h4 := And.intro h2 h3
    have h5 := simplify_not_1 a.fst a.snd b.fst b.snd
    contradiction


/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: Fin n → X
  surj: Function.Surjective x

/--
  Custom extensionality lemma for Exercise 3.5.2.
  Placing {attr}`@[ext]` on the structure would generate a lemma requiring proof of {lit}`t.x = t'.x`,
  but these functions have different types when {lean}`t.X ≠ t'.X`. This lemma handles that part.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t t':Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object)) :
    t = t' := by
  have ⟨X, x, surj⟩ := t;
  have ⟨X', x', surj'⟩ := t';
  subst hX;
  congr;
  ext;
  grind

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n) :
    t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by
    have ht1 := t.surj
    have ht2 := t'.surj
    unfold Function.Surjective at ht1 ht2
    constructor
    . intro h m
      rw [h]
    intro h
    apply ext
    . ext x;
      constructor
      . intro h1
        obtain ⟨a, ha⟩ := ht1 ⟨x, h1⟩
        have hb := h a
        simp [← Subtype.val_inj] at ha
        rw [hb] at ha
        grind
      intro h1
      obtain ⟨a, ha⟩ := ht2 ⟨x, h1⟩
      have hb := h a
      simp [← Subtype.val_inj] at ha
      rw [← hb] at ha
      grind
    exact h

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use {name}`OrderedPair.eq` or {name}`SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by
  rw [OrderedPair.eq]
  have h1 : p.fst = p.fst := rfl
  have h2 : p.snd = p.snd := rfl
  exact And.intro h1 h2


theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  rw [OrderedPair.eq, OrderedPair.eq]
  grind

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by grind

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a = tuple a := by rw [SetTheory.Set.tuple_inj]


theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by
      rw [SetTheory.Set.tuple_inj, SetTheory.Set.tuple_inj]
      grind


theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by
      rw [SetTheory.Set.tuple_inj] at *
      rw [← hab] at hbc
      exact hbc



/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  ext x;
  rw [mem_union]
  simp only [mem_cartesian]
  constructor
  . rintro ⟨a, ⟨bc, hbc⟩⟩
    have h := bc.property
    rw [mem_union] at h
    rcases h with h | h
    . apply Or.inl
      use a
      use ⟨bc, h⟩
    apply Or.inr
    use a
    use ⟨bc, h⟩
  intro h
  rcases h with h | h
  . obtain ⟨a, ⟨bc, hbc⟩⟩ := h
    use a
    have h1 : bc.val ∈ B ∪ C := by
      rw [mem_union]
      exact Or.inl bc.property
    use ⟨bc, h1⟩
  obtain ⟨a, ⟨bc, hbc⟩⟩ := h
  use a
  have h1 : bc.val ∈ B ∪ C := by
    rw [mem_union]
    exact Or.inr bc.property
  use ⟨bc, h1⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  ext x;
  rw [mem_inter]
  simp only [mem_cartesian]
  constructor
  . rintro ⟨a, ⟨bc, hbc⟩⟩
    have h := bc.property
    rw [mem_inter] at h
    obtain ⟨hb, hc⟩ := h
    constructor
    . use a, ⟨bc, hb⟩
    use a, ⟨bc, hc⟩
  rintro ⟨h1, h2⟩
  obtain ⟨a1, ⟨bc1, hbc1⟩⟩ := h1
  obtain ⟨a2, ⟨bc2, hbc2⟩⟩ := h2
  rw [hbc1] at hbc2
  -- SetTheory.set_to_object.injective
  have h3 := OrderedPair.toObject.injective hbc2
  simp at h3
  obtain ⟨h4, h5⟩ := h3
  use a1
  have h6 : bc2.val ∈ C := bc2.property
  rw [← h5] at h6
  have h7 : bc1.val ∈ B ∩ C := by
    rw [mem_inter]
    exact And.intro bc1.property h6
  use ⟨bc1, h7⟩


/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  ext x;
  rw [mem_sdiff]
  simp only [mem_cartesian]
  constructor
  . rintro ⟨a, ⟨bc, hbc⟩⟩
    have h := bc.property
    rw [mem_sdiff] at h
    obtain ⟨hb, hc⟩ := h
    constructor
    . use a, ⟨bc, hb⟩
    rintro ⟨a1, ⟨b1, hb1⟩⟩
    rw [hbc] at hb1
    have h2 := OrderedPair.toObject.injective hb1
    simp at h2
    obtain ⟨h3, h4⟩ := h2
    rw [h4] at hc
    have h5 := b1.property
    contradiction
  rintro ⟨h1, h2⟩
  obtain ⟨a1, ⟨bc1, hbc1⟩⟩ := h1
  push_neg at h2
  use a1
  have hbc2 : ¬ (bc1.val ∈ C) := by
    intro h3
    have h4 := h2 a1 ⟨bc1, h3⟩
    rw [hbc1] at h4
    simp at h4
  have hbc3 :  bc1.val ∈ B \ C := by
    rw [mem_sdiff]
    exact And.intro bc1.property hbc2
  use ⟨bc1, hbc3⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by
  ext x;
  rw [mem_union]
  simp only [mem_cartesian]
  constructor
  . rintro ⟨a, ⟨bc, hbc⟩⟩
    have h := a.property
    rw [mem_union] at h
    rcases h with h | h
    . apply Or.inl
      use ⟨a, h⟩
      use bc
    apply Or.inr
    use ⟨a, h⟩
    use bc
  intro h
  rcases h with h | h
  . obtain ⟨a, ⟨bc, hbc⟩⟩ := h
    use ⟨a, by rw [mem_union];apply Or.inl;exact a.property⟩
    use bc
  obtain ⟨a, ⟨bc, hbc⟩⟩ := h
  use ⟨a, by rw [mem_union];apply Or.inr;exact a.property⟩
  use bc

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by
  ext x;
  rw [mem_inter]
  simp only [mem_cartesian]
  constructor
  . rintro ⟨a, ⟨bc, hbc⟩⟩
    have h := a.property
    rw [mem_inter] at h
    obtain ⟨hb, hc⟩ := h
    constructor
    . use ⟨a, hb⟩, bc
    use ⟨a, hc⟩, bc
  rintro ⟨h1, h2⟩
  obtain ⟨a1, ⟨bc1, hbc1⟩⟩ := h1
  obtain ⟨a2, ⟨bc2, hbc2⟩⟩ := h2
  rw [hbc1] at hbc2
  -- SetTheory.set_to_object.injective
  have h3 := OrderedPair.toObject.injective hbc2
  simp at h3
  obtain ⟨h4, h5⟩ := h3
  have ha : a1.val ∈ A ∩ B := by
    rw [mem_inter]
    have h6 := a2.property
    rw [← h4] at h6
    exact And.intro a1.property h6
  use ⟨a1, ha⟩
  use bc1

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by
  ext x;
  rw [mem_sdiff]
  simp only [mem_cartesian]
  constructor
  . rintro ⟨a, ⟨bc, hbc⟩⟩
    have h := a.property
    rw [mem_sdiff] at h
    obtain ⟨hb, hc⟩ := h
    constructor
    . use ⟨a, hb⟩, bc
    rintro ⟨a1, ⟨b1, hb1⟩⟩
    rw [hbc] at hb1
    have h2 := OrderedPair.toObject.injective hb1
    simp at h2
    obtain ⟨h3, h4⟩ := h2
    rw [h3] at hc
    have h5 := a1.property
    contradiction
  rintro ⟨h1, h2⟩
  obtain ⟨a1, ⟨bc1, hbc1⟩⟩ := h1
  push_neg at h2
  have h3 : a1.val ∈ A \ B := by
    rw [mem_sdiff]
    constructor
    . exact a1.property
    intro h3
    have h4 := h2 ⟨a1, h3⟩ bc1
    rw [hbc1] at h4
    simp at h4
  use ⟨a1, h3⟩
  use bc1

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  ext x;
  rw [mem_inter]
  simp only [mem_cartesian]
  constructor
  . rintro ⟨h1, h2⟩
    obtain ⟨x1, ⟨y1, hy1⟩⟩ := h1
    obtain ⟨x2, ⟨y2, hy2⟩⟩ := h2
    rw [hy1] at hy2
    have h3 := OrderedPair.toObject.injective hy2
    simp at h3
    obtain ⟨h4, h5⟩ := h3
    have h6 : x1.val ∈ A ∩ C ∧ y1.val ∈ B ∩ D := by
      simp only [mem_inter]
      have h7 := x2.property
      have h8 := y2.property
      rw [← h4] at h7
      rw [← h5] at h8
      exact And.intro (And.intro x1.property h7) (And.intro y1.property h8)
    use ⟨x1, h6.1⟩
    use ⟨y1, h6.2⟩
  intro ⟨x1, ⟨y1, h⟩⟩
  have h1 := x1.property
  have h2 := y1.property
  rw [mem_inter] at h1 h2
  constructor
  . use ⟨x1, h1.1⟩
    use ⟨y1, h2.1⟩
  use ⟨x1, h1.2⟩
  use ⟨y1, h2.2⟩


/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use ({0}:Set)
  use ({1}:Set)
  use ({1}:Set)
  use ({0}:Set)
  have h1 : ({0}:Set) ×ˢ ({1}:Set) = ({((mk_cartesian (0: Nat) (1: Nat)): Object)}: Set) := by
    ext
    aesop
  have h2 : ({1}:Set) ×ˢ ({0}:Set) = ({((mk_cartesian (1: Nat) (0: Nat)): Object)}: Set) := by
    ext
    aesop
  have h3 : (({0} ∪ {1}):Set) = ({0,1}:Set) := by
    ext
    aesop
  have h4 : (({1} ∪ {0}):Set) = ({0,1}:Set) := by
    ext
    aesop
  rw [h3, h4]
  have h5 : ((mk_cartesian (0: Nat) (0: Nat)): Object) ∈ ({0, 1}:Set) ×ˢ ({0, 1}:Set) := by
    aesop
  rw [h1, h2]
  intro h6
  have h7 : ((mk_cartesian (0: Nat) (0: Nat)): Object) ∉  ({((mk_cartesian (0: Nat) (1: Nat)): Object)}: Set) ∪ ({((mk_cartesian (1: Nat) (0: Nat)): Object)}: Set) := by
    intro h7
    rw [mem_union] at h7
    rcases h7 with h7 | h7
    . rw [mem_singleton] at h7
      simp [Subtype.val_inj] at h7
      unfold mk_cartesian at h7
      simp at h7
      simp [Subtype.val_inj] at h7
    rw [mem_singleton] at h7
    simp [Subtype.val_inj] at h7
    unfold mk_cartesian at h7
    simp at h7
    simp [Subtype.val_inj] at h7
  rw [← h6] at h5
  contradiction


/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use ({0}:Set)
  use ({0}:Set)
  use ({0}:Set)
  use ({1}:Set)
  -- ⊢ {0} ×ˢ {0} \ {0} ×ˢ {1} ≠ ({0} \ {0}) ×ˢ ({0} \ {1})
  have h1 : ({0}:Set) ×ˢ ({0}:Set) = ({((mk_cartesian (0: Nat) (0: Nat)): Object)}: Set) := by
    ext
    aesop
  have h2 : ({0}:Set) ×ˢ ({1}:Set) = ({((mk_cartesian (0: Nat) (1: Nat)): Object)}: Set) := by
    ext
    aesop
  have h3 : (({0}:Set) \ ({0}:Set)) = ∅ := by
    ext
    aesop
  have h4 : (∅:Set) ×ˢ (({0}:Set) \ ({1}:Set)) = ∅ := by
    ext
    aesop
  have h5 : ({0}:Set) ×ˢ ({0}:Set) \ ({0}:Set) ×ˢ ({1}:Set) = ({((mk_cartesian (0: Nat) (0: Nat)): Object)}: Set) := by
    rw [h1, h2]
    ext x;
    rw [mem_sdiff]
    constructor
    . intro ⟨h5, h6⟩
      exact h5
    intro h
    constructor
    . exact h
    intro h2
    rw [mem_singleton] at *
    rw [h] at h2
    unfold mk_cartesian at h2
    simp at h2
    simp [Subtype.val_inj] at h2
  rw [h3, h4, h5]
  intro h
  have h6 := not_mem_empty ((mk_cartesian (0: Nat) (0: Nat)): Object)
  have h7 : ((mk_cartesian (0: Nat) (0: Nat)): Object) ∈ ({((mk_cartesian (0: Nat) (0: Nat)): Object)}:Set) := by simp
  rw [h] at h7
  contradiction


/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) (hC: C ≠ ∅) (hD: D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
      have ⟨a, ha⟩ := nonempty_def hA
      have ⟨b, hb⟩ := nonempty_def hB
      have ⟨c, hc⟩ := nonempty_def hC
      have ⟨d, hd⟩ := nonempty_def hD
      constructor
      . intro h
        rw [subset_def] at h
        constructor
        . intro x hx
          have hxb : ((mk_cartesian ⟨x, hx⟩ ⟨b, hb⟩): Object) ∈ A ×ˢ B := by
            rw [mem_cartesian]
            use ⟨x, hx⟩
            use ⟨b, hb⟩
            unfold mk_cartesian
            simp
          have hxc := h ((mk_cartesian ⟨x, hx⟩ ⟨b, hb⟩): Object) hxb
          rw [mem_cartesian] at hxc
          obtain ⟨xx, ⟨yy, hxxyy⟩⟩ := hxc
          unfold mk_cartesian at hxxyy
          simp at hxxyy
          obtain ⟨h1, h2⟩ := hxxyy
          have h3 := xx.property
          rw [← h1] at h3
          exact h3
        intro x hx
        have hxb : ((mk_cartesian ⟨a, ha⟩ ⟨x, hx⟩): Object) ∈ A ×ˢ B := by
            rw [mem_cartesian]
            use ⟨a, ha⟩
            use ⟨x, hx⟩
            unfold mk_cartesian
            simp
        have hxc := h ((mk_cartesian ⟨a, ha⟩ ⟨x, hx⟩): Object) hxb
        rw [mem_cartesian] at hxc
        obtain ⟨xx, ⟨yy, hxxyy⟩⟩ := hxc
        unfold mk_cartesian at hxxyy
        simp at hxxyy
        obtain ⟨h1, h2⟩ := hxxyy
        have h3 := yy.property
        rw [← h2] at h3
        exact h3
      intro ⟨h1, h2⟩ x hx
      rw [mem_cartesian] at *
      obtain ⟨a, ⟨b, hab⟩⟩ := hx
      rw [subset_def] at h1 h2
      use ⟨a, h1 a a.property⟩
      use ⟨b, h2 b b.property⟩







def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use ({1}:Set)
  use (∅:Set)
  use (∅:Set)
  use (∅:Set)
  simp_all
  apply Or.inl
  constructor
  . intro x hx
    aesop
  intro h
  rw [subset_def] at h
  have h1 : 1 ∈ ({1}:Set) := by simp
  have h2 := h 1 h1
  have h3 := not_mem_empty 1
  contradiction


/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
    ∃! h: Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by
    set fx := fun z ↦ mk_cartesian (f z) (g z)
    apply ExistsUnique.intro fx
    . constructor
      . ext x
        unfold fx
        simp
      ext
      unfold fx
      simp
    intro gx ⟨h1, h2⟩
    ext z
    unfold fx
    have h3 := congr($h1 z)
    have h4 := congr($h2 z)
    rw [← h3, ← h4]
    simp


/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by
      constructor
      . intro h
        by_contra h1
        push_neg at h1
        have h2 := finite_choice h1
        contradiction
      -- inspired by https://github.com/Shaunticlair/analysis/blob/b0bf9f3fb006f08e0a450a8685251709f7223f86/analysis/Analysis/Section_3_5.lean#L887
      intro h
      by_contra! ht
      replace ht := SetTheory.Set.nonempty_def ht
      obtain ⟨t,ht⟩ := ht
      obtain ⟨i,hi⟩ := h
      unfold iProd at ht
      simp at ht
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ht
      suffices (b i).val ∈ (∅:Set) by simp_all
      rw [← hi]
      apply (b i).property



/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by sorry

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
    graph f = graph f' ↔ f = f' := by sorry

theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
    ∃! f: X → Y, G = graph f := by sorry

/--
  Exercise 3.5.11. This trivially follows from {name}`SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from {name}`SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
    ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := sorry

/-- Exercise 3.5.12, with errata from web site incorporated -/
theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
    ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by sorry

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have nat_coe_eq {m:nat} {n} : (m:ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m:nat} : (m:ℕ) = 0 → m = 0 := nat_coe_eq
  obtain ⟨f, hf⟩ := recursion nat' sorry sorry
  apply existsUnique_of_exists_of_unique
  · use f
    constructor
    · constructor
      · intro x1 x2 heq
        induction' hx1: (x1:ℕ) with i ih generalizing x1 x2
        · sorry
        sorry
      sorry
    sorry
  sorry


end Chapter3
