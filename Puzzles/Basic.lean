
/-
See here for the motivation of the discussion
https://aarinc.org/Newsletters/141-2023-06.html#geoff

The formalization and solutions using refutation-based provers:
https://www.tptp.org/cgi-bin/SeeTPTP?Category=Problems&Domain=PUZ&File=PUZ001+1.p

Proofs by refutation are not easy to follow. A direct formalization in Lean would be easier?
-/

section tptp

variable (u : Type)

variable (agatha butler charles : u)
variable (lives : u → Prop)
variable (killed hates richer : u → u → Prop)

variable (pel55_1 : ∃ x : u, lives x ∧ killed x agatha)
variable (pel55_2_1 : lives agatha)
variable (pel55_2_2 : lives butler)
variable (pel55_2_3 : lives charles)
variable (pel55_3 : ∀ x, lives x → x = agatha ∨ x = butler ∨ x = charles)
variable (pel55_4 : ∀ x y, killed x y → hates x y)
variable (pel55_5 : ∀ x y, killed x y → ¬ richer x y)
variable (pel55_6 : ∀ x, hates agatha x → ¬ hates charles x)

variable (pel55_7 : ∀ x, x ≠ butler → hates agatha x)
variable (pel55_8 : ∀ x, ¬ richer x agatha → hates butler x)
variable (pel55_9 : ∀ x, hates agatha x → hates butler x)

variable (pel55_10 : ∀ x, ∃ y, ¬ hates x y)
variable (pel55_10' : ¬ ∃ x, ∀ y, lives y → hates x y)

variable (pel55_11 : agatha ≠ butler)

theorem result : killed agatha agatha := by
  have ⟨n,h1,h2⟩ := pel55_1
  have h3 := pel55_3 n h1
  have hC_innocent : ¬killed charles agatha := by
    have h_AA := pel55_7 agatha pel55_11
    have h_CA := pel55_6 agatha h_AA
    intro h
    exact h_CA (pel55_4 charles agatha h)

  cases h3 with
  | inl h => rw [h] at h2; exact h2
  | inr h => cases h with
    | inl h =>
      rw [h] at h1 h2; clear h
      apply False.elim
      apply pel55_10'; exists butler
      intro y hy
      cases pel55_3 y hy with
      | inl h => rw [h]; exact pel55_4 butler agatha h2
      | inr h => cases h with
        | inl h => rw [h]; exact pel55_8 butler (pel55_5 butler agatha h2)
        | inr h =>
          rw [h]
          apply pel55_9 charles
          apply pel55_7 charles
          intro H
          rw [←H] at h2
          exact hC_innocent h2

    | inr h =>
      rw [h] at h2
      apply False.elim
      exact hC_innocent h2
  done


end tptp


section nl

opaque u : Type
opaque e : Type

opaque  lives : u → Prop
opaque  hates : u → u → Prop
opaque killed : u → u → Prop
opaque richer : u → u → Prop

opaque         person : u → Prop
opaque      _in_p_dir : e → e → u → Prop
opaque      _hate_v_1 : e → u → u → Prop
opaque      _live_v_1 : e → u → Prop
opaque      _kill_v_1 : e → u → u → Prop
opaque      _except_p : e → u → u → Prop
opaque     _rich_a_in : e → u → Prop
opaque      more_comp : e → e → u → Prop
opaque    _butler_n_1 : u → Prop
opaque       _be_v_id : e → u → u → Prop
opaque  implicit_conj : u → u → u → Prop
opaque   _people_n_of : u → Prop
opaque _therein_p_dir : e → e → Prop
opaque      _only_a_1 : e → u → Prop
opaque     _never_a_1 : e → Prop → Prop
opaque   _victim_n_of : u → Prop
opaque    _killer_n_1 : u → Prop
opaque    _always_a_1 : e → Prop
opaque           poss : e → u → u → Prop
opaque           pron : u → Prop

opaque         _and_c {α : Type} : α → α → α → Prop

variable (agatha Agatha charles Charles butler : u)
variable (haa : Agatha = agatha)
variable (hcc : Charles = charles)


theorem aux0 (P : u → Prop)
  : ∀ c, (∃ x, c = x ∧ P x) ↔ P c := by
  intro y
  apply Iff.intro
  intro h
  apply Exists.elim h; clear h
  intro x h1
  rw [h1.left]
  exact h1.right
  intro h
  apply Exists.intro y
  exact And.intro rfl h
  done


theorem aux1 (P : Prop) (Q : e → Prop) :
  (∃ x, P ∧ Q x) ↔ P ∧ (∃ x, Q x) := by
   apply Iff.intro
   intro h
   apply And.intro
   apply Exists.elim h
   intro a h1
   exact h1.left
   apply Exists.elim h
   intro a h1
   apply Exists.intro a
   exact h1.right
   intro h
   apply Exists.elim h.right
   intro a h2
   apply Exists.intro a
   exact And.intro h.left h2
   done


theorem aux2 (P : e → u → u → Prop)
  : ∀ c z, (∃ x, c = x ∧ ∃ e, P e x z) ↔ ∃ e, P e c z := by
  intro y z
  apply Iff.intro
  intro h
  apply Exists.elim h; clear h
  intro x h1
  rw [h1.left]
  exact h1.right
  intro h
  apply Exists.intro y
  exact And.intro rfl h
  done


/- Someone who lives in Dreadbury Mansion killed Aunt Agatha. -/

theorem sentence0
  (h₂ : ∀ x, person x ∧ (∃ e1, _live_v_1 e1 x ∧ ∃ e2, _in_p_dir e2 e1 Dreadbury)
    ↔ lives x)
  (h₃ : ∀ x y, (∃ e1, _kill_v_1 e1 x y) ↔ killed x y) :
  (∃ x10, Dreadbury = x10 ∧ (∃ x3, (∃ e8 e9, person x3 ∧ _live_v_1 e8 x3 ∧ _in_p_dir e9 e8 x10)
   ∧ (∃ x16, Agatha = x16 ∧ (∃ e2, _kill_v_1 e2 x3 x16))))
   → (∃ x, lives x ∧ killed x agatha) := by
  intro h1
  simp [aux0] at h1
  simp [h₃] at h1
  simp [h₂] at h1
  apply Exists.elim h1; clear h1
  intro a h2; rw [haa] at h2
  apply Exists.intro a ; exact h2
  done


/- Agatha, the butler, and Charles live in Dreadbury Mansion,
   and are the only people who live therein. -/

theorem sentence1 :
  (∃ x32, Dreadbury = x32 ∧ (∃ x14, (∃ x24, Charles = x24 ∧ (∃ x19, _butler_n_1 x19
   ∧ _and_c x14 x19 x24)) ∧ (∃ x39, (∃ e44 e46 e47, _only_a_1 e44 x39
   ∧ _people_n_of x39 ∧ _live_v_1 e46 x39 ∧ _therein_p_dir e47 e46)
   ∧ (∃ x3, (∃ x8, Agatha = x8 ∧ implicit_conj x3 x8 x14)
   ∧ (∃ e30 e31 e2 e38, _live_v_1 e30 x3 ∧ _in_p_dir e31 e30 x32
   ∧ _and_c e2 e30 e38 ∧ _be_v_id e38 x3 x39)))))
   → (∀ x, lives x → x = agatha ∨ x = butler ∨ x = charles) := by
  intro h1 p h2
  simp [aux0,aux1,aux2] at h1
  sorry


/- A killer always hates his victim, and is never richer than his victim.
   obs: translation error. The next theorem is a manually fixed version -/

#check (∃ e2 e22 e9 x10,
 (∃ x16, pron x16
 ∧ (∃ e15, poss e15 x10 x16
 ∧ _victim_n_of x10))
 ∧ (∃ x34, pron x34
 ∧ (∃ x3, _killer_n_1 x3
 ∧ (∃ e22, _always_a_1 e9
 ∧ _hate_v_1 e9 x3 x10
 ∧ _and_c e2 e9 e22
 ∧ _never_a_1 e22 (∃ x28, (∃ e9 e9 e2 e33, poss e33 x28 x34 ∧ _victim_n_of x28)
  ∧ (∃ e25 e27, _rich_a_in e25 x3 ∧ more_comp e27 e25 x28))))))
→ (∀ x y, killed x y → hates x y) ∧ (∀ x y, killed x y → ¬richer x y)

theorem sentence2
 (h₁ : ∀ e1, _never_a_1 e1 P ↔ ¬ P) :
 (∃ e2 e9 x10,
 (∃ x16, pron x16 ∧ (∃ e15, poss e15 x10 x16
  ∧ _victim_n_of x10))
 ∧ (∃ x34, pron x34
 ∧ (∃ x3, _killer_n_1 x3
 ∧ (∃ e22, _always_a_1 e9
 ∧ _hate_v_1 e9 x3 x10
 ∧ _and_c e2 e9 e22
 ∧ _never_a_1 e22 (∃ x28, (∃ e33, poss e33 x28 x34 ∧ _victim_n_of x28)
  ∧ (∃ e25 e27, _rich_a_in e25 x3 ∧ more_comp e27 e25 x28))))))
→ (∀ x y, killed x y → hates x y) ∧ (∀ x y, killed x y → ¬richer x y) := by
  intro h1
  simp [aux0,aux1,h₁] at h1
  sorry


/- Charles hates no one that Aunt Agatha hates. -/

theorem sentence3
  (hh₂ : ∀ x y, (∃ e1, _hate_v_1 e1 x y) ↔ hates x y)
  (hh₃ : ∀ x y, hates x y → person x ∧ person y) :
  (∃ x15, Agatha = x15 ∧ (∃ x3, Charles = x3
    ∧ (∀ x9, (∃ e20, person x9 ∧ _hate_v_1 e20 x15 x9) →
    ¬(∃ e2, _hate_v_1 e2 x3 x9)))) →
    (∀ x, hates agatha x → ¬ hates charles x) := by
  intro h1 a
  intro Haa Hca
  apply Exists.elim h1; clear h1
  intro a1
  intro h₂
  apply Exists.elim (h₂.right)
  intro c
  intro h₄
  apply (h₄.right a)
  rw [aux1, hh₂]
  apply And.intro
  exact (hh₃ agatha a Haa).right
  rw [←h₂.left, haa]
  exact Haa
  rw [hh₂,←h₄.left,hcc]
  exact Hca
  done


/- Agatha hates everyone except the butler. -/

theorem sentence4
  (h₁ : ∀ x y, (∃ e1, _hate_v_1 e1 x y) ↔ hates x y)
  (h₂ : ∀ x y, (∃ e, _except_p e x y) ↔ x ≠ y)
  (h₃ : ∀ x y, hates x y → person x ∧ person y)
  (h₄ : ∀ x, _butler_n_1 x ↔ x = butler)
  (h₅ : ∀ x, _butler_n_1 x → person x)
  (h₆ : agatha ≠ butler) :
  (∀ x9, (∃ x15, _butler_n_1 x15 ∧ (∃ e14, person x9 ∧ _except_p e14 x9 x15))
    → (∃ x3, Agatha = x3 ∧ (∃ e2, _hate_v_1 e2 x3 x9)))
    → (∀ x, x ≠ butler → hates agatha x) := by
  sorry


/- The butler hates everyone not richer than Aunt Agatha. -/

theorem sentence5
  (h₂ : ∀ x y, (∃ e1 e2, _rich_a_in e1 x ∧ more_comp e2 e1 y) ↔ richer x y)
  (h₃ : ∀ x y, (∃ e1, _hate_v_1 e1 x y) ↔ hates x y)
  (h₅ : forall x, _butler_n_1 x ↔ x = butler)
  (h₆ : ∀ x y, ¬ richer x y → person x ∧ person y)
  (h₇ : Agatha = agatha) :
  (∃ x19, Agatha = x19 ∧ (∀ x8, person x8 ∧ ¬(∃ e16 e18, _rich_a_in e16 x8 ∧ more_comp e18 e16 x19)
   → (∃ x3, _butler_n_1 x3 ∧ (∃ e2, _hate_v_1 e2 x3 x8))))
   → (∀ x, ¬ richer x agatha → hates butler x) := by
  intro h1 a h2
  apply Exists.elim h1; clear h1
  intro a1 h3
  have h4 := h3.right a
  have h5 := h3.left ; clear h3
  rw [h₂,← h5] at h4
  rw [← h₇] at h2
  have h6 := And.intro (h₆ a Agatha h2).left h2
  have h7 := h4 h6
  apply Exists.elim h7; clear h7
  intro b h7
  rw [h₃,h₅] at h7
  rw [← h7.left]
  exact h7.right
  done


/- The butler hates everyone Aunt Agatha hates. -/

theorem sentence6
 (h₁ : ∀ x y, (∃ e1, _hate_v_1 e1 x y) ↔ hates x y)
 (h₂ : ∀ x y, hates x y → person x ∧ person y)
 (h₃ : ∀ x, _butler_n_1 x ↔ x = butler) :
 (∀ x8, (∃ x14, Agatha = x14 ∧ (∃ e19, person x8 ∧ _hate_v_1 e19 x14 x8))
  → (∃ x3, _butler_n_1 x3 ∧ (∃ e2, _hate_v_1 e2 x3 x8)))
  → (∀ x, hates agatha x → hates butler x) := by
  intro h1 a h2
  have h3 := h1 a; clear h1
  simp [h₁] at h3; rw [haa] at h3
  have h4 := h3 (h₂ agatha a h2).2 h2 ; clear h3
  simp [h₃] at h4
  assumption
  done


/- No one hates everyone. -/

theorem sentence7
  (h₁ : ∀ x y, (∃ e1, _hate_v_1 e1 x y) ↔ hates x y)
  (h₂ : ∀ x y, hates x y → person x ∧ person y) :
  (∀ x3, person x3 → ¬(∀ x8, person x8 → (∃ e2, _hate_v_1 e2 x3 x8)))
   → ¬(∃ x, ∀ y, hates x y) := by
  intro h1 h2
  apply Exists.elim h2; clear h2
  intro a h3
  have h4 := h1 a $ (h₂ a a $ h3 a).left
  apply h4; clear h4
  intro b _
  rw [h₁]
  exact h3 b
  done


/- Agatha is not the butler. -/

theorem sentence8
 (h₁ : ∀ x, _butler_n_1 x ↔ x = butler)
 (h₂ : ∀ x y, (∃ e1, _be_v_id e1 x y) ↔ x = y) :
 ¬(∃ x10, _butler_n_1 x10 ∧ (∃ x3, Agatha = x3 ∧ (∃ e2, _be_v_id e2 x3 x10)))
  → agatha ≠ butler := by
  intro h1 h2
  apply h1
  simp [aux0]
  apply Exists.intro butler
  have h3 := (h₁ butler).2 rfl
  apply And.intro
  exact h3
  rw [h₂]
  rw [← haa] at h2 ; exact h2
  done


end nl
