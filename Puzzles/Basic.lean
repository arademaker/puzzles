
/-
See here for the motivation of the discussion
https://aarinc.org/Newsletters/141-2023-06.html#geoff

The formalization and solutions using refutation-based provers:
https://www.tptp.org/cgi-bin/SeeTPTP?Category=Problems&Domain=PUZ&File=PUZ001+1.p

Proofs by refutation are not easy to follow. A direct formalization in Lean would be easier?
-/

section tptp

variable (u : Type)

variable (lives : u → Prop)

variable (killed hates richer : u → u → Prop)
variable (agatha butler charles : u)

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

opaque hates : u → u → Prop
opaque person : u → Prop
opaque _hate_v_1 : e → u → u → Prop

theorem test_aux (P : Prop) (Q : e → Prop) :
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

theorem sentence3
  (Agatha agatha charles Charles : u)
  (hh₁ : Agatha = agatha)
  (hh₄ : Charles = charles)
  (hh₂ : ∀ x y, (∃ e1, _hate_v_1 e1 x y) ↔ hates x y)
  (hh₃ : ∀ x y, hates x y → person x ∧ person y) :
  (∃ x15, Agatha = x15 ∧ (∃ x3, Charles = x3
    ∧ (∀ x9, (∃ e20, person x9 ∧ _hate_v_1 e20 x15 x9) →
    ¬(∃ e2, _hate_v_1 e2 x3 x9)))) →
    (∀ x, hates agatha x → ¬ hates charles x) := by
  intro h1 a
  intro haa hca
  apply Exists.elim h1; clear h1
  intro a1
  intro h₂
  apply Exists.elim (h₂.right)
  intro c
  intro h₄
  apply (h₄.right a)
  rw [test_aux, hh₂]
  apply And.intro
  exact (hh₃ agatha a haa).right
  rw [←h₂.left,hh₁]
  exact haa
  rw [hh₂,←h₄.left,hh₄]
  exact hca
  done

opaque _rich_a_in : e → u → Prop
opaque more_comp : e → e → u → Prop
opaque _butler_n_1 : u → Prop
opaque richer : u → u → Prop

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

theorem sentence7
  (h₁ : ∀ x y, (∃ e1, _hate_v_1 e1 x y) ↔ hates x y)
  (h₂ : ∀ x y, hates x y → person x ∧ person y) :
  (∀ x3, person x3 → ¬(∀ x8, person x8 → (∃ e2, _hate_v_1 e2 x3 x8)))
   → ¬(∃ x, ∀ y, hates x y) :=
  by
  intro h1 h2
  apply Exists.elim h2; clear h2
  intro a h3
  have h4 := h1 a $ (h₂ a a $ h3 a).left
  apply h4; clear h4
  intro b _
  rw [h₁]
  exact h3 b
  done

end nl
