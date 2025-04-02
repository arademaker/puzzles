
section Agatha

opaque u : Type

opaque aunt : u → Prop
opaque person : u → Prop
opaque name : u → Prop
opaque hate : u → Prop
opaque butler : u → Prop
opaque mansion : u → Prop
opaque live : u → Prop
opaque past : u → Prop
opaque same : u → Prop
opaque size : (u → Prop) → Nat
opaque kill : u → Prop
opaque wealth : u → Prop
opaque only : u → Prop
opaque greater : (u → Prop) → u → Prop
opaque agent : (u → Prop) → u → Prop
opaque victim : u → Prop
opaque possessive : u → Prop

variable (lit : String → u)
variable (uset : (u → Prop) → u)

variable (charles : u)
variable (arg1 arg2 : u → u)


-- 1. Someone who lives in Dreadbury Mansion killed Aunt Agatha.
variable (h1 :
 ∃ s, (person s
 ∧ ∃ l, (live l ∧ arg1 l = s
  ∧ ∃ m, mansion m ∧ (∃ n, (name n ∧ arg1 n = m ∧ arg2 n = lit "Dreadbury")
  ∧ arg2 l = m))
 ∧ ∃ a, (aunt a ∧ ∃ n, (name n ∧ arg1 n = a ∧ arg2 n = lit "Agatha")
 ∧ ∃ k, (kill k ∧ past k ∧ arg1 k = s ∧ arg2 k = a)))
)

-- 2. Agatha, the butler, and Charles live in Dreadbury Mansion, and are the only people who live therein.
variable (h2 :
 ∃ a, (∃ n, name n ∧ arg1 n = a ∧ arg2 n = lit "Agatha")
 ∧ ∃ B, B = (λ b => butler b) ∧ size B = 1
 ∧ ∃ c, (∃ n, name n ∧ arg1 n = c ∧ arg2 n = lit "Charles")
 ∧ ∃ S, (S = (λ s => s = a ∨ B s ∨ s = c)
 ∧ ∃ m, mansion m ∧ (∃ n, (name n ∧ arg1 n = m ∧ arg2 n = lit "Dreadbury")
 ∧ ∀ s, (S s → ∃ l, (live l ∧ arg1 l = s ∧ arg2 l = m)))
 ∧ ∃ r, (∃ n, (name n ∧ arg1 n = r ∧ arg2 n = lit "Dreadbury")
 ∧ ∃ P, (P = (λ p => person p ∧ ∃ l, (live l ∧ arg1 l = p ∧ arg2 l = r))
 ∧ ∃ o, (only o ∧ arg1 o = uset S ∧ arg2 o = uset P))))
)

-- 3. A killer always hates his victim, and is never richer than his victim.
variable (h3 :
∃ K, (K = (λ k => (agent kill) k)
 ∧ ∀ k, (K k → ∀ v, ((victim v ∧ ∃ p, (possessive p ∧ arg1 p = k ∧ arg2 p = v))
 → (∃ h, (hate h ∧ arg1 h = k ∧ arg2 h = v)
    ∧ ¬ ∃ r, (greater wealth) r ∧ arg1 r = k ∧ arg2 r = v))))
)

-- 4. Charles hates no one that Aunt Agatha hates.
variable (h4 :
  ∃ c, (∃ n, name n ∧ arg1 n = c ∧ arg2 n = lit "Charles")
  ∧ ∃ a, (aunt a ∧ (∃ n, name n ∧ arg1 n = a ∧ arg2 n = lit "Agatha")
  ∧ ∃ S, (S = λ s => ∃ h, (hate h ∧ arg1 h = a ∧ arg2 h = s)
  ∧ ∀ s, (S s → ¬ ∃ h, (hate h ∧ arg1 h = c ∧ arg2 h = s))))
)

-- 5. Agatha hates everyone except the butler.
variable (h5 :
 ∃ a, (∃ n, (name n ∧ arg1 n = a ∧  arg2 n = lit "Agatha")
  ∧ ∃ B, ((B = λ b => butler b) ∧ size B = 1
  ∧ ∃ S, (S = λ s => (person s ∧ ¬ B s)
  ∧ ∀ s, (S s → ∃ h, (hate h ∧ arg1 h = a ∧ arg2 h = s)))))
)

-- 6. The butler hates everyone not richer than Aunt Agatha.
variable (h6 :
 ∃ B, (B = (λ b => butler b) ∧ size B = 1
  ∧ ∃ b, (B b ∧ ∃ a, (aunt a ∧ ∃ n, (name n ∧ arg1 n = a ∧ arg2 n = lit "Agatha")
  ∧ ∃ E, (E = λ e => (person e ∧ ¬ ∃ r, ((greater wealth) r ∧ arg1 r = e ∧ arg2 r = a))
  ∧ ∀ e, (E e → ∃ h, (hate h ∧ arg1 h = b ∧ arg2 h = e))))))
)

-- 7. The butler hates everyone Aunt Agatha hates.
variable (h7 :
  ∃ B, (B = (λ b => butler b) ∧ size B = 1
  ∧ ∃ b, (B b
  ∧ ∃ a, (aunt a ∧ (∃ n, name n ∧ arg1 n = a ∧ arg2 n = lit "Agatha")
  ∧ ∃ E, (E = (λ e => person e ∧ ∃ h, hate h ∧ arg1 h = a ∧ arg2 h = e)
  ∧ ∀ e, (E e → (∃ h, hate h ∧ arg1 h = b ∧ arg2 h = e))))))
)

-- 8. No one hates everyone.
variable (h8 :
  ∃ E, (E = (λ e => person e) ∧ ¬ ∃ p, (person p
  ∧ ∀ e, (E e → ∃ h, hate h ∧ arg1 h = p ∧ arg2 h = e)))
)

-- 9. Agatha is not the butler.
variable (h9 :
  ∃ a, (∃ n, (name n ∧ arg1 n = a ∧ arg2 n = lit "Agatha")
  ∧ ∃ B, B = (λ b => butler b) ∧ size B = 1
  ∧ ∃ b, (B b ∧ ¬ ∃ s, same s ∧ arg1 s = a ∧ arg2 s = b))
)

end Agatha
