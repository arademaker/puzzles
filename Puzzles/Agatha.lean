
section Agatha

opaque u : Type

opaque aunt : u → Prop
opaque animate : u → Prop
opaque name : u → Prop
opaque hate : u → Prop
opaque butler : u → Prop
opaque same : u → Prop
opaque size : (u → Prop) → Nat
opaque kill : u → Prop

opaque agent : (u → Prop) → u

variable (charles : u)
variable (arg1 arg2 : u → u)
variable (lit : String → u)


-- 2. A killer always hates his victim, and is never richer than his victim
/-
variable (h2 :
 ∃ K, K = (λ k => (agent kill) k))

?[K]:(K=^[k]:agent(kill)(k)
	& ![k]:(K(k) => ?[v]:(victim(v) & ?[p]:(possessive(p) & arg1(p)=k & arg2(p)=v)
		& ?[h]:(hate(h) & arg1(h)=k & arg2(h)=v) & ~?[r]:(greater(wealth)(r) & arg1(r)=k & arg2(r)=v))
	)
);
-/

-- 4. Charles hates no one that Aunt Agatha hates.

variable (h4 :
  ∃ c, c = charles ∧
  ∃ a, aunt a ∧
  (∃ n, name n ∧ arg1 n = a ∧ arg2 n = lit "Agatha") ∧
  (∃ S, S = (λ s => ∃ h, hate h ∧ arg1 h = a ∧ arg2 h = s)
   ∧ (∀ s, S s → ¬∃ h, hate h ∧ arg1 h = c ∧ arg2 h = s)))

-- 7. The butler hates everyone Aunt Agatha hates.

variable (h7 :
  ∃ B, (B = (λ b => butler b ∧ size B = 1 ∧
  ∃ b, (B b ∧ ∃ a,
  (aunt a ∧ ∃ n , (name n ∧ arg1 n = a ∧ arg2 n = lit "Agatha")
  ∧ ∃ E, (E = λ e => (animate e ∧ ∃ h, (hate h ∧ arg1 h = a ∧ arg2 h = e))
  ∧ ∀ e, (E e → ∃ h, (hate h ∧ arg1 h = b ∧ arg2 h = e))))))))


-- 8. No one hates everyone.

variable (h8 :
  ¬ ∃ E, E = (λ e => animate e) ∧ ¬ ∃ p, animate p ∧
    ∀ e, E e → ∃ h, hate h ∧ arg1 h = p ∧ arg2 h = e)


-- 9. Agatha is not the butler.

variable (h9 :
  ∃ a, (∃ n, name n ∧ arg1 n = a ∧ arg2 n = lit "Agatha")
  ∧ ∃ B, B = (λ b => butler b) ∧ size B = 1
  ∧ ∃ b, (B b ∧ ¬ ∃ s, same s ∧ arg1 s = a ∧ arg2 s = b))


end Agatha
