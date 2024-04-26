import «Puzzles»

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"



section TestPlur

variable (u x : Type)
variable (live : u → Prop)
variable (live₁ : Set u → Prop)
variable (live₂ : (u → Prop) → Prop)

def plur {u : Type} (p : u → Prop) : Set u → Prop :=
λ x => ∀ y, p y → x y

#check live
#check (plur live)
#check ∀ (a : Set u), (plur live) a
#check ∀ (a : u), live a


end TestPlur


section MTT

-- continuos corrosion prevented contact

variable (corrosion contact : Type)
variable (continous : contact → Type)
variable (prevent : corrosion → contact → Type)

#check Σ z : (Σ x : contact, (Σ y : corrosion, prevent y x)), continous z.1

end MTT
