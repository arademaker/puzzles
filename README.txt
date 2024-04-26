
Puzzle 1 = Agatha

https://tptp.org/cgi-bin/SeeTPTP?Category=Problems&Domain=PUZ&File=PUZ001+1.p

See Basic.lean

1. Someone who lives in Dreadbury Mansion killed Aunt Agatha.
2. Agatha, the butler, and Charles live in Dreadbury Mansion, and are the only people who live therein.
3. A killer always hates his victim, and is never richer than his victim.
4. Charles hates no one that Aunt Agatha hates.
5. Agatha hates everyone except the butler.
6. The butler hates everyone not richer than Aunt Agatha.
7. The butler hates everyone Aunt Agatha hates.
8. No one hates everyone.
9. Agatha is not the butler.
---
Agatha killed herself.


The agatha profile:

delphin mkprof --input agatha.txt --relations ~/r/lkb-src/src/tsdb/skeletons/english/Relations --skeleton agatha
delphin process agatha -g ../erg.dat --full-forest --options='--disable-generalization'


Axioms obtained from the profile gold analyses dropping u and i vars:

% python agatha.py

ax1 ≔ ∃ x29, _aunt_n_of x29 ∧ (∃ x10, (∃ x16, Dreadbury = x16 ∧ (∃ e15, compound e15 x10 x16 ∧ Mansion = x10))
   ∧ (∃ x23, (∃ e28, compound e28 x23 x29 ∧ Agatha = x23) ∧ (∃ x3, (∃ e8 e9, person x3 ∧ _live_v_1 e8 x3 ∧ _in_p_state e9 e8 x10)
   ∧ (∃ e2, _kill_v_1 e2 x3 x23))))

ax2 ≔ ∃ x32, (∃ x38, Dreadbury = x38 ∧ (∃ e37, compound e37 x32 x38 ∧ Mansion = x32))
 ∧ (∃ x14, (∃ x24, Charles = x24 ∧ (∃ x19, _butler_n_1 x19 ∧ _and_c x14 x19 x24))
 ∧ (∃ x46, (∃ e51 e53 e54, _only_a_1 e51 x46 ∧ _people_n_of x46 ∧ _live_v_1 e53 x46 ∧ _therein_p_state e54 e53)
 ∧ (∃ x3, (∃ x8, Agatha = x8 ∧ implicit_conj x3 x8 x14) ∧ (∃ e30 e31 e2 e45, _live_v_1 e30 x3 ∧ _in_p_state e31 e30 x32
 ∧ _and_c e2 e30 e45 ∧ _be_v_id e45 x3 x46))))

ax3 ≔ ∃ e2 e22 e9 x10, (∃ x16, pron x16 ∧ (∃ e15, poss e15 x10 x16 ∧ _victim_n_of x10))
 ∧ (∃ x34, pron x34 ∧ (∃ x3, _killer_n_1 x3 ∧ (∃ e22, _always_a_1 e9 ∧ _hate_v_1 e9 x3 x10
 ∧ _and_c e2 e9 e22 ∧ _never_a_1 e22 (∃ x28, (∃ e9 e9 e2 e33, poss e33 x28 x34 ∧ _victim_n_of x28)
 ∧ (∃ e25 e27, _rich_a_in e25 x3 ∧ more_comp e27 e25 x28)))))

ax4 ≔ ∃ x20, _aunt_n_of x20 ∧ (∀ x9, (∃ x15, (∃ e19, compound e19 x15 x20 ∧ Agatha = x15)
 ∧ (∃ e27, person x9 ∧ _hate_v_1 e27 x15 x9)) → ¬(∃ x3, Charles = x3 ∧ (∃ e2, _hate_v_1 e2 x3 x9)))

ax5 ≔ ∀ x9, (∃ x15, _butler_n_1 x15 ∧ (∃ e14, person x9 ∧ _except_p e14 x9 x15)) → (∃ x3, Agatha = x3 ∧ (∃ e2, _hate_v_1 e2 x3 x9))

ax6 ≔ ∀ x8, person x8 ∧ ¬(∃ x19, (∃ x25, _aunt_n_of x25 ∧ (∃ e24, compound e24 x19 x25 ∧ Agatha = x19))
 ∧ (∃ e16 e18, _rich_a_in e16 x8 ∧ more_comp e18 e16 x19)) → (∃ x3, _butler_n_1 x3 ∧ (∃ e2, _hate_v_1 e2 x3 x8))

ax7 ≔ ∀ x8, (∃ x19, _aunt_n_of x19 ∧ (∃ x14, (∃ e18, compound e18 x14 x19 ∧ Agatha = x14)
 ∧ (∃ e26, person x8 ∧ _hate_v_1 e26 x14 x8))) → (∃ x3, _butler_n_1 x3 ∧ (∃ e2, _hate_v_1 e2 x3 x8))

ax8 ≔ ∀ x8, person x8 → (∀ x3, person x3 → ¬(∃ e2, _hate_v_1 e2 x3 x8))

ax9 ≔ ¬(∃ x10, _butler_n_1 x10 ∧ (∃ x3, Agatha = x3 ∧ (∃ e2, _be_v_id e2 x3 x10)))

I could not prove

	 (∃ x9, pron x9 ∧ (∃ x3, Agatha = x3 ∧ (∃ e2, _kill_v_1 e2 x3 x9))) 


Axioms obtained from the gold profile analyses with i and u vars:

% python agatha.py

ax1 ≔ ∃ i34 x29, _aunt_n_of x29 i34 ∧ (∃ x10, (∃ x16, Dreadbury = x16 ∧ (∃ e15, compound e15 x10 x16 ∧ Mansion = x10))
 ∧ (∃ x23, (∃ e28, compound e28 x23 x29 ∧ Agatha = x23) ∧ (∃ x3, (∃ e8 e9, person x3 ∧ _live_v_1 e8 x3 ∧ _in_p_state e9 e8 x10)
 ∧ (∃ e2, _kill_v_1 e2 x3 x23))))

ax2 ≔ ∃ i52 x32, (∃ x38, Dreadbury = x38 ∧ (∃ e37, compound e37 x32 x38 ∧ Mansion = x32))
 ∧ (∃ x14, (∃ x24, Charles = x24 ∧ (∃ x19, _butler_n_1 x19 ∧ _and_c x14 x19 x24))
 ∧ (∃ x46, (∃ e51 e53 e54, _only_a_1 e51 x46 ∧ _people_n_of x46 i52 ∧ _live_v_1 e53 x46 ∧ _therein_p_state e54 e53)
 ∧ (∃ x3, (∃ x8, Agatha = x8 ∧ implicit_conj x3 x8 x14) ∧ (∃ e30 e31 e2 e45, _live_v_1 e30 x3
 ∧ _in_p_state e31 e30 x32 ∧ _and_c e2 e30 e45 ∧ _be_v_id e45 x3 x46))))

ax3 ≔ ∃ e2 e22 e9 i21 i39 i8 u26 x10, (∃ x16, pron x16 ∧ (∃ e15, poss e15 x10 x16 ∧ _victim_n_of x10 i21))
 ∧ (∃ x34, pron x34 ∧ (∃ x3, _killer_n_1 x3 ∧ (∃ e22, _always_a_1 i8 e9 ∧ _hate_v_1 e9 x3 x10
 ∧ _and_c e2 e9 e22 ∧ _never_a_1 e22 (∃ x28, (∃ e9 e2 e33, poss e33 x28 x34 ∧ _victim_n_of x28 i39)
 ∧ (∃ e25 e27, _rich_a_in e25 x3 u26 ∧ more_comp e27 e25 x28)))))

ax4 ≔ ∃ i25 x20, _aunt_n_of x20 i25 ∧ (∀ x9, (∃ x15, (∃ e19, compound e19 x15 x20 ∧ Agatha = x15)
 ∧ (∃ e27, person x9 ∧ _hate_v_1 e27 x15 x9)) → ¬(∃ x3, Charles = x3 ∧ (∃ e2, _hate_v_1 e2 x3 x9)))

ax5 ≔ ∀ x9, (∃ x15, _butler_n_1 x15 ∧ (∃ e14, person x9 ∧ _except_p e14 x9 x15)) → (∃ x3, Agatha = x3 ∧ (∃ e2, _hate_v_1 e2 x3 x9))

ax6 ≔ ∃ i30 u17, ∀ x8, person x8 ∧ ¬(∃ x19, (∃ x25, _aunt_n_of x25 i30 ∧ (∃ e24, compound e24 x19 x25 ∧ Agatha = x19))
 ∧ (∃ e16 e18, _rich_a_in e16 x8 u17 ∧ more_comp e18 e16 x19)) → (∃ x3, _butler_n_1 x3 ∧ (∃ e2, _hate_v_1 e2 x3 x8))

ax7 ≔ ∃ i24, ∀ x8, (∃ x19, _aunt_n_of x19 i24 ∧ (∃ x14, (∃ e18, compound e18 x14 x19 ∧ Agatha = x14)
 ∧ (∃ e26, person x8 ∧ _hate_v_1 e26 x14 x8))) → (∃ x3, _butler_n_1 x3 ∧ (∃ e2, _hate_v_1 e2 x3 x8))

ax8 ≔ ∀ x8, person x8 → (∀ x3, person x3 → ¬(∃ e2, _hate_v_1 e2 x3 x8))

ax9 ≔ ¬(∃ x10, _butler_n_1 x10 ∧ (∃ x3, Agatha = x3 ∧ (∃ e2, _be_v_id e2 x3 x10)))

I could not prove
	 (∃ x9, pron x9 ∧ (∃ x3, Agatha = x3 ∧ (∃ e2, _kill_v_1 e2 x3 x9))) 
