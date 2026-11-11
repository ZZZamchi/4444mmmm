import ExperimentsMathlib.CanonV4

-- names swapped: the candidate's `n` plays the reference's `m`
#canon4_goals "swap" "" (∀ m n : Nat, n > 0 → m % n < n) (∀ n m : Nat, 0 < m → n % m < m)
#canon4_goals "swap_perm" "align" (∀ m n : Nat, n > 0 → m % n < n) (∀ n m : Nat, 0 < m → n % m < m)
#canon4_goals "swap_anon" "anon" (∀ m n : Nat, n > 0 → m % n < n) (∀ n m : Nat, 0 < m → n % m < m)
#canon4_goals "swap_perm_anon" "align,anon" (∀ m n : Nat, n > 0 → m % n < n) (∀ n m : Nat, 0 < m → n % m < m)

-- a genuine error: the hypothesis is on the wrong variable; no bijection repairs it
#canon4_goals "wrong_perm" "align" (∀ m n : Nat, n > 0 → m % n < n) (∀ m n : Nat, m > 0 → m % n < n)

-- the conclusion of the candidate binds a variable the reference does not
#canon4_goals "trail" "" (∀ (f g : Nat → Nat), (∀ x, f x = g x) → f = g)
  (∀ (f g : Nat → Nat), (∀ x, f x = g x) → ∀ y, f y = g y)

-- `Type` against `Type*`: only `univ0m` aligns them
universe u
#canon4_goals "univ" "univ0m" (∀ (α : Type) (f : α → α), f = f) (∀ (β : Type u) (g : β → β), g = g)
#canon4_goals "univ_same" "univ0m" (∀ (α : Type u) (f : α → α), f = f) (∀ (β : Type u) (g : β → β), g = g)

-- shuffled and renamed: the greedy alignment pairs by position, `align` recovers the pairing
#canon4_goals "shuf" "anon,shuffle" (∀ m n : Nat, n > 0 → m % n < n) (∀ m n : Nat, n > 0 → m % n < n)
#canon4_goals "shuf_perm" "align,anon,shuffle" (∀ m n : Nat, n > 0 → m % n < n) (∀ m n : Nat, n > 0 → m % n < n)

-- a dependent run: after the shuffle the greedy alignment maps `X ↦ β`, and `f` no longer matches
#canon4_goals "dep" "anon,shuffle" (∀ (α β : Type) (f : α → β), Function.Injective f → f = f)
  (∀ (X Y : Type) (f : X → Y), Function.Injective f → f = f)
#canon4_goals "dep_align" "align,anon,shuffle" (∀ (α β : Type) (f : α → β), Function.Injective f → f = f)
  (∀ (X Y : Type) (f : X → Y), Function.Injective f → f = f)

canon4_prove "align" swap_acc (∀ m n : Nat, n > 0 → m % n < n) (∀ n m : Nat, 0 < m → n % m < m) acc :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩
