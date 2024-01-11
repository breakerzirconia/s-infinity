import Mathlib.Init.Function

theorem String.decEq_refl (s : String) : String.decEq s s = isTrue rfl := by
  cases String.decEq s s <;> try contradiction
  simp

open Function

theorem Option.map_inj {A B : Type} (f : A → B) (inj : Injective f) {x y : Option A} :
  Option.map f x = Option.map f y → x = y := by
  intros p
  induction x <;> induction y <;> try trivial
  case some.some v v' =>
    have obvs : ∀ a, Option.map f (some a) = some (f a) := by intros a; rfl
    rw [obvs v, obvs v'] at p
    rw [Option.some_inj] at p
    apply congrArg; apply inj; assumption
