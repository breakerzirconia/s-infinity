import Mathlib.Init.ZeroOne
import Std.Data.AssocList

inductive Sinf_term where
  | var : String → Sinf_term
  | O : Sinf_term
  | S : Sinf_term → Sinf_term
  | plus : Sinf_term → Sinf_term → Sinf_term
  | times : Sinf_term → Sinf_term → Sinf_term

prefix:max "_" => Sinf_term.var
postfix:75 "↗" => Sinf_term.S
infixl:65 " +ₛ " => Sinf_term.plus
infixl:70 " *ₛ " => Sinf_term.times

namespace Sinf_term

@[simp] def fromNat (n : Nat) : Sinf_term := match n with
  | Nat.zero => O
  | Nat.succ n => S (fromNat n)

@[simp] def eval : Sinf_term → Std.AssocList String Nat → Option Nat :=
  λ t al ↦ match t with
    | var x => Std.AssocList.find? x al
    | O => some 0
    | S θ => Nat.succ <$> eval θ al
    | plus θ₁ θ₂ => Nat.add <$> eval θ₁ al <*> eval θ₂ al
    | times θ₁ θ₂ => Nat.mul <$> eval θ₁ al <*> eval θ₂ al

#reduce eval (S O +ₛ _"x" *ₛ _"x") (Std.AssocList.cons "x" 21 Std.AssocList.nil)

@[simp] def subst : Sinf_term → String → Sinf_term → Sinf_term :=
  λ θ' x θ ↦ match θ' with
  | var x' => match String.decEq x x' with
    | isTrue _ => θ
    | isFalse _ => var x'
  | O => O
  | S θ' => S (subst θ' x θ)
  | plus θ₁ θ₂ => plus (subst θ₁ x θ) (subst θ₂ x θ)
  | times θ₁ θ₂ => times (subst θ₁ x θ) (subst θ₂ x θ)

end Sinf_term

instance : Coe Nat Sinf_term where
  coe := Sinf_term.fromNat

instance : Zero Sinf_term where
  zero := Sinf_term.O

instance : One Sinf_term where
  one := Sinf_term.S Sinf_term.O

instance : Add Sinf_term where
  add := Sinf_term.plus

instance : Mul Sinf_term where
  mul := Sinf_term.times

inductive NoVars : Sinf_term → Type where
  | O : NoVars Sinf_term.O
  | S : ∀ {t}, NoVars t → NoVars (t↗)
  | plus : ∀ {θ₁ θ₂}, NoVars θ₁ → NoVars θ₂ → NoVars (θ₁ +ₛ θ₂)
  | times : ∀ {θ₁ θ₂}, NoVars θ₁ → NoVars θ₂ → NoVars (θ₁ *ₛ θ₂)

namespace NoVars

theorem fromNat {n : Nat} : NoVars (Sinf_term.fromNat n) := by
  induction n <;> try constructor <;> assumption

theorem unique {θ : Sinf_term} (nv₁ nv₂ : NoVars θ) : nv₁ = nv₂ := by
  induction θ <;> try contradiction
  case O => cases nv₁; cases nv₂; rfl
  case S θ ih =>
    cases nv₁; case S nv₁ => cases nv₂; case S nv₂ =>
    apply congrArg; exact (ih nv₁ nv₂)
  case plus θ₁ θ₂ ih₁ ih₂ =>
    cases nv₁; case plus nv₁₁ nv₂₁ => cases nv₂; case plus nv₁₂ nv₂₂ =>
    apply congrArg₂; exact (ih₁ nv₁₁ nv₁₂); exact (ih₂ nv₂₁ nv₂₂)
  case times θ₁ θ₂ ih₁ ih₂ =>
    cases nv₁; case times nv₁₁ nv₂₁ => cases nv₂; case times nv₁₂ nv₂₂ =>
    apply congrArg₂; exact (ih₁ nv₁₁ nv₁₂); exact (ih₂ nv₂₁ nv₂₂)

end NoVars

inductive Sinf_const where
  | O : Sinf_const
  | S : Sinf_const → Sinf_const
  | plus : Sinf_const → Sinf_const → Sinf_const
  | times : Sinf_const → Sinf_const → Sinf_const

postfix:75 "↗ᶜ" => Sinf_const.S
infixl:65 " +ᶜ " => Sinf_const.plus
infixl:70 " *ᶜ " => Sinf_const.times

namespace Sinf_const

@[simp] def fromNat (n : Nat) : Sinf_const := match n with
  | Nat.zero => O
  | Nat.succ n => S (fromNat n)

@[simp] def eval : Sinf_const → Nat :=
  λ t ↦ match t with
    | O => 0
    | S θ => Nat.succ $ eval θ
    | plus θ₁ θ₂ => Nat.add (eval θ₁) (eval θ₂)
    | times θ₁ θ₂ => Nat.mul (eval θ₁) (eval θ₂)

@[simp] def coerce (θ : Sinf_term) (nv : NoVars θ) : Sinf_const :=
  match nv with
  | NoVars.O => Sinf_const.O
  | @NoVars.S θ' nv => Sinf_const.S (coerce θ' nv)
  | @NoVars.plus θ₁' θ₂' nv₁ nv₂ => Sinf_const.plus (coerce θ₁' nv₁) (coerce θ₂' nv₂)
  | @NoVars.times θ₁' θ₂' nv₁ nv₂ => Sinf_const.times (coerce θ₁' nv₁) (coerce θ₂' nv₂)

#reduce eval (S (S O) +ᶜ S (S (S O) *ᶜ S (S (S O))))
#reduce coerce (Sinf_term.plus (Sinf_term.S Sinf_term.O) Sinf_term.O) (NoVars.plus (NoVars.S NoVars.O) NoVars.O)

end Sinf_const

instance : Coe Nat Sinf_const where
  coe := Sinf_const.fromNat

instance : Zero Sinf_const where
  zero := Sinf_const.O

instance : One Sinf_const where
  one := Sinf_const.S Sinf_const.O

instance : Add Sinf_const where
  add := Sinf_const.plus

instance : Mul Sinf_const where
  mul := Sinf_const.times

inductive Sinf : Type where
  | S_eq : Sinf_term → Sinf_term → Sinf
  | S_neg : Sinf → Sinf
  | S_or : Sinf → Sinf → Sinf
  | S_forall : String → Sinf → Sinf

infix:50 " =ₛ " => Sinf.S_eq
notation:max "¬ₛ " α:40 => Sinf.S_neg α
infixl:30 " ∨ₛ " => Sinf.S_or
notation:28 "∀ₛ " x " ; " α:28 => Sinf.S_forall x α

namespace Sinf

@[simp] def subst : Sinf → String → Sinf_term → Sinf :=
  λ α x θ ↦ match α with
    | S_eq θ₁ θ₂ => S_eq (Sinf_term.subst θ₁ x θ) (Sinf_term.subst θ₂ x θ)
    | S_neg α => S_neg (subst α x θ)
    | S_or α β => S_or (subst α x θ) (subst β x θ)
    | S_forall x' α => match String.decEq x x' with
      | isTrue _ => S_forall x' α
      | isFalse _ => S_forall x' (subst α x θ)

end Sinf

notation:45 α " [" x " ≔ " θ "]" => Sinf.subst α x θ

open Sinf_term

#reduce Sinf.subst (¬ₛ _"x"↗↗↗↗ =ₛ O↗↗) "x" (O +ₛ O↗)
