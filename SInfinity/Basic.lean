import Mathlib.Init.ZeroOne
import Std.Data.AssocList

inductive Sinf_term where
  | S_var : String → Sinf_term
  | O : Sinf_term
  | S : Sinf_term → Sinf_term
  | S_plus : Sinf_term → Sinf_term → Sinf_term
  | S_times : Sinf_term → Sinf_term → Sinf_term

prefix:max "_" => Sinf_term.S_var
prefix:max "S " => Sinf_term.S
infixl:65 " +ₛ " => Sinf_term.S_plus
infixl:70 " *ₛ " => Sinf_term.S_times

namespace Sinf_term

@[simp] def fromNat (n : Nat) : Sinf_term := match n with
  | Nat.zero => O
  | Nat.succ n => S (fromNat n)

@[simp] def eval : Sinf_term → Std.AssocList String Nat → Option Nat :=
  λ t al ↦ match t with
    | S_var x => Std.AssocList.find? x al
    | O => some 0
    | S θ => Nat.succ <$> eval θ al
    | S_plus θ₁ θ₂ => Nat.add <$> eval θ₁ al <*> eval θ₂ al
    | S_times θ₁ θ₂ => Nat.mul <$> eval θ₁ al <*> eval θ₂ al

#reduce eval (S O +ₛ _"x" *ₛ _"x") (Std.AssocList.cons "x" 21 Std.AssocList.nil)

@[simp] def subst : Sinf_term → String → Sinf_term → Sinf_term :=
  λ θ' x θ ↦ match θ' with
  | S_var x' => match String.decEq x x' with
    | isTrue _ => θ
    | isFalse _ => S_var x'
  | O => O
  | S θ' => S (subst θ' x θ)
  | S_plus θ₁ θ₂ => S_plus (subst θ₁ x θ) (subst θ₂ x θ)
  | S_times θ₁ θ₂ => S_times (subst θ₁ x θ) (subst θ₂ x θ)

end Sinf_term

instance : Coe Nat Sinf_term where
  coe := Sinf_term.fromNat

instance : Zero Sinf_term where
  zero := Sinf_term.O

instance : One Sinf_term where
  one := Sinf_term.S Sinf_term.O

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

notation:45 α "[" x " ≔ " θ "]" => Sinf.subst α x θ

open Sinf_term

#reduce Sinf.subst (¬ₛ S S S S _"x" =ₛ S S O) "x" (O +ₛ S O)
