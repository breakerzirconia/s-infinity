import Mathlib.Init.ZeroOne
import Std.Data.AssocList

import SInfinity.Basic
import SInfinity.Util

notation:max "Ø" => List.nil
-- infixl:25 " ∨ᶜ " => λ ss s ↦ List.cons s ss

inductive NoVars : Sinf_term → Prop where
  | NV_zero : NoVars O
  | NV_succ : ∀ {t}, NoVars t → NoVars (S t)
  | NV_plus : ∀ {θ₁ θ₂}, NoVars θ₁ → NoVars θ₂ → NoVars (θ₁ +ₛ θ₂)
  | NV_times : ∀ {θ₁ θ₂}, NoVars θ₁ → NoVars θ₂ → NoVars (θ₁ *ₛ θ₂)

namespace NoVars

theorem fromNat {n : Nat} : NoVars (Sinf_term.fromNat n) := by
  induction n <;> simp <;> constructor

end NoVars

inductive Sinf_proof : List Sinf → Sinf → Prop where
  | S_axiom : ∀ {θ₁ θ₂ Γ},
              NoVars θ₁ →
              NoVars θ₂ →
              Sinf_term.eval θ₁ Std.AssocList.nil = Sinf_term.eval θ₂ Std.AssocList.nil →
              Sinf_proof Γ (θ₁ =ₛ θ₂)
  | S_axiom_neg : ∀ {θ₁ θ₂ Γ},
                  NoVars θ₁ →
                  NoVars θ₂ →
                  Sinf_term.eval θ₁ Std.AssocList.nil ≠ Sinf_term.eval θ₂ Std.AssocList.nil →
                  Sinf_proof Γ (¬ₛ θ₁ =ₛ θ₂)

  | S_inr : ∀ α {β Γ},
            Sinf_proof Γ β →
            Sinf_proof Γ (α ∨ₛ β)
  | S_de_morgan : ∀ {α β Γ},
                  Sinf_proof Γ (¬ₛ α) →
                  Sinf_proof Γ (¬ₛ β) →
                  Sinf_proof Γ (¬ₛ (α ∨ₛ β))
  | S_dni : ∀ {α Γ},
            Sinf_proof Γ α →
            Sinf_proof Γ (¬ₛ ¬ₛ α)
  | S_neg_forall : ∀ {α x θ Γ},
                   Sinf_proof Γ (¬ₛ α [x ≔ θ]) →
                   Sinf_proof Γ (¬ₛ (∀ₛ x ; α))

  | S_induction : ∀ {α x Γ},
                  (∀ n : Nat, Sinf_proof Γ (α [x ≔ n])) →
                  Sinf_proof Γ (∀ₛ x ; α)
  | S_section : ∀ {ζ} α {δ} {Γ},
                Sinf_proof Γ (ζ ∨ₛ α) →
                Sinf_proof Γ (¬ₛ α ∨ₛ δ) →
                Sinf_proof Γ (ζ ∨ₛ δ)

axiom S_out : ∀ {α γ Γ},
              Sinf_proof (γ :: Γ) α →
              Sinf_proof Γ (γ ∨ₛ α)
axiom S_in : ∀ {α γ Γ},
             Sinf_proof Γ (γ ∨ₛ α) →
             Sinf_proof (γ :: Γ) α
axiom S_exchange_ctx : ∀ {α γ Γ},
                       Sinf_proof (γ :: Γ) α →
                       Sinf_proof (α :: Γ) γ
axiom S_contraction_ctx : ∀ {α Γ},
                          Sinf_proof (α :: Γ) α →
                          Sinf_proof Γ α

notation:25 ctx:25 " ⊢ₛ " α:28 => Sinf_proof ctx α
