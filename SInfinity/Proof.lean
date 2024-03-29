import Mathlib.Init.ZeroOne
import Std.Data.AssocList

import SInfinity.Basic
import SInfinity.Util

def Ctx := List

notation:max "Ø" => List.nil
-- infixl:25 " ∨ᶜ " => λ ss s ↦ List.cons s ss

inductive Sinf_proof : Ctx Sinf → Sinf → Prop where
  | S_axiom : ∀ {θ₁ θ₂ Δ},
              ∀ (nv₁ : NoVars θ₁) (nv₂ : NoVars θ₂),
              Sinf_const.eval (Sinf_const.coerce θ₁ nv₁) = Sinf_const.eval (Sinf_const.coerce θ₂ nv₂) →
              Sinf_proof Δ (θ₁ =ₛ θ₂)
  | S_axiom_neg : ∀ {θ₁ θ₂ Δ},
                  ∀ (nv₁ : NoVars θ₁) (nv₂ : NoVars θ₂),
                  Sinf_const.eval (Sinf_const.coerce θ₁ nv₁) ≠ Sinf_const.eval (Sinf_const.coerce θ₂ nv₂) →
                  Sinf_proof Δ (¬ₛ θ₁ =ₛ θ₂)

  | S_weakening : ∀ α {δ Δ},
                  Sinf_proof Δ δ →
                  Sinf_proof (δ :: Δ) α
  | S_de_morgan : ∀ {α β Δ},
                  Sinf_proof Δ (¬ₛ α) →
                  Sinf_proof Δ (¬ₛ β) →
                  Sinf_proof Δ (¬ₛ (α ∨ₛ β))
  | S_dni : ∀ {α Δ},
            Sinf_proof Δ α →
            Sinf_proof Δ (¬ₛ ¬ₛ α)
  | S_neg_forall : ∀ {α x θ Δ},
                   Sinf_proof Δ (¬ₛ α [x ≔ θ]) →
                   Sinf_proof Δ (¬ₛ (∀ₛ x ; α))

  | S_induction : ∀ {α x Δ},
                  (∀ n : Nat, Sinf_proof Δ (α [x ≔ n])) →
                  Sinf_proof Δ (∀ₛ x ; α)
  | S_section : ∀ {ζ} α {δ} {Δ},
                Sinf_proof Δ (ζ ∨ₛ α) →
                Sinf_proof Δ (¬ₛ α ∨ₛ δ) →
                Sinf_proof Δ (ζ ∨ₛ δ)

axiom S_join : ∀ {α δ₁ δ₂ Δ},
               Sinf_proof (δ₂ :: δ₁ :: Δ) α →
               Sinf_proof ((δ₁ ∨ₛ δ₂) :: Δ) α
axiom S_split : ∀ {α δ₁ δ₂ Δ},
                Sinf_proof ((δ₁ ∨ₛ δ₂) :: Δ) α →
                Sinf_proof (δ₂ :: δ₁ :: Δ) α

axiom S_out : ∀ {α δ Δ},
              Sinf_proof (δ :: Δ) α →
              Sinf_proof Δ (δ ∨ₛ α)
axiom S_in : ∀ {α δ Δ},
             Sinf_proof Δ (δ ∨ₛ α) →
             Sinf_proof (δ :: Δ) α

axiom S_exchange_ctx : ∀ {α δ Δ},
                       Sinf_proof (δ :: Δ) α →
                       Sinf_proof (α :: Δ) δ
axiom S_contraction_ctx : ∀ {α Δ},
                          Sinf_proof (α :: Δ) α →
                          Sinf_proof Δ α

notation:25 ctx:25 " ⋁ " α:28 => Sinf_proof ctx α
