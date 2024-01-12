import Std.Data.Nat.Lemmas

import SInfinity.Proof

namespace Sinf_term

theorem succ_inj {θ₁ θ₂ : Sinf_term} : θ₁↗ = θ₂↗ → θ₁ = θ₂ := by
  induction θ₁ <;> induction θ₂ <;> simp at *

end Sinf_term

open Sinf_proof

theorem S_exchange : ∀ {α β Δ},
                     Δ ⋁ α ∨ₛ β →
                     Δ ⋁ β ∨ₛ α := by
  intros α β Δ αβ
  apply S_out; apply S_exchange_ctx; apply S_in; assumption

theorem S_assoc : ∀ {α β γ Δ},
                     Δ ⋁ α ∨ₛ β ∨ₛ γ ↔
                     Δ ⋁ α ∨ₛ (β ∨ₛ γ) := by
  intros α β γ Δ
  constructor <;> intros h
  · apply S_out; apply S_out; apply S_split; apply S_in; assumption
  · apply S_out; apply S_join; apply S_in; apply S_in; assumption

theorem S_contraction : ∀ {α Δ},
                     Δ ⋁ α ∨ₛ α →
                     Δ ⋁ α := by
  intros α Δ αα
  apply S_contraction_ctx; apply S_in; assumption

theorem S_inr : ∀ α {β} {Δ},
                Sinf_proof Δ β →
                Sinf_proof Δ (α ∨ₛ β) := by
  intros α β Δ b
  apply S_exchange
  apply S_out
  apply S_weakening
  assumption

theorem S_inl : ∀ {α} β {Δ},
                Sinf_proof Δ α →
                Sinf_proof Δ (α ∨ₛ β) := by
  intros α β Δ a
  apply S_exchange; exact (S_inr β a)

theorem S_duplicate : ∀ {α Δ},
                      Δ ⋁ α →
                      Δ ⋁ α ∨ₛ α := λ {α} ↦ S_inr α


theorem S_dne : ∀ {α Δ},
                Δ ⋁ ¬ₛ ¬ₛ α →
                Δ ⋁ α := by
  intros α Δ dn
  cases dn
  case S_weakening ne => exact (S_weakening α ne)
  case S_dni β => exact β

theorem S_de_morgan_inv : ∀ {α β Δ},
                          Δ ⋁ ¬ₛ (α ∨ₛ β) →
                          (Δ ⋁ (¬ₛ α)) ∧
                          (Δ ⋁ (¬ₛ β)) := by
  intros α β Δ d
  cases d
  case S_weakening ne => exact And.intro (S_weakening (¬ₛ α) ne) (S_weakening (¬ₛ β) ne)
  case S_de_morgan nα nβ => exact And.intro nα nβ

theorem S_neg_forall_inv : ∀ {α x Δ},
                           Δ ⋁ (¬ₛ (∀ₛ x ; α)) →
                           (∃ θ, Δ ⋁ (¬ₛ α [x ≔ θ])) := by
  intros α x Δ nf
  cases nf
  case S_weakening ne => exists (_ x); exact (S_weakening (¬ₛ α[x ≔ _ x]) ne)
  case S_neg_forall θ β => exists θ -- exact Exists.intro θ β

theorem S_induction_inv : ∀ {α x Δ},
                          Δ ⋁ ∀ₛ x ; α →
                          ∀ n : Nat, Δ ⋁ α [x ≔ n] := by
  intros α x Δ f
  cases f
  case S_weakening ne => intros n; exact (S_weakening (α [x ≔ n]) ne)
  case S_induction i => assumption

namespace Sinf

open Sinf_term

theorem eq_trans : ∀ {θ₁} θ₂ {θ₃ Δ},
                   Δ ⋁ θ₁ =ₛ θ₂ →
                   Δ ⋁ θ₂ =ₛ θ₃ →
                   Δ ⋁ θ₁ =ₛ θ₃ := by
  intros θ₁ θ₂ θ₃ Δ _12 _23
  cases _12
  case S_axiom nv₁ nv₂ e =>
    cases _23
    case S_axiom nv₂' nv₃ e' =>
      constructor <;> try assumption
      rw [NoVars.unique nv₂ nv₂'] at e
      exact (Eq.trans e e')
    case S_weakening ne => exact (S_weakening (θ₁ =ₛ θ₃) ne)
  case S_weakening ne => exact (S_weakening (θ₁ =ₛ θ₃) ne)

theorem succ_cong : ∀ {θ₁ θ₂ Δ},
                    Δ ⋁ θ₁ =ₛ θ₂ →
                    Δ ⋁ θ₁↗ =ₛ θ₂↗ := by
  intros θ₁ θ₂ Δ _12
  cases _12
  case S_axiom nv₁ nv₂ e =>
    constructor <;> try constructor <;> try assumption
    simp at *
    assumption
  case S_weakening ne => exact (S_weakening (θ₁↗ =ₛ θ₂↗) ne)

theorem succ_inj : ∀ {θ₁ θ₂ Δ},
                   Δ ⋁ θ₁↗ =ₛ θ₂↗ →
                   Δ ⋁ θ₁ =ₛ θ₂ := by
  intros θ₁ θ₂ Δ _12
  cases _12
  case S_axiom nv₁ nv₂ e =>
    cases nv₁; cases nv₂; constructor <;> try assumption
    simp at e
    assumption
  case S_weakening ne => exact (S_weakening (θ₁ =ₛ θ₂) ne)

theorem consistent : ∃ α, ¬ (Ø ⋁ α) := by
  exists (¬ₛ O =ₛ O)
  intros p
  cases p
  case S_axiom_neg nv₁ nv₂ p =>
    rw [NoVars.unique nv₁ nv₂] at p
    exact p rfl

theorem contradiction_yields_anything : ∀ {α β Δ},
                                        Δ ⋁ ¬ₛ (α ∨ₛ ¬ₛ α) →
                                        Δ ⋁ β := by
  intros α β Δ contr
  have iβ := S_inr β contr
  have s_return := S_in iβ
  cases S_de_morgan_inv s_return
  case intro n nn =>
    apply S_contraction
    apply S_section (¬ₛ α)
    · apply S_out; assumption
    · apply S_out; apply S_exchange_ctx; assumption

theorem var_refl : Ø ⋁ (∀ₛ a ; _ a =ₛ _ a) := by
  apply S_induction; intros n
  constructor <;> simp <;> try rw [String.decEq_refl a] <;> apply NoVars.fromNat
  rfl

theorem refl {θ} (nv : NoVars θ) : Ø ⋁ θ =ₛ θ := by
  induction nv
  case O => constructor <;> try constructor
  case S nv =>
    rcases nv with ⟨nv₁, nv₂, e⟩
    constructor <;> try constructor
    assumption
  case plus nv₁ nv₂ =>
    rcases nv₁ with ⟨nv₁₁, nv₁₂, e₁⟩
    rcases nv₂ with ⟨nv₂₁, nv₂₂, e₂⟩
    constructor <;> try constructor <;> try assumption
  case times nv₁ nv₂ =>
    rcases nv₁ with ⟨nv₁₁, nv₁₂, e₁⟩
    rcases nv₂ with ⟨nv₂₁, nv₂₂, e₂⟩
    constructor <;> try constructor <;> try assumption

theorem plus_comm : Ø ⋁ ∀ₛ a ; ∀ₛ b ; _ a +ₛ _ b =ₛ _ b +ₛ _ a := by
  apply S_induction; intros n; simp
  cases (String.decEq a b)
  case a.isFalse nab =>
    simp
    rw [String.decEq_refl a]; simp
    apply S_induction; intros m; simp
    rw [String.decEq_refl b]; simp
    induction n <;> induction m <;> simp at *
    case a.zero.zero =>
      constructor <;> constructor <;> constructor
    case a.zero.succ n ih =>
      rcases ih with ⟨⟨⟩, ⟨⟩, e⟩
      constructor <;> try constructor <;> try constructor <;> try assumption
      simp at *
    case a.succ.zero n ih =>
      rcases ih with ⟨⟨⟩, ⟨⟩, e⟩
      constructor <;> try constructor <;> try constructor <;> try assumption
      simp at *
    case a.succ.succ n m ihn ihm =>
      sorry
  case a.isTrue ab =>
    simp; rw [ab]
    apply S_induction; simp
    rw [String.decEq_refl b]; simp
    intros n; constructor <;> constructor <;> apply NoVars.fromNat

theorem succ_ne_zero : Ø ⋁ ∀ₛ a ; ¬ₛ (_ a ↗ =ₛ O) := by
  apply S_induction; intros n
  induction n <;> simp at *
  case a.zero =>
    rw [String.decEq_refl a]; simp
    constructor <;> try constructor <;> try constructor
    intros p
    contradiction
  case a.succ n ih =>
    rw [String.decEq_refl a] at *; simp at *
    cases ih
    case S_axiom_neg nv1 nv2 e =>
      constructor <;> try constructor <;> try assumption
      intros p
      contradiction


end Sinf
