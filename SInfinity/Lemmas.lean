import Std.Data.Nat.Lemmas

import SInfinity.Proof

namespace Sinf_term

theorem succ_inj {θ₁ θ₂ : Sinf_term} : S θ₁ = S θ₂ → θ₁ = θ₂ := by
  induction θ₁ <;> induction θ₂ <;> simp at *

end Sinf_term

open Sinf_proof

theorem S_duplicate : ∀ {α Γ},
                      Γ ⊢ₛ α →
                      Γ ⊢ₛ α ∨ₛ α := λ {α} ↦ S_inr α

theorem S_exchange : ∀ {α β Γ},
                     Γ ⊢ₛ α ∨ₛ β →
                     Γ ⊢ₛ β ∨ₛ α := by
  intros α β Γ αβ
  apply S_out; apply S_exchange_ctx; apply S_in; assumption

theorem S_inl : ∀ {α} β {Γ},
                Sinf_proof Γ α →
                Sinf_proof Γ (α ∨ₛ β) := by
  intros α β Γ a
  apply S_exchange; exact (S_inr β a)

theorem S_contraction : ∀ {α Γ},
                     Γ ⊢ₛ α ∨ₛ α →
                     Γ ⊢ₛ α := by
  intros α Γ αα
  apply S_contraction_ctx; apply S_in; assumption

theorem S_dne : ∀ {α Γ},
                Γ ⊢ₛ ¬ₛ ¬ₛ α →
                Γ ⊢ₛ α := by
  intros α Γ dn
  cases dn
  case S_dni β => exact β

theorem S_de_morgan_inv : ∀ {α β Γ},
                          Γ ⊢ₛ ¬ₛ (α ∨ₛ β) →
                          (Γ ⊢ₛ (¬ₛ α)) ∧
                          (Γ ⊢ₛ (¬ₛ β)) := by
  intros α β Γ d
  cases d
  case S_de_morgan nα nβ => exact And.intro nα nβ

theorem S_neg_forall_inv : ∀ {α x Γ},
                           Γ ⊢ₛ (¬ₛ (∀ₛ x ; α)) →
                           (∃ θ, Γ ⊢ₛ (¬ₛ α [x ≔ θ])) := by
  intros α x Γ nf
  cases nf
  case S_neg_forall θ β => exists θ -- exact Exists.intro θ β

theorem S_induction_inv : ∀ {α x Γ},
                          Γ ⊢ₛ ∀ₛ x ; α →
                          ∀ n : Nat, Γ ⊢ₛ α [x ≔ n] := by
  intros α x Γ f
  cases f
  case S_induction i => assumption

namespace Sinf

open Sinf_term

theorem eq_trans : ∀ {θ₁} θ₂ {θ₃ Γ},
                   Γ ⊢ₛ θ₁ =ₛ θ₂ →
                   Γ ⊢ₛ θ₂ =ₛ θ₃ →
                   Γ ⊢ₛ θ₁ =ₛ θ₃ := by
  intros θ₁ θ₂ θ₃ Γ _12 _23
  cases _12
  case S_axiom nv₁ nv₂ e =>
    cases _23
    case S_axiom nv₃ e' =>
      constructor <;> try assumption
      exact (Eq.trans e e')

theorem succ_cong : ∀ {θ₁ θ₂ Γ},
                    Γ ⊢ₛ θ₁ =ₛ θ₂ →
                    Γ ⊢ₛ S θ₁ =ₛ S θ₂ := by
  intros θ₁ θ₂ Γ _12
  cases _12
  case S_axiom nv₁ nv₂ e =>
    constructor <;> try constructor
    simp
    apply (congrArg (Option.map Nat.succ))
    assumption

theorem succ_inj : ∀ {θ₁ θ₂ Γ},
                   Γ ⊢ₛ S θ₁ =ₛ S θ₂ →
                   Γ ⊢ₛ θ₁ =ₛ θ₂ := by
  intros θ₁ θ₂ Γ _12
  cases _12
  case S_axiom nv₁ nv₂ e =>
    constructor <;> sorry

theorem consistent : ∃ α, ¬ (Ø ⊢ₛ α) := by
  exists (¬ₛ O =ₛ O)
  intros p
  cases p
  case S_axiom_neg p => exact p rfl

theorem contradiction_yields_anything :
  ∀ {α β Γ}, Γ ⊢ₛ ¬ₛ (α ∨ₛ ¬ₛ α) → Γ ⊢ₛ β := by
  intros α β Γ contr
  have iβ := S_inr β contr
  have s_return := S_in iβ
  cases S_de_morgan_inv s_return
  case intro n nn =>
    apply S_contraction
    apply S_section (¬ₛ α)
    · apply S_out; assumption
    · apply S_out; apply S_exchange_ctx; assumption

theorem var_refl : Ø ⊢ₛ (∀ₛ a ; _ a =ₛ _ a) := by
  constructor; intros n
  constructor <;> simp <;> rw [String.decEq_refl a] <;> simp <;> apply NoVars.fromNat

theorem plus_comm : Ø ⊢ₛ ∀ₛ a ; ∀ₛ b ; _ a +ₛ _ b =ₛ _ b +ₛ _ a := by
  apply S_induction; intros n; simp
  cases (String.decEq a b)
  case a.isFalse nab =>
    simp
    cases String.decEq a a
    case isFalse c => contradiction
    case isTrue _ =>
      simp; apply S_induction; intros m; simp
      cases String.decEq b b <;> simp
      · contradiction
      · induction n <;> induction m <;> simp
        · constructor <;> constructor
        case a.isTrue.zero.succ ih =>
          cases ih
          case S_axiom nv1 nv2 e =>
            constructor <;> try constructor
            simp at *
            sorry
        case a.isTrue.succ n ih => sorry
        case a.isTrue.succ.succ n m ihn ihm => sorry
  case a.isTrue ab =>
    simp; rw [ab]
    apply S_induction; simp
    cases String.decEq b b
    case a.isFalse => contradiction
    case a.isTrue =>
      simp; intros n
      constructor <;> constructor

theorem succ_ne_zero : Ø ⊢ₛ ∀ₛ a ; ¬ₛ (S (_ a) =ₛ O) := by
  apply S_induction; intros n
  induction n <;> simp at *
  case a.zero =>
    rw [String.decEq_refl a]; simp
    constructor <;> try constructor
    intros h; contradiction
  case a.succ n ih =>
    rw [String.decEq_refl a] at *; simp at *
    cases ih
    case S_axiom_neg nv1 nv2 e =>
      constructor <;> try constructor
      simp

end Sinf
