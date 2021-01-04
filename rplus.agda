module rplus where

open import DSt

open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality



exp0 : {var : typ → Set} {α : typ} {μα : trail} →
       term[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α

exp0 = Prompt refl (Val (Num 12))

term1 : {var : typ → Set}{α : typ} {μα : trail} →
        term[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
term1 = Val (Num 1)

term8 : {var : typ → Set}{α : typ} {μα : trail} →
        term[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
term8 = Val (Num 8)

termx : {var : typ → Set}{τ α : typ}{μα : trail} →
        term[ var ] (τ ⇒ τ ⟨ μα ⟩ α ⟨ μα ⟩ α) ⟨ μα ⟩ α ⟨ μα ⟩ α

termx = Val (Fun λ x → Val (Var x))

-- termyz : {var : typ → Set} → {!!}
-- termyz = Val (Fun (λ y → Val (Fun (λ z → Val (Var z)))))

termy : {var : typ → Set}{τ α : typ}{μα : trail} →
        term[ var ] (τ ⇒ τ ⟨ μα ⟩ α ⟨ μα ⟩ α) ⟨ μα ⟩ α ⟨ μα ⟩ α

termy = Val (Fun λ y → Val (Var y))

test4 : {var : typ → Set}{μα : trail}{τ₂ : typ} →
        Reduce* {var}{τ₂ = τ₂}{μα = μα} (App termx term1) term1


test4 = R*Trans (App (Val (Fun (λ z → Val (Var z)))) (Val (Num 1)))
        (Val (Num 1)) (Val (Num 1)) (RBeta (sVal sVar=))
        (R*Id (Val (Num 1)))


exp3 : {var : typ → Set} {α : typ} {μα : trail} →
       term[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
       
exp3 = Plus (Val (Num 1)) (Val (Num 2))

test1 : {var : typ → Set}{τ₂ : typ}{μβ : trail} →
       Reduce {var}{τ₂ = τ₂}{μβ = μβ} exp3 (Val (Num 3))

test1 = RPlus

valuex : {var : typ → Set}{τ α : typ}{μα : trail} →
        value[ var ] (τ ⇒ τ ⟨ μα ⟩ α ⟨ μα ⟩ α) 
valuex = (Fun λ x → Val (Var x))

test7 : {var : typ → Set}{τ₂ : typ}{μα : trail} →
         Reduce* {var}{τ₂ = τ₂} {μα = μα} (App (Val (valuex)) (Plus (Val (Num 1)) (Val (Num 2)))) (Val (Num 3))

test7 = R*Trans (App (Val valuex) (Plus (Val (Num 1)) (Val (Num 2)))) (frame-plug (App₂ valuex) (Val (Num 3)))
       (Val (Num 3))
       (RFrame (App₂ valuex) RPlus)
       (R*Trans (frame-plug (App₂ valuex) (Val (Num 3))) (Val (Num 3)) (Val (Num 3))
       (RBeta (sVal sVar=)) (R*Id (Val (Num 3))))


exp4 : {var : typ → Set} {β : typ} {μβ : trail} →
       term[ var ] Nat ⟨ μβ ⟩ β ⟨ μβ ⟩ β

exp4 = Prompt (refl , refl , refl)
                      (Control {μ₀ = Nat ⇒ Nat , ∙}
                               {μ₂ = ∙}
                               refl refl refl
                               (λ k → (Val (Num 1))))
                               
test2′ : {var : typ → Set}{τ₂ : typ} →
         Reduce* {var} {τ₂ = Nat}{μα = Nat ⇒ Nat , ∙} exp4 (Val (Num 1))

test2′ = R*Trans exp4
         (Prompt refl
           (App (Val (Fun (λ k → Val (Num 1))))
            (Val (Fun (λ x → pcontext-plug Hole (Val (Var x))))))) (Val (Num 1))
         (RControl {β' = Tbool}{τ₃ = Tbool}{τ₄ = Tbool}{τ₅ = Tbool}
                   {μβ' = ∙}{μ₄ = ∙}{μ₅ = ∙}
         Hole Hole refl refl refl Hole (λ k → Val (Num 1)))
         (R*Trans (Prompt refl
                    (App (Val (Fun (λ k → Val (Num 1))))
                     (Val (Fun (λ x → pcontext-plug Hole (Val (Var x)))))))
                     (frame-plug (Pro refl) (Val (Num 1))) (Val (Num 1))
                     (RFrame (Pro refl) (RBeta (sVal sNum)))
                     (R*Trans (frame-plug (Pro refl) (Val (Num 1))) (Val (Num 1)) (Val (Num 1))
                     RPrompt (R*Id (Val (Num 1)))))





exp4′ : {var : typ → Set} {β : typ} {μβ : trail} →
       term[ var ] Nat ⟨ μβ ⟩ β ⟨ μβ ⟩ β

exp4′ = Plus (Val (Num 2)) (Prompt refl (Plus (Val (Num 3)) (Val (Num 3))))

                              
exp5 : {var : typ → Set} {α τ : typ} {μα : trail} →
       term[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α

exp5 = Prompt refl (Plus (Val (Num 1)) (Val (Num 2)))


-- equational reasoning
infix  3 _∎
infixr 2 _⟶⟨_⟩_ _⟶*⟨_⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : {var : typ → Set} → {τ α β : typ}{μα μβ : trail} →
         {e₁ e₂ : term[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β } → Reduce* e₁ e₂ → Reduce* e₁ e₂
begin_ red = red

_⟶⟨_⟩_ : {var : typ → Set} → {τ α β : typ}{μα μβ : trail} →
           (e₁ {e₂ e₃} : term[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) → Reduce e₁ e₂ → Reduce* e₂ e₃ →
           Reduce* e₁ e₃
_⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-red-e₂ e₂-red*-e₃ =
  R*Trans e₁ e₂ e₃ e₁-red-e₂ e₂-red*-e₃

_⟶*⟨_⟩_ : {var : typ → Set} → {τ α β : typ}{μα μβ : trail} →
            (e₁ {e₂ e₃} : term[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) → Reduce* e₁ e₂ → Reduce* e₂ e₃ →
            Reduce* e₁ e₃
_⟶*⟨_⟩_ e₁ {.e₁} {e₃} (R*Id .e₁) e₁-red*-e₃ = e₁-red*-e₃
_⟶*⟨_⟩_ e₁ {.e₂} {e₃} (R*Trans .e₁ e₁′ e₂ e₁-red-e₁′ e₁′-red*-e₂) e₂-red*-e₃ =
  R*Trans e₁ e₁′ e₃ e₁-red-e₁′
          (e₁′ ⟶*⟨ e₁′-red*-e₂ ⟩ e₂-red*-e₃)

_≡⟨_⟩_ : {var : typ → Set} → {τ α β : typ}{μα μβ : trail} →
           (e₁ {e₂ e₃} : term[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) → e₁ ≡ e₂ → Reduce* e₂ e₃ →
           Reduce* e₁ e₃
_≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-red*-e₃ = e₂-red*-e₃

_∎ : {var : typ → Set} → {τ α β : typ}{μα μβ : trail} →
     (e : term[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) → Reduce* e e
_∎ e = R*Id e


test8 : {var : typ → Set}{μα : trail}{τ₂ : typ} →
  Reduce* {var}{τ₂ = Nat}{μα = μα} (App termx (App termy term1)) term1

test8 = begin
     App termx (App termy term1)
     ⟶⟨ RFrame (App₂ (Fun (λ x → Val (Var x)))) (RBeta (sVal sVar=)) ⟩
     frame-plug (App₂ (Fun (λ x → Val (Var x)))) (Val (Num 1))
     ≡⟨ refl ⟩
     App (Val (Fun (λ x → Val (Var x)))) (Val (Num 1))
     ⟶⟨ RBeta (sVal sVar=) ⟩
     term1
     ∎



 
test2′e : {var : typ → Set}{τ₂ : typ} →
         Reduce* {var} {τ₂ = Nat}{μα = Nat ⇒ Nat , ∙} exp4 (Val (Num 1))

test2′e = begin
       exp4
       ⟶⟨ RControl {β' = Tbool}{τ₃ = Tbool}{τ₄ = Tbool}{τ₅ = Tbool}
                    {μβ' = ∙}{μ₄ = ∙}{μ₅ = ∙}
                     Hole Hole refl refl refl Hole (λ k → (Val (Num 1))) ⟩
       Prompt refl
         (App (Val (Fun (λ k → Val (Num 1))))
          (Val (Fun (λ x → pcontext-plug Hole (Val (Var x))))))
       ⟶⟨ RFrame (Pro refl) (RBeta (sVal sNum)) ⟩
       frame-plug (Pro refl) (Val (Num 1))
       ⟶⟨ RPrompt ⟩
       Val (Num 1)
       ∎
exp4-2 : {var : typ → Set} {β : typ} {μβ : trail} →
       term[ var ] Nat ⟨ μβ ⟩ β ⟨ μβ ⟩ β
exp4-2 = Prompt (refl , refl , refl)
               (Plus (Val (Num 2))
                     (Control {μ₀ = Nat ⇒ Nat , ∙}{μ₂ = ∙}
                              refl refl refl
                              (λ k → (Val (Num 1)))))

test4-2 : {var : typ → Set}{τ₂ : typ}{μα : trail} →
        Reduce* {var}{τ₂ = Nat}{μα = Nat ⇒ Nat , ∙} (exp4-2) (Val (Num 1))

test4-2 = begin
       exp4-2
       ⟶⟨ RControl {β' = Tbool}{τ₃ = Tbool}{τ₄ = Tbool}{τ₅ = Tbool}
                    {μβ' = ∙}{μ₄ = ∙}{μ₅ = ∙}
                    (Frame (Plus₂ (Num 2)) Hole) (Frame (Plus₂ (Num 2)) Hole)
            refl refl refl (Frame (Plus₂ (Num 2)) Hole) (λ k → (Val (Num 1))) ⟩
       Prompt refl
         (App (Val (Fun (λ k → Val (Num 1))))
          (Val
           (Fun
            (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x))))))
       ⟶⟨ RFrame (Pro refl) (RBeta (sVal sNum)) ⟩
       frame-plug (Pro refl) (Val (Num 1))
       ⟶⟨ RPrompt ⟩
       Val (Num 1)
       ∎

exp4-3 : {var : typ → Set} {β : typ} {μβ : trail} →
       term[ var ] Nat ⟨ μβ ⟩ β ⟨ μβ ⟩ β
exp4-3 =
       Prompt (refl , refl , refl)
               (Plus (Val (Num 2))
                     (Control {μ₀ = Nat ⇒ Nat , ∙}{μ₂ = ∙}
                              refl refl refl
                              (λ k → App (Val (Var k))
                                         (Val (Num 3)))))

test4-3 : {var : typ → Set}{τ₂ : typ}{μα : trail} →
        Reduce* {var}{τ₂ = Nat}{μα = Nat ⇒ Nat , ∙} (exp4-3) (Val (Num 5))

test4-3 = begin
      exp4-3
      ⟶⟨ RControl{β' = Tbool}{τ₃ = Tbool}{τ₄ = Tbool}{τ₅ = Tbool}
                    {μβ' = ∙}{μ₄ = ∙}{μ₅ = ∙}
      (Frame (Plus₂ (Num 2)) Hole) (Frame (Plus₂ (Num 2)) Hole)
      refl refl refl (Frame (Plus₂ (Num 2)) Hole) (λ k → App (Val (Var k))
                                         (Val (Num 3))) ⟩
      Prompt refl
        (App (Val (Fun (λ k → App (Val (Var k)) (Val (Num 3)))))
         (Val
          (Fun
           (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x))))))
      ⟶⟨ RFrame (Pro refl) (RBeta (sApp (sVal sVar=) (sVal sNum))) ⟩
      frame-plug (Pro refl)
        (App (Val (Fun (λ y → Plus (Val (Num 2)) (Val (Var y)))))
         (Val (Num 3)))
      ⟶⟨ RFrame (Pro refl) (RBeta (sPlu (sVal sNum) (sVal sVar=))) ⟩
      frame-plug (Pro refl) (Plus (Val (Num 2)) (Val (Num 3)))
      ⟶⟨ RFrame (Pro refl) RPlus ⟩
      frame-plug (Pro refl) (Val (Num (2 + 3)))
      ⟶⟨ RPrompt ⟩
      Val (Num 5)
      ∎
      
exp4-4 : {var : typ → Set} {β : typ} {μβ : trail} →
       term[ var ] Nat ⟨ μβ ⟩ β ⟨ μβ ⟩ β
exp4-4 =
     Plus (Val (Num 1))
       (Prompt (refl , refl , refl)
               (Plus (Val (Num 2))
                     (Control {μ₀ = Nat ⇒ Nat , ∙}{μ₂ = ∙}
                              refl refl refl
                              (λ k → App (Val (Var k))
                                         (App (Val (Var k)) (Val (Num 3)))))))


test4-4 : {var : typ → Set}{τ₂ : typ}{μα : trail} →
        Reduce* {var}{τ₂ = Nat}{μα = Nat ⇒ Nat , ∙} (exp4-4) (Val (Num 8))


test4-4 = begin
      exp4-4
      ⟶⟨ RFrame (Plus₂ (Num 1))
         (RControl {β' = Tbool}{τ₃ = Tbool}{τ₄ = Tbool}{τ₅ = Tbool}
                   {μβ' = ∙}{μ₄ = ∙}{μ₅ = ∙}
         (Frame (Plus₂ (Num 2)) Hole) (Frame (Plus₂ (Num 2)) Hole)
          refl refl refl (Frame (Plus₂ (Num 2)) Hole) (λ k → App (Val (Var k))
                                            (App (Val (Var k)) (Val (Num 3))))) ⟩
       frame-plug (Plus₂ (Num 1))
      (Prompt refl
        (App (Val
          (Fun (λ k → App (Val (Var k)) (App (Val (Var k)) (Val (Num 3))))))
         (Val
         (Fun (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x)))))))
      ⟶⟨ RFrame (Plus₂ (Num 1)) (RFrame (Pro refl)
         (RBeta (sApp (sVal sVar=) (sApp (sVal sVar=) (sVal sNum))))) ⟩
       frame-plug (Plus₂ (Num 1))
        (frame-plug (Pro refl)
         (App (Val
           (Fun (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x)))))
          (App (Val
            (Fun (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x)))))
           (Val (Num 3)))))
      ⟶⟨ RFrame (Plus₂ (Num 1)) (RFrame (Pro refl)
          (RFrame (App₂ (Fun (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x)))))
          (RBeta (sPlu (sVal sNum) (sVal sVar=))))) ⟩
       frame-plug (Plus₂ (Num 1)) (frame-plug (Pro refl)
      (frame-plug
        (App₂
         (Fun (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x)))))
        (Plus (Val (Num 2)) (Val (Num 3)))))
      ⟶⟨ RFrame (Plus₂ (Num 1)) (RFrame (Pro refl)
          (RFrame
          (App₂ (Fun (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x))))) RPlus)) ⟩
       frame-plug (Plus₂ (Num 1))
        (frame-plug (Pro refl)
         (frame-plug
          (App₂
           (Fun (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x)))))
           (Val (Num (2 + 3)))))
      ⟶⟨ RFrame (Plus₂ (Num 1)) (RFrame (Pro refl) (RBeta (sPlu (sVal sNum) (sVal sVar=)))) ⟩
       frame-plug (Plus₂ (Num 1))
        (frame-plug (Pro refl) (Plus (Val (Num 2)) (Val (Num (2 + 3)))))
      ⟶⟨ RFrame (Plus₂ (Num 1)) (RFrame (Pro refl) RPlus) ⟩
       frame-plug (Plus₂ (Num 1))
        (frame-plug (Pro refl) (Val (Num (2 + (2 + 3)))))
      ⟶⟨ RFrame (Plus₂ (Num 1)) RPrompt ⟩
       frame-plug (Plus₂ (Num 1)) (Val (Num (2 + (2 + 3))))
      ⟶⟨ RPlus ⟩
       Val (Num 8)
      ∎
