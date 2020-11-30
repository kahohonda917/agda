module rplus where

open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

infixr 5 _⇒_⟨_⟩_⟨_⟩_
-- type
mutual
  data typ : Set where
    Nat : typ
    Tbool : typ
    _⇒_⟨_⟩_⟨_⟩_ : typ → typ → trail → typ → trail → typ → typ

  data trail : Set where
    ∙ : trail
    _⇒_,_ : typ → typ → trail → trail

compatible : trail → trail → trail → Set
compatible ∙ μ₂ μ₃ = μ₂ ≡ μ₃
compatible (τ₁ ⇒ τ₁' , μ₁) ∙ μ₃ = (τ₁ ⇒ τ₁' , μ₁) ≡ μ₃
compatible (τ₁ ⇒ τ₁' , μ₁) (τ₂ ⇒ τ₂' , μ₂) ∙ = ⊥
compatible (τ₁ ⇒ τ₁' , μ₁) (τ₂ ⇒ τ₂' , μ₂) (τ₃ ⇒ τ₃' , μ₃) =
           (τ₁ ≡ τ₃) × (τ₁' ≡ τ₃') × (compatible (τ₂ ⇒ τ₂' , μ₂) μ₃ μ₁)

is-id-trail : typ → typ → trail → Set
is-id-trail τ τ' ∙ = τ ≡ τ'
is-id-trail τ τ' (τ₁ ⇒ τ₁' , μ) = (τ ≡ τ₁) × (τ' ≡ τ₁') × (μ ≡ ∙)

-- source term
mutual
  data value[_]_ (var : typ → Set) : typ → Set where
    Var : {τ₁ : typ} → var τ₁ → value[ var ] τ₁
    Num : (n : ℕ) → value[ var ] Nat
    -- Bol : (b : 𝔹) → value[ var ] Tbool
    Fun : {τ₁ τ₂ α β : typ}{μα μβ : trail} →
          (e₁ : var τ₂ → term[ var ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β)
          → value[ var ] (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β)

  data term[_]_⟨_⟩_⟨_⟩_ (var : typ → Set) : typ → trail → typ → trail → typ → Set where
    Val : {τ₁ α : typ}{μα : trail} → value[ var ] τ₁ → term[ var ] τ₁ ⟨ μα ⟩ α ⟨ μα ⟩ α
    App : {τ₁ τ₂ α β γ δ : typ}{μα μβ μγ μδ : trail} →
          (e₁ : term[ var ] (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ) →
          (e₂ : term[ var ] τ₂ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ) →
          term[ var ] τ₁ ⟨ μα ⟩ α ⟨ μδ ⟩ δ
    Plus : {α β γ : typ} {μα μβ μγ : trail} →
           term[ var ] Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ →
           term[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β →
           term[ var ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ
    -- Equal : {τ₁ τ₂ β γ σ : typ} →
    --       (e₁ : term[ var ] Nat , γ , σ) → (e₂ : term[ var ] Nat , β , γ) →
    --       term[ var ] Tbool , β , σ
    Control : {τ α β γ γ' t₁ t₂ : typ}{μ₀ μ₁ μ₂ μᵢ μα μβ : trail} →
             (is-id-trail γ γ' μᵢ) →
             (compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
             (compatible μβ μ₀ μα) →
             (e : var (τ ⇒ t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) → term[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
             term[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β
    Prompt : {τ α β β' : typ}{μᵢ μα : trail} →
             (is-id-trail β β' μᵢ) →
             (e : term[ var ] β ⟨ μᵢ ⟩ β' ⟨ ∙ ⟩ τ) →
             term[ var ] τ ⟨ μα ⟩ α ⟨ μα ⟩ α

mutual
  ⟦_⟧τ : typ → Set
  ⟦ Nat ⟧τ = ℕ
  ⟦ Tbool ⟧τ = 𝔹
  ⟦ τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β ⟧τ = ⟦ τ₂ ⟧τ → ( ⟦ τ₁ ⟧τ → ⟦ μα ⟧μ → ⟦ α ⟧τ) → ⟦ μβ ⟧μ → ⟦ β ⟧τ

  ⟦_⟧μ : trail → Set
  ⟦ ∙ ⟧μ = ⊤
  ⟦ τ ⇒ τ' , μ ⟧μ = ⟦ τ ⟧τ → ⟦ μ ⟧μ → ⟦ τ' ⟧τ



cons-trail : {τ₁ τ₂ : typ}{μ μα μβ : trail} → compatible (τ₁ ⇒ τ₂ , μ) μα μβ
            → ⟦ τ₁ ⇒ τ₂ , μ ⟧μ → ⟦ μα ⟧μ → ⟦ μβ ⟧μ
cons-trail {μα = ∙} refl k tt = k
cons-trail {μα = x₃ ⇒ x₄ , μα} {x₁ ⇒ x₅ , μβ} (refl , refl , snd) k k' =
  λ v t' → k v (cons-trail snd k' t')

append-trail : {μα μβ μγ : trail} → compatible μα μβ μγ → ⟦ μα ⟧μ → ⟦ μβ ⟧μ → ⟦ μγ ⟧μ
append-trail {∙} refl tt t = t
append-trail {x₃ ⇒ x₄ , μα} x k t = cons-trail x k t

idk : {τ₁ τ₂ : typ}{μ : trail} → is-id-trail τ₁ τ₂ μ → ⟦ τ₁ ⟧τ → ⟦ μ ⟧μ → ⟦ τ₂ ⟧τ
idk {μ = ∙} refl v tt = v
idk {μ = x₃ ⇒ x₄ , .∙} (refl , refl , refl) v k = k v tt

idt = ∙



mutual
  ⟦_⟧v : {τ : typ} →  value[ ⟦_⟧τ ] τ →  ⟦ τ ⟧τ
  ⟦ Var x ⟧v = x
  ⟦ Num n ⟧v = n
  ⟦ Fun e ⟧v = λ v  → ⟦ e v ⟧




  ⟦_⟧ : {τ α β : typ}{µα µβ : trail} →  term[ ⟦_⟧τ ] τ ⟨ µα ⟩ α ⟨ µβ ⟩ β
           → ( ⟦ τ ⟧τ →  ⟦ µα ⟧μ → ⟦ α ⟧τ ) → ⟦ µβ ⟧μ → ⟦ β ⟧τ
  ⟦ Val v ⟧ k t = k ⟦ v ⟧v t
  ⟦ App e₁ e₂ ⟧ k t = ⟦ e₁ ⟧ (λ x → ⟦ e₂ ⟧ (λ y → x y k )) t
  ⟦ Plus e₁ e₂ ⟧ k t = ⟦ e₁ ⟧ (λ x → ⟦ e₂ ⟧ (λ y → k ( x + y ) )) t
  ⟦ Control x x₂ x₃ e ⟧ k t = ⟦ e (λ v k' t' → k v (append-trail x₃ t (cons-trail x₂ k' t'))) ⟧ (idk x) tt 
  ⟦ Prompt x e ⟧ k t = k (⟦ e ⟧ (idk x) tt) t

mutual
  data SubstVal {var : typ → Set} : {τ₁ τ₂ : typ} →
                (var τ₁ → value[ var ] τ₂) →
                value[ var ] τ₁ →
                value[ var ] τ₂ → Set where
   -- (λx.x)[v] → v
    sVar= : {τ₁ : typ} {v : value[ var ] τ₁} →
            SubstVal (λ x → Var x) v v
   -- (λ_.x)[v] → x
    sVar≠ : {τ₁ τ₂ : typ} {v : value[ var ] τ₂} {x : var τ₁} →
            SubstVal (λ _ → Var x) v (Var x)
   -- (λ_.n)[v] → n
    sNum  : {τ₁ : typ} {v : value[ var ] τ₁} {n : ℕ} →
            SubstVal (λ _ → Num n) v (Num n)
   -- (λy.λx.ey)[v] → λx.e′
    sFun  : {τ τ₁ τ₂ α β : typ}{μα μβ : trail} →
            {e₁ : var τ₁ → var τ → term[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
            {v : value[ var ] τ₁} →
            {e₁′ : var τ → term[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
            ((x : var τ) → Subst (λ y → (e₁ y) x) v (e₁′ x)) →
            SubstVal (λ y → Fun (e₁ y)) v (Fun e₁′)

  data Subst {var : typ → Set} : {τ₁ τ₂ τ₃ τ₄ : typ}{μα μβ : trail} →
             (var τ₁ → term[ var ] τ₂ ⟨ μα ⟩ τ₃ ⟨ μβ ⟩ τ₄) →
             value[ var ] τ₁ →
             term[ var ] τ₂ ⟨ μα ⟩ τ₃ ⟨ μβ ⟩ τ₄ → Set where

     sVal  : {τ τ₁ : typ}{μα : trail} →
             {v₁ : var τ → value[ var ] τ₁} →
             {v : value[ var ] τ} →
             {v₁′ : value[ var ] τ₁} →
             SubstVal v₁ v v₁′ →
             Subst {τ₃ = τ₁}{μα = μα}(λ y → Val (v₁ y)) v (Val v₁′)

     sApp  : {τ τ₁ τ₂ α β γ δ : typ}{μα μβ μγ μδ : trail} →
             {e₁ : var τ → term[ var ] (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ}
             {e₂ : var τ → term[ var ] τ₂ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ}
             {v : value[ var ] τ}
             {e₁′ : term[ var ] (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ}
             {e₂′ : term[ var ] τ₂ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ} →
             Subst e₁ v e₁′ → Subst e₂ v e₂′ →
             Subst (λ y → App (e₁ y) (e₂ y))
                   v
                   (App e₁′ e₂′)

     sPlu : {τ α β γ : typ} {μα μβ μγ : trail} →
            {e₁ : var τ → term[ var ] Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ}
            {e₂ : var τ → term[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β }
            {v : value[ var ] τ}
            {e₁′ : term[ var ] Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ }
            {e₂′ : term[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β  } →
            Subst e₁ v e₁′ → Subst e₂ v e₂′ →
            Subst (λ y → Plus (e₁ y) (e₂ y)) v (Plus e₁′ e₂′)



     sCon : {τ t₁ t₂ τ₃ α β γ γ' : typ}{μ₀ μ₁ μ₂ μᵢ μα μβ : trail} →
            {e₁ : var τ₃ →
                  var (τ ⇒ t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
                  term[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ β} →
            {v : value[ var ] τ₃} →
            {e₁′ : var (τ ⇒ t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
                  term[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ β} →
            {x : is-id-trail γ γ' μᵢ} →
            {x₂ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀} →
            {x₃ : compatible μβ μ₀ μα} →
            ((k : var (τ ⇒ t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α)) →
                 Subst (λ y → (e₁ y) k) v ((e₁′ k))) →
            Subst (λ y → Control x x₂ x₃ (e₁ y))
                  v
                  (Control x x₂ x₃ e₁′)

     sPro : {τ β β' γ τ₃ : typ}{μᵢ μα : trail} →
            {e₁ : var τ → term[ var ] β ⟨ μᵢ ⟩ β' ⟨ ∙ ⟩ γ} →
            {v : value[ var ] τ} →
            {e₁′ : term[ var ] β ⟨ μᵢ ⟩ β' ⟨ ∙ ⟩ γ} →
            {x : is-id-trail β β' μᵢ} →
            Subst e₁ v e₁′ →
            Subst {τ₃ = τ₃}{μα = μα} (λ y → Prompt x (e₁ y)) v
                  (Prompt x e₁′)

  --frame
  data frame[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : typ → Set)
       : typ → trail → typ → trail → typ → typ → trail → typ → trail → typ → Set where
    App₁ : {τ₁ τ₂ α β γ δ : typ}{μα μβ μγ μδ : trail} →
           (e₂ : term[ var ] τ₂ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ) →
           frame[ var , (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ ]
                  τ₁ ⟨ μα ⟩ α ⟨ μδ ⟩ δ

    App₂ : {τ₁ τ₂ α β γ : typ}{μα μβ μγ : trail} →
           (v₁ : value[ var ] (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β)) →
           frame[ var , τ₂ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ]
                  τ₁ ⟨ μα ⟩ α ⟨ μγ ⟩ γ

    Plus₁ : {α β γ : typ} {μα μβ μγ : trail} →
            (e₂ : term[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            frame[ var , Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

    Plus₂ : {α γ : typ} {μα μγ : trail} →
            (v₁ : value[ var ] Nat) →
            frame[ var , Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ
            

    Pro  : {τ α β β' : typ}{μᵢ μα : trail} →
           (is-id-trail β β' μᵢ) →
           frame[ var , β ⟨ μᵢ ⟩ β' ⟨ ∙ ⟩ τ ] τ ⟨ μα ⟩ α ⟨ μα ⟩ α

  frame-plug : {var : typ → Set}
               {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μδ : trail} →
               frame[ var , τ₂ ⟨ μα ⟩ τ₄ ⟨ μβ ⟩ τ₅ ] τ₁ ⟨ μγ ⟩ τ₃ ⟨ μδ ⟩ τ₆ →
               term[ var ] τ₂ ⟨ μα ⟩ τ₄ ⟨ μβ ⟩ τ₅ →
               term[ var ] τ₁ ⟨ μγ ⟩ τ₃ ⟨ μδ ⟩ τ₆
  frame-plug (App₁ e₂) e₁ = App e₁ e₂
  frame-plug {μβ = μβ}(App₂ v₁) e₂ = App (Val v₁) e₂
  frame-plug (Plus₁ e₂) e₁ = Plus e₁ e₂
  frame-plug (Plus₂ v₁) e₂ = Plus (Val v₁) e₂

  frame-plug {τ₁ = τ₁}{τ₂ = τ₂}{τ₃ = τ₃}{τ₄ = τ₄}{μα = μα}{μγ = μγ} (Pro x) e₁ =
             Prompt x e₁

  --frame
  data pframe[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : typ → Set)
       : typ → trail → typ → trail → typ → typ → trail → typ → trail → typ → Set where
    App₁ : {τ₁ τ₂ α β γ δ : typ}{μα μβ μγ μδ : trail} →
           (e₂ : term[ var ] τ₂ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ) →
           pframe[ var , (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ ]
                   τ₁ ⟨ μα ⟩ α ⟨ μδ ⟩ δ

    App₂ : {τ₁ τ₂ α β γ : typ}{μα μβ μγ : trail} →
           (v₁ : value[ var ] (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β)) →
           pframe[ var , τ₂ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ]
                   τ₁ ⟨ μα ⟩ α ⟨ μγ ⟩ γ

    Plus₁ : {α β γ : typ} {μα μβ μγ : trail} →
            (e₂ : term[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            pframe[ var , Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

    Plus₂ : {α γ : typ} {μα μγ : trail} →
            (v₁ : value[ var ] Nat) →
            pframe[ var , Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  pframe-plug : {var : typ → Set}
                {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μδ : trail} →
                pframe[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
                term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
                term[ var ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆

  pframe-plug (App₁ e₂) e₁ = App e₁ e₂
  pframe-plug (App₂ v₁) e₂ = App (Val v₁) e₂
  pframe-plug (Plus₁ e₂) e₁ = Plus e₁ e₂
  pframe-plug (Plus₂ v₁) e₂ = Plus (Val v₁) e₂

  data same-pframe {var : typ → Set}:
                   {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : typ}
                   {μα μα' μβ μβ' μγ μγ' μδ μδ' : trail} →
         pframe[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
         pframe[ var , τ₁' ⟨ μα' ⟩ τ₂' ⟨ μβ' ⟩ τ₃' ] τ₄' ⟨ μγ' ⟩ τ₅' ⟨ μδ' ⟩ τ₆' →
         Set where
   App₁ : {τ β γ τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' : typ}{μ₁ μ₂ μβ μβ' μγ μγ' : trail} →
          (e₂ : term[ var ] τ ⟨ μ₁ ⟩ β ⟨ μ₂ ⟩ γ) →
          same-pframe {τ₃ = τ₃}{τ₃'}{τ₄}{τ₄'}{τ₅}{τ₅'}{μβ = μβ}{μβ'}{μγ}{μγ'}
                      (App₁ e₂) (App₁ e₂)
   App₂ : {τ₁ τ₂ α β τ₃ τ₃' : typ}{μ₁ μ₂ μβ μβ' : trail} →
          (v₁ : value[ var ] (τ₂ ⇒ τ₁ ⟨ μ₁ ⟩ α ⟨ μ₂ ⟩ β) ) →
          same-pframe {τ₃ = τ₃}{τ₃'}{μβ = μβ}{μβ'}
                      (App₂ v₁) (App₂ v₁)

   Plus₁ : {α β γ τ₃ τ₃' : typ} {μα μβ μγ μβ' : trail} →
           (e₂ : term[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
           same-pframe {τ₃ = τ₃}{τ₃'}{μβ = μβ}{μβ'} (Plus₁ e₂) (Plus₁ e₂)

   Plus₂ : {τ₂ τ₂' τ₃ τ₃' : typ} {μα μα' μβ μβ' : trail} →
           (v₁ : value[ var ] Nat) →
           same-pframe {τ₂ = τ₂}{τ₂'}{τ₃}{τ₃'}{μα = μα}{μα'}{μβ}{μβ'} (Plus₂ v₁) (Plus₂ v₁)


  -- pure context
  data pcontext[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : typ → Set)
       : typ → trail → typ → trail → typ → typ → trail → typ → trail → typ → Set where
   Hole : {τ₁ τ₂ τ₃ : typ}{μα μβ : trail} →
          pcontext[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃
   Frame : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ : typ}{μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : trail} →
           (f : pframe[ var , τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ ] τ₇ ⟨ μ₅ ⟩ τ₈ ⟨ μ₆ ⟩ τ₉ ) →
           (c : pcontext[ var , τ₁ ⟨ μ₁ ⟩ τ₂ ⟨ μ₂ ⟩ τ₃ ] τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ ) →
           pcontext[ var , τ₁ ⟨ μ₁ ⟩ τ₂ ⟨ μ₂ ⟩ τ₃ ] τ₇ ⟨ μ₅ ⟩ τ₈ ⟨ μ₆ ⟩ τ₉

  pcontext-plug : {var : typ → Set}
                  {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μδ : trail} →
                  pcontext[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
                  term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
                  term[ var ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆
  pcontext-plug Hole e₁ = e₁
  pcontext-plug (Frame f p) e₁ = pframe-plug f (pcontext-plug p e₁)

  data same-pcontext {var : typ → Set} :
                     {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : typ}
                     {μα μα' μβ μβ' μγ μγ' μδ μδ' : trail} →
                     pcontext[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
                     pcontext[ var , τ₁' ⟨ μα' ⟩ τ₂' ⟨ μβ' ⟩ τ₃' ] τ₄' ⟨ μγ' ⟩ τ₅' ⟨ μδ' ⟩ τ₆' →
                     Set where
       Hole  : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' : typ}{μα μα' μβ μβ' : trail} →
               same-pcontext {τ₁ = τ₁}{τ₁'}{τ₂}{τ₂'}{τ₃}{τ₃'}{μα = μα}{μα'}{μβ}{μβ'}
                             Hole Hole
       Frame : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' τ₇ τ₇' τ₈' τ₈ τ₉ τ₉' : typ}
               {μ₁ μ₁' μ₂ μ₂' μ₃ μ₃' μ₄ μ₄' μ₅ μ₅' μ₆ μ₆' : trail} →
               {f₁ : pframe[ var , τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ ] τ₇ ⟨ μ₅ ⟩ τ₈ ⟨ μ₆ ⟩ τ₉ } →
               {f₂ : pframe[ var , τ₄' ⟨ μ₃' ⟩ τ₅' ⟨ μ₄' ⟩ τ₆' ] τ₇' ⟨ μ₅' ⟩ τ₈' ⟨ μ₆' ⟩ τ₉' } →
               same-pframe f₁ f₂ →
               {c₁ : pcontext[ var , τ₁ ⟨ μ₁ ⟩ τ₂ ⟨ μ₂ ⟩ τ₃ ] τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ } →
               {c₂ : pcontext[ var , τ₁' ⟨ μ₁' ⟩ τ₂' ⟨ μ₂' ⟩ τ₃' ] τ₄' ⟨ μ₃' ⟩ τ₅' ⟨ μ₄' ⟩ τ₆' } →
               same-pcontext c₁ c₂ →
               same-pcontext (Frame f₁ c₁) (Frame f₂ c₂)


  -- reduction rules
  data Reduce {var : typ → Set} :
              {τ₁ τ₂ τ₃ : typ}{μα μβ : trail} →
              term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
              term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ → Set where
    RBeta   : {τ τ₁ τ₂ τ₃ : typ}{μα μβ : trail} →
              {e₁ : var τ → term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃} →
              {v₂ : value[ var ] τ} →
              {e₁′ : term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃} →
              Subst e₁ v₂ e₁′ →
              Reduce (App (Val (Fun e₁)) (Val v₂)) e₁′

    RPlus   : {τ₂ : typ}{μα : trail} →
              {n₁ : ℕ} →
              {n₂ : ℕ} →
              Reduce {τ₂ = τ₂}{μα = μα} (Plus (Val (Num n₁)) (Val (Num n₂))) (Val (Num (n₁ + n₂)))





    RFrame  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μδ : trail} →
              {e₁ : term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃} →
              {e₂ : term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃} →
              (f : frame[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ]
                        τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆) →
              Reduce e₁ e₂ →
              Reduce (frame-plug f e₁) (frame-plug f e₂)

    RPrompt : {τ₂ β : typ}{μα : trail} →
              {v₁ : value[ var ] β} →
              Reduce {τ₂ = τ₂}{μα = ∙}(Prompt refl (Val v₁)) (Val v₁)

    RControl : {τ α α' β β' γ γ' t₁ t₂ τ₁ τ₂ τ₃ τ₄ τ₅ : typ}
               {μ₀ μ₁ μᵢ μα μα' μβ μβ' μ₂ μ₃ μ₄ μ₅ : trail} →
              (p₁ : pcontext[ var , τ ⟨ μα ⟩ α ⟨ μβ ⟩ β ]
                             τ₁ ⟨ μ₃ ⟩ τ₂ ⟨ ∙ ⟩ β ) →
              (p₂ : pcontext[ var , τ ⟨ μα' ⟩ α' ⟨ μα' ⟩ α' ]
                             t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α ) →
              {x₀ : is-id-trail τ₁ τ₂ μ₃} →
              (x₁ : is-id-trail γ γ' μᵢ) →
              (x₂ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
              (x₃ : compatible μβ μ₀ μα) →
              same-pcontext p₁ p₂ →
              (e : var (τ ⇒ t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) → term[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
              Reduce {τ₂ = τ₂}{μα = μα} (Prompt x₀
                     (pcontext-plug p₁ (Control x₁ x₂ x₃ e)))
                     (Prompt x₁ (App (Val (Fun e))
                     (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))))
              -- Reduce {τ₂ = τ₂}{μα = μα}(Prompt x₁
              --        (pcontext-plug p₁ (Control x₁ x₂ x₃ e)))
              --        (Prompt x₁ (App (Val
              --        (Fun e))
              --        (Val (Fun λ x → pcontext-plug p₂ (Val (Var x))))))

-- (p₁ : pcontext[ var , τ ⟨ μα ⟩ α ⟨ μβ ⟩ β ]
--                              γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ β ) →
--               (p₂ : pcontext[ var , τ ⟨ μ₂ ⟩ α ⟨ μ₂ ⟩ α ]
--                              t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α ) →
--               (x₁ : is-id-trail γ γ' μᵢ) →
--               (x₂ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
--               (x₃ : compatible μβ μ₀ μα) →
  data Reduce* {var : typ → Set} :
               {τ₁ τ₂ τ₃ : typ}{μα μβ : trail} →
               term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
               term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ → Set where

    R*Id    : {τ₁ τ₂ τ₃ : typ}{μα μβ : trail} →
              (e : term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ) →
              Reduce* e e
    R*Trans : {τ₁ τ₂ τ₃ : typ}{μα μβ : trail} →
              (e₁ : term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃) →
              (e₂ : term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃) →
              (e₃ : term[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃) →
              Reduce e₁ e₂ →
              Reduce* e₂ e₃ →
              Reduce* e₁ e₃


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

test4 : {var : typ → Set}{μα : trail} →
        Reduce* {var}{μα = μα} (App termx term1) term1


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

test7 : {var : typ → Set}{μα : trail} →
         Reduce* {var} {μα = μα} (App (Val (valuex)) (Plus (Val (Num 1)) (Val (Num 2)))) (Val (Num 3))

test7 = R*Trans (App (Val valuex) (Plus (Val (Num 1)) (Val (Num 2)))) (frame-plug (App₂ valuex) (Val (Num 3)))
       (Val (Num 3))
       (RFrame (App₂ valuex) RPlus)
       (R*Trans (frame-plug (App₂ valuex) (Val (Num 3))) (Val (Num 3)) (Val (Num 3))
       (RBeta (sVal sVar=)) (R*Id (Val (Num 3))))

exp2 : {var : typ → Set} {α : typ} {μα : trail} →
       term[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
exp2 =
  Plus (Val (Num 1))
       (Prompt (refl , refl , refl)
               (Plus (Val (Num 2))
                     (Control {μ₀ = Nat ⇒ Nat , ∙}
                              refl refl refl
                              (λ k → App (Val (Var k))
                                         (App (Val (Var k)) (Val (Num 3)))))))

-- test2 : {var : typ → Set} →
--         Reduce* {var} exp2 (Val (Num 8))

-- test2 = R*Trans exp2
--         {!!}
--         (Val (Num 8))
--         {!!} {!!}

exp4 : {var : typ → Set} {β : typ} {μβ : trail} →
       term[ var ] Nat ⟨ μβ ⟩ β ⟨ μβ ⟩ β

exp4 = Prompt refl
                      (Control {μ₀ = ∙}
                               refl refl refl
                               (λ k → (Val (Num 1))))
test2′ : {var : typ → Set}{τ₂ : typ} →
         Reduce* {var} {τ₂ = τ₂} exp4 (Val (Num 1))

test2′ = R*Trans exp4
        (Prompt refl
          (App (Val (Fun (λ k → Val (Num 1))))
           (Val (Fun (λ x → pcontext-plug Hole (Val (Var x))))))) (Val (Num 1))
        (RControl Hole Hole refl refl refl  Hole λ k → (Val (Num 1)))
        (R*Trans (Prompt refl
                   (App (Val (Fun (λ k → Val (Num 1))))
                    (Val (Fun (λ x → pcontext-plug Hole (Val (Var x)))))))
                    (frame-plug (Pro refl) (Val (Num 1))) (Val (Num 1))
                    (RFrame (Pro refl) (RBeta (sVal sNum)))
                    (R*Trans (frame-plug (Pro refl) (Val (Num 1))) (Val (Num 1)) (Val (Num 1))
                    RPrompt (R*Id (Val (Num 1)))))

exp4-2 : {var : typ → Set} {β : typ} {μβ : trail} →
       term[ var ] Nat ⟨ μβ ⟩ β ⟨ μβ ⟩ β
exp4-2 = Prompt refl
               (Plus (Val (Num 2))
                     (Control {μ₀ = ∙}
                              refl refl refl
                              (λ k → (Val (Num 1)))))

test4-2 : {var : typ → Set} →
        Reduce* {var} (exp4-2) (Val (Num 1))

test4-2 = R*Trans exp4-2 (Prompt refl
                           (App (Val (Fun (λ k → Val (Num 1))))
                            (Val
                             (Fun
                              (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x))))))) (Val (Num 1))
         (RControl (Frame (Plus₂ (Num 2)) Hole) (Frame (Plus₂ (Num 2)) Hole)
         refl refl refl (Frame (Plus₂ (Num 2)) Hole) λ k → (Val (Num 1)))
         (R*Trans (Prompt refl
                    (App (Val (Fun (λ k → Val (Num 1))))
                     (Val
                      (Fun
                       (λ x → pcontext-plug (Frame (Plus₂ (Num 2)) Hole) (Val (Var x)))))))
                       (frame-plug (Pro refl) (Val (Num 1))) (Val (Num 1))
                       (RFrame (Pro refl) (RBeta (sVal sNum)))
                       (R*Trans (frame-plug (Pro refl) (Val (Num 1))) (Val (Num 1)) (Val (Num 1))
                       RPrompt (R*Id (Val (Num 1)))))

-- test2′ = R*Trans exp4 {!!} (Val (Num 1))
--          (RControl (Frame (Plus₂ (Num 2)) Hole) (Frame (Plus₂ (Num 2)) Hole) refl {!!} refl {!!}
--          λ k → Val (Num 1))
--          {!!}

exp4′ : {var : typ → Set} {β : typ} {μβ : trail} →
       term[ var ] Nat ⟨ μβ ⟩ β ⟨ μβ ⟩ β

exp4′ = Plus (Val (Num 2)) (Prompt refl (Plus (Val (Num 3)) (Val (Num 3))))

test2′′ : {var : typ → Set}{τ₂ : typ} →
          Reduce* {var} {τ₂ = τ₂} exp4′ (Val (Num 8))

test2′′ = R*Trans exp4′ (frame-plug (Plus₂ (Num 2))
          (frame-plug (Pro refl) (Val (Num 6))))
          (Val (Num 8))
          (RFrame (Plus₂ (Num 2)) (RFrame (Pro refl) RPlus))
          (R*Trans (frame-plug (Plus₂ (Num 2)) (frame-plug (Pro refl) (Val (Num 6))))
          (frame-plug (Plus₂ (Num 2)) (Val (Num 6))) (Val (Num 8))
          (RFrame (Plus₂ (Num 2)) RPrompt)
          (R*Trans (frame-plug (Plus₂ (Num 2)) (Val (Num 6))) (Val (Num 8)) (Val (Num 8))
          RPlus
          (R*Id (Val (Num 8)))))
                              
exp5 : {var : typ → Set} {α τ : typ} {μα : trail} →
       term[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α

exp5 = Prompt refl (Plus (Val (Num 1)) (Val (Num 2)))

-- λy.λz.z
-- termyz : {var : typ → Set} {α β τ₁ τ₂ τ₃ : typ} {μα μβ : trail}  →
--          term[ var ] ((τ₃ ⇒ τ₂ ⇒ τ₁) ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μα ⟩ α ⟨ μα ⟩ α
-- termyz = Val (Fun (λ x → {!!}))


