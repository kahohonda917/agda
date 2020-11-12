module test3 where

open import Data.Nat
open import Data.Bool using (true; false)  renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

infixr 5 _⇒_,⟨_⟩,_,⟨_⟩,_
-- type 
mutual
  data typ : Set where
    Nat : typ
    Tbool : typ
    _⇒_,⟨_⟩,_,⟨_⟩,_ : typ → typ → trail → typ → trail → typ → typ
  
  data trail : Set where
    ∙ : trail
    _⇒_,_ : typ → typ → trail → trail


compatible : trail → trail → trail → Set
compatible ∙ µ₂ µ₃ = µ₂ ≡ µ₃
compatible (τ₁ ⇒ τ₁' , µ₁) ∙ µ₃ = (τ₁ ⇒ τ₁' , µ₁) ≡ µ₃
compatible (τ₁ ⇒ τ₁' , µ₁) (τ₂ ⇒ τ₂' , µ₂) ∙ = ⊥
compatible (τ₁ ⇒ τ₁' , µ₁) (τ₂ ⇒ τ₂' , µ₂) (τ₃ ⇒ τ₃' , µ₃) =
           (τ₁ ≡ τ₃) × (τ₁' ≡ τ₃') × (compatible (τ₂ ⇒ τ₂' , µ₂) µ₃ µ₁)

is-id-trail : typ → typ → trail → Set
is-id-trail τ τ' ∙ = τ ≡ τ'
is-id-trail τ τ' (τ₁ ⇒ τ₁' , µ) = (τ ≡ τ₁) × (τ' ≡ τ₁') × (µ ≡ ∙)



-- source term
mutual
  data value[_]_ (var : typ → Set) : typ → Set where
    Var : {τ₁ : typ} → var τ₁ → value[ var ] τ₁
    Num : (n : ℕ) → value[ var ] Nat
    -- Bol : (b : 𝔹) → value[ var ] Tbool
    Fun : (τ₁ τ₂ {α β} : typ){μα μβ : trail} →
          (e₁ : var τ₂ → term[ var ] τ₁ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β)
          → value[ var ] (τ₂ ⇒ τ₁ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β)

  data term[_]_,⟨_⟩,_,⟨_⟩,_ (var : typ → Set) : typ → trail → typ → trail → typ → Set where
    Val : {τ₁ α : typ}{μα : trail} → value[ var ] τ₁ →  term[ var ] τ₁ ,⟨ μα ⟩, α ,⟨ μα ⟩, α
    App : {τ₁ τ₂ α β γ σ : typ}{μα μβ μγ μσ : trail} →
          (e₁ : term[ var ] (τ₂ ⇒ τ₁ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β) ,⟨ μγ ⟩, γ ,⟨ μσ ⟩, σ) →
          (e₂ : term[ var ] τ₂ ,⟨ μβ ⟩, β ,⟨ μγ ⟩, γ) →
          term[ var ] τ₁ ,⟨ μα ⟩, α ,⟨ μσ ⟩, σ
    -- Plus : {τ₁ τ₂ β γ σ : typ} →
    --       (e₁ : term[ var ] Nat , γ , σ) → (e₂ : term[ var ] Nat , β , γ) →
    --       term[ var ] Nat , β , σ
    -- Equal : {τ₁ τ₂ β γ σ : typ} →
    --       (e₁ : term[ var ] Nat , γ , σ) → (e₂ : term[ var ] Nat , β , γ) →
    --       term[ var ] Tbool , β , σ
    Control : {τ α β γ γ' t₁ t₂ : typ}{μ₀ μ₁ μ₂ μᵢ μα μβ : trail}  →
             (is-id-trail γ γ' μᵢ) →
             (compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
             (compatible μβ μ₀ μα) →
             (e : var (τ ⇒ t₁ ,⟨ μ₁ ⟩, t₂ ,⟨ μ₂ ⟩, α) → term[ var ] γ ,⟨ μᵢ ⟩, γ' ,⟨ ∙ ⟩, β) →
             term[ var ] τ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β
    Prompt : {τ α β β' : typ}{μᵢ μα : trail} →
             (is-id-trail β β' μᵢ) →
             (e : term[ var ] β ,⟨ μᵢ ⟩, β' ,⟨ ∙ ⟩, τ) →
             term[ var ] τ ,⟨ μα ⟩, α ,⟨ μα ⟩, α
mutual
 ⟦_⟧τ : typ → Set
 ⟦ Nat ⟧τ = ℕ
 ⟦ Tbool ⟧τ = 𝔹
 ⟦ τ₂ ⇒ τ₁ ,⟨ µα ⟩, α ,⟨ µβ ⟩, β ⟧τ = ⟦ τ₂ ⟧τ → ( ⟦ τ₁ ⟧τ → ⟦ µα ⟧µ → ⟦ α ⟧τ) → ⟦ µβ ⟧µ → ⟦ β ⟧τ

 ⟦_⟧µ : trail → Set
 ⟦ ∙ ⟧µ = ⊤
 ⟦ τ ⇒ τ' , µ ⟧µ = ⟦ τ ⟧τ → ⟦ µ ⟧µ → ⟦ τ' ⟧τ

cons-trail : {τ₁ τ₂ : typ}{µ µα µβ : trail} → compatible (τ₁ ⇒ τ₂ , µ) µα µβ
            → ⟦ τ₁ ⇒ τ₂ , µ ⟧µ  → ⟦ µα ⟧µ → ⟦ µβ ⟧µ
cons-trail {µα = ∙} refl k tt = k
cons-trail {µα = x₃ ⇒ x₄ , µα} {x₁ ⇒ x₅ , µβ} (refl , refl , snd) k k' = λ v t' → k v (cons-trail snd k' t')


append-trail : {µα µβ µγ : trail} → compatible µα µβ µγ →  ⟦ µα ⟧µ → ⟦ µβ ⟧µ → ⟦ µγ ⟧µ
append-trail {∙} refl tt t = t
append-trail {x₃ ⇒ x₄ , µα} {∙} refl k t = k
append-trail {x₃ ⇒ x₄ , µα} {x₅ ⇒ x₆ , µβ} x k t = cons-trail x k t


idk : {τ₁ τ₂ : typ}{µ : trail} → is-id-trail τ₁ τ₂ µ → ⟦ τ₁ ⟧τ → ⟦ µ ⟧µ → ⟦ τ₂ ⟧τ
idk {µ = ∙} refl v tt = v
idk {µ = x₃ ⇒ x₄ , .∙} (refl , refl , refl) v k = k v tt

idt = ∙

-- mutual
--   ⟦_⟧v : {τ : typ} →  value[ ⟦_⟧τ ] τ →  ⟦ τ ⟧τ
--   ⟦ Var x ⟧v = x
--   ⟦ Num n ⟧v = n
--   ⟦ Fun τ₁ τ₂ e₁ ⟧v = λ v  → ⟦ e₁ v ⟧




--   ⟦_⟧ : {τ α β : typ}{µα µβ : trail} →  term[ ⟦_⟧τ ] τ ,⟨ µα ⟩, α ,⟨ µβ ⟩, β
--            → ( ⟦ τ ⟧τ →  ⟦ µα ⟧µ → ⟦ α ⟧τ ) → ⟦ µβ ⟧µ → ⟦ β ⟧τ
--   ⟦ Val v ⟧ k t = {!⟦ v ⟧v!}
--   ⟦ App e₁ e₂ ⟧ k t = ⟦ e₁ ⟧ (λ x → ⟦ e₂ ⟧ (λ y → x y k )) t
--   ⟦ Control x x₂ x₃ e ⟧ k t = ⟦ e (λ v k' t' → k v (append-trail x₃ t (cons-trail x₂ k' t'))) ⟧ (idk x) tt 
--   ⟦ Prompt _ _ β β' μᵢ _ x e ⟧ k t = k (⟦ e ⟧ (idk x) tt) t
  
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
            {e₁ : var τ₁ → var τ → term[ var ] τ₂ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β} →
            {v : value[ var ] τ₁} →
            {e₁′ : var τ → term[ var ] τ₂ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β} →
            ((x : var τ) → Subst (λ y → (e₁ y) x) v (e₁′ x)) →
            SubstVal (λ y → Fun τ₂ τ (e₁ y)) v (Fun τ₂ τ e₁′)
            -- SubstVal (λ y → Fun (e₁ y))
            --          v
            --          (Fun e₁′)
    
  data Subst {var : typ → Set} : {τ₁ τ₂ τ₃ τ₄ : typ}{μα μβ : trail} →
             (var τ₁ → term[ var ] τ₂ ,⟨ μα ⟩, τ₃ ,⟨ μβ ⟩, τ₄) →
             value[ var ] τ₁ →
             term[ var ] τ₂ ,⟨ μα ⟩, τ₃ ,⟨ μβ ⟩, τ₄ → Set where
             
     sVal  : {τ τ₁  : typ}{μα μβ : trail} →
             {v₁ : var τ → value[ var ] τ₁} →
             {v : value[ var ] τ} →
             {v₁′ : value[ var ] τ₁} →
             SubstVal v₁ v v₁′ →
             Subst {τ₃ = τ₁}{μα = μα}(λ y → Val (v₁ y)) v (Val v₁′)

             
     sApp  : {τ τ₁ τ₂ α β γ σ : typ}{μα μβ μγ μσ : trail} →
             {e₁ : var τ → term[ var ] (τ₂ ⇒ τ₁ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β) ,⟨ μγ ⟩, γ ,⟨ μσ ⟩, σ}
             {e₂ : var τ → term[ var ] τ₂ ,⟨ μβ ⟩, β ,⟨ μγ ⟩, γ}
             {v : value[ var ] τ}
             {e₁′ : term[ var ] (τ₂ ⇒ τ₁ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β) ,⟨ μγ ⟩, γ ,⟨ μσ ⟩, σ}
             {e₂′ : term[ var ] τ₂ ,⟨ μβ ⟩, β ,⟨ μγ ⟩, γ} →
             Subst e₁ v e₁′ → Subst e₂ v e₂′ →
             Subst (λ y → App (e₁ y) (e₂ y))
                   v
                   (App e₁′ e₂′)

     sCon : {τ t₁ t₂ τ₃ α β γ γ' : typ}{μ₀ μ₁ μ₂ μᵢ μα μβ : trail} →
            {e₁ : var τ₃ →
                  var (τ ⇒ t₁ ,⟨ μ₁ ⟩, t₂ ,⟨ μ₂ ⟩, α) →
                  term[ var ] γ ,⟨ μᵢ ⟩, γ' ,⟨ ∙ ⟩, β} →
            {v  : value[ var ] τ₃} →
            {e₁′ : var (τ ⇒ t₁ ,⟨ μ₁ ⟩, t₂ ,⟨ μ₂ ⟩, α) →
                  term[ var ] γ ,⟨ μᵢ ⟩, γ' ,⟨ ∙ ⟩, β} →
            {x : is-id-trail γ γ' μᵢ} →
            {x₂ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀} →
            {x₃ : compatible μβ μ₀ μα} →
            ((k : var (τ ⇒ t₁ ,⟨ μ₁ ⟩, t₂ ,⟨ μ₂ ⟩, α)) →
                 Subst (λ y → (e₁ y) k) v ((e₁′ k))) →
            Subst (λ y → Control x x₂ x₃ (e₁ y))
                  v
                  (Control x x₂ x₃ e₁′)


     sPro : {τ β β' γ τ₃ : typ}{μᵢ μα : trail} →
            {e₁ : var τ → term[ var ] β ,⟨ μᵢ ⟩, β' ,⟨ ∙ ⟩, γ} →
            {v : value[ var ] τ} →
            {e₁′ : term[ var ] β ,⟨ μᵢ ⟩, β' ,⟨ ∙ ⟩, γ} →
            {x : is-id-trail β β' μᵢ} →
            Subst e₁ v e₁′ →
            Subst {τ₃ = τ₃}{μα = μα} (λ y → Prompt x (e₁ y)) v
                  (Prompt  x e₁′)


  --frame
  data frame[_,_,⟨_⟩,_,⟨_⟩,_]_,⟨_⟩,_,⟨_⟩,_ (var : typ → Set)
       : typ → trail → typ → trail → typ → typ → trail → typ → trail → typ → Set where
    App₁ : {τ₁ τ₂ α β γ σ : typ}{μα μβ μγ μσ : trail} →
           (e₂ : term[ var ] τ₂ ,⟨ μβ ⟩, β ,⟨ μγ ⟩, γ) →
           frame[ var , (τ₂ ⇒ τ₁ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β) ,⟨ μγ ⟩, γ ,⟨ μσ ⟩, σ ]
                  τ₁ ,⟨ μα ⟩, α ,⟨ μσ ⟩, σ

    App₂ : {τ₁ τ₂ α β γ σ : typ}{μα μβ μγ μσ : trail} →
           (v₁ : value[ var ] (τ₂ ⇒ τ₁ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β)) →
           frame[ var , τ₂ ,⟨ μβ ⟩, β ,⟨ μγ ⟩, γ ]
                  τ₁ ,⟨ μα ⟩, α ,⟨ μγ ⟩, γ

    Pro  : {τ α β β' : typ}{μᵢ μα : trail} →
           (is-id-trail β β' μᵢ) →
           frame[ var , β ,⟨ μᵢ ⟩, β' ,⟨ ∙ ⟩, τ ] τ ,⟨ μα ⟩, α ,⟨ μα ⟩, α

  frame-plug : {var : typ → Set}
               {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μσ : trail} →
               frame[ var , τ₂ ,⟨ μα ⟩, τ₄ ,⟨ μβ ⟩, τ₅ ] τ₁ ,⟨ μγ ⟩, τ₃ ,⟨ μσ ⟩, τ₆ →
               term[ var ] τ₂ ,⟨ μα ⟩, τ₄ ,⟨ μβ ⟩, τ₅  →
               term[ var ] τ₁ ,⟨ μγ ⟩, τ₃ ,⟨ μσ ⟩, τ₆
  frame-plug (App₁ e₂) e₁ = App e₁ e₂
  frame-plug {μβ = μβ}(App₂ v₁) e₂ = App (Val v₁) e₂

  
  frame-plug {τ₁ = τ₁}{τ₂ = τ₂}{τ₃ = τ₃}{τ₄ = τ₄}{μα = μα}{μγ = μγ} (Pro x) e₁ =
             Prompt x e₁

                 
                 
       
  --frame
  data pframe[_,_,⟨_⟩,_,⟨_⟩,_]_,⟨_⟩,_,⟨_⟩,_ (var : typ → Set)
       : typ → trail → typ → trail → typ → typ → trail → typ → trail → typ → Set where
    App₁ : {τ₁ τ₂ α β γ σ : typ}{μα μβ μγ μσ : trail} →
           (e₂ : term[ var ] τ₂ ,⟨ μβ ⟩, β ,⟨ μγ ⟩, γ) →
           pframe[ var , (τ₂ ⇒ τ₁ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β) ,⟨ μγ ⟩, γ ,⟨ μσ ⟩, σ ]
                   τ₁ ,⟨ μα ⟩, α ,⟨ μσ ⟩, σ

    App₂ : {τ₁ τ₂ α β γ σ : typ}{μα μβ μγ : trail} →
           (v₁ : value[ var ] (τ₂ ⇒ τ₁ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β)) →
           pframe[ var , τ₂ ,⟨ μβ ⟩, β ,⟨ μγ ⟩, γ ]
                   τ₁ ,⟨ μα ⟩, α ,⟨ μγ ⟩, γ


  pframe-plug : {var : typ → Set}
               {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μσ : trail} →
               pframe[ var , τ₂ ,⟨ μα ⟩, τ₄ ,⟨ μβ ⟩, τ₅ ] τ₁ ,⟨ μγ ⟩, τ₃ ,⟨ μσ ⟩, τ₆ →
               term[ var ] τ₂ ,⟨ μα ⟩, τ₄ ,⟨ μβ ⟩, τ₅  →
               term[ var ] τ₁ ,⟨ μγ ⟩, τ₃ ,⟨ μσ ⟩, τ₆
 
  pframe-plug (App₁ e₂) e₁ = App e₁ e₂
  pframe-plug {μβ = μβ}(App₂ v₁) e₂ = App (Val v₁) e₂

  data same-pframe {var : typ → Set}{τ₇ τ₆  : typ}{μβ μσ : trail} :
                   {τ τ₅ τ₁ τ₃ τ' τ₅' : typ}{μα μα' μγ : trail} →
         pframe[ var , τ ,⟨ μα ⟩, τ₅ ,⟨ μβ ⟩, τ₆ ] τ₁ ,⟨ μγ ⟩, τ₃ ,⟨ μβ ⟩, τ₆  →
         pframe[ var , τ' ,⟨ μα' ⟩, τ₅' ,⟨ μσ ⟩, τ₇ ] τ₁ ,⟨ μγ ⟩, τ₃ ,⟨ μσ ⟩, τ₇  →
         Set where
   App₁ : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ}{μ₄ μ₅ μγ : trail} →
          (e₂ : term[ var ] τ₂ ,⟨ μ₄ ⟩, τ₄ ,⟨ μ₅ ⟩, τ₅) →
          same-pframe {τ₁ = τ₁}{τ₃ = τ₃}{μγ = μγ} (App₁ e₂) (App₁ e₂)
   App₂ : {α β τ₁ τ₂ σ : typ}{μα μβ : trail} →
          (v₁ : value[ var ] (τ₂ ⇒ τ₁ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β) ) →
          same-pframe  (App₂ {σ = σ} v₁) (App₂ {σ = σ} v₁)

  -- pure context
  data pcontext[_,_,⟨_⟩,_,⟨_⟩,_]_,⟨_⟩,_,⟨_⟩,_ (var : typ → Set)
       : typ → trail → typ → trail → typ → typ → trail → typ → trail → typ → Set where
   Hole : {τ₁ τ₂ τ₃ : typ}{μα μβ : trail} →
          pcontext[ var , τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μβ ⟩, τ₃ ] τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μβ ⟩, τ₃
   Frame : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ : typ}{μα μγ μσ μ₁ μ' : trail} →
           (f : pframe[ var , τ₄ ,⟨ μγ ⟩, τ₅ ,⟨ μ₁ ⟩, τ₃ ] τ₆ ,⟨ μσ ⟩, τ₇ ,⟨ μ₁ ⟩, τ₃ ) →
           (e : pcontext[ var , τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μ' ⟩, τ₃ ] τ₄ ,⟨ μγ ⟩, τ₅ ,⟨ μ₁ ⟩, τ₃ ) →
           pcontext[ var , τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μ' ⟩, τ₃ ] τ₆ ,⟨ μσ ⟩, τ₇ ,⟨ μ₁ ⟩, τ₃

  pcontext-plug : {var : typ → Set}
                  ({τ₁} τ₂ {τ₃ τ₄ τ₅} : typ){μα μβ μγ μ' : trail} →
                  pcontext[ var , τ₂ ,⟨ μβ ⟩, τ₄ ,⟨ μ' ⟩, τ₅ ] τ₁ ,⟨ μα ⟩, τ₃ ,⟨ μγ ⟩, τ₅ →
                  term[ var ] τ₂ ,⟨ μβ ⟩, τ₄ ,⟨ μ' ⟩, τ₅ →
                  term[ var ] τ₁ ,⟨ μα ⟩, τ₃ ,⟨ μγ ⟩, τ₅
  pcontext-plug τ₂ Hole e₁ = e₁
  pcontext-plug τ₂ (Frame f p) e₁ = pframe-plug f (pcontext-plug τ₂ p e₁)


  data same-pcontext {var : typ → Set} {τ₁ τ₂ τ₃ : typ} :
                     {τ₄ τ₆ τ₇ τ' : typ}{μα μβ μγ μ' μ₂ μ₃  : trail} →
                     pcontext[ var , τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μ₃ ⟩, τ₃ ] τ₄ ,⟨ μγ ⟩, τ₇ ,⟨ μβ ⟩, τ₃  →
                     pcontext[ var , τ₁ ,⟨ μ₂ ⟩, τ₂ ,⟨ μ₂ ⟩, τ₂ ] τ₆ ,⟨ μ' ⟩, τ' ,⟨ μ₂ ⟩, τ₂   →
                     Set where
       Hole  : {μα μβ μ' : trail} → same-pcontext {μα = μα}{μβ = μβ}{μ' = μ'}  Hole Hole
       Frame : {τ₄  τ₆ τ₇ τ' τ₈ τ₉  : typ}{μ₂ μ₃ μ₇ μα μβ μγ μ' : trail} →
               {f₁ : pframe[ var , τ₄ ,⟨ μγ ⟩, τ₇ ,⟨ μβ ⟩, τ₃ ] τ₉ ,⟨ μ₇ ⟩, τ₈ ,⟨ μβ ⟩, τ₃ } →
               {f₂ : pframe[ var , τ₆ ,⟨ μ' ⟩, τ' ,⟨ μ₂ ⟩, τ₂ ] τ₉ ,⟨ μ₇ ⟩, τ₈ ,⟨ μ₂ ⟩, τ₂ } →
               same-pframe  f₁ f₂ →
               {p₁ : pcontext[ var , τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μ₃ ⟩, τ₃ ] τ₄ ,⟨ μγ ⟩, τ₇ ,⟨ μβ ⟩, τ₃ } →
               {p₂ : pcontext[ var , τ₁ ,⟨ μ₂ ⟩, τ₂ ,⟨ μ₂ ⟩, τ₂ ] τ₆ ,⟨ μ' ⟩, τ' ,⟨ μ₂ ⟩, τ₂ } →
               same-pcontext p₁ p₂ →
               same-pcontext (Frame f₁ p₁) (Frame f₂ p₂)
 
               
    -- Hole  : same-pcontext Hole Hole
    -- Frame : {τ₄ τ₅ τ₆ τ₇ : typ} →
    --         {f₁ : pframe[ var , τ₄ cps[ τ₅ , τ₃ ]] τ₆
    --                     cps[ τ₇ , τ₃ ]} →
    --         {f₂ : pframe[ var , τ₄ cps[ τ₅ , τ₂ ]] τ₆
    --                     cps[ τ₇ , τ₂ ]} →
    --         same-pframe f₁ f₂ →
    --         {p₁ : pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
    --                       cps[ τ₅ , τ₃ ]} →
    --         {p₂ : pcontext[ var , τ₁ cps[ τ₂ , τ₂ ]] τ₄
    --                       cps[ τ₅ , τ₂ ]} →
    --         same-pcontext p₁ p₂ →
    --         same-pcontext (Frame f₁ p₁) (Frame f₂ p₂)
          
  -- reduction rules
  data Reduce {var : typ → Set} :
              {τ₁ τ₂ τ₃ : typ}{μα μβ : trail} →
              term[ var ] τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μβ ⟩, τ₃ →
              term[ var ] τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μβ ⟩, τ₃ → Set where
    RBeta   : {τ τ₁ τ₂ τ₃ : typ}{μα μβ : trail} →
              {e₁ : var τ → term[ var ] τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μβ ⟩, τ₃} →
              {v₂ : value[ var ] τ} →
              {e₁′ : term[ var ] τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μβ ⟩, τ₃} →
              Subst e₁ v₂ e₁′ →
              Reduce (App (Val (Fun τ₁ τ e₁)) (Val v₂)) e₁′

              
    RFrame  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μσ : trail} →
              {e₁ : term[ var ] τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μβ ⟩, τ₃} →
              {e₂ : term[ var ] τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μβ ⟩, τ₃} →
              (f : frame[ var , τ₁ ,⟨ μα ⟩, τ₂ ,⟨ μβ ⟩, τ₃ ]
                        τ₄ ,⟨ μγ ⟩, τ₅ ,⟨ μσ ⟩, τ₆) →
              Reduce e₁ e₂ →
              Reduce (frame-plug f e₁) (frame-plug f e₂)

    RPrompt : {τ₁ τ₂ β : typ}{μα μβ : trail} →
              {v₁ : value[ var ] β} →
              Reduce {τ₂ = τ₂}{μα = ∙}(Prompt refl (Val v₁)) (Val v₁)
 
                  
    RControl : {τ α β γ γ' t₁ t₂ τ₄ τ₁ τ₂ : typ}{μ₀ μ₁  μᵢ μα μβ μ₂ μ₃ μ₄ μ₅ : trail} →
              (p₁ : pcontext[ var , τ ,⟨ μα ⟩, α ,⟨ μβ ⟩, β ]
                             γ ,⟨ μᵢ ⟩, γ' ,⟨ ∙ ⟩, β ) →
              (p₂ : pcontext[ var , τ ,⟨ μ₂ ⟩, α ,⟨ μ₂ ⟩, α ]
                             t₁ ,⟨ μ₁ ⟩, t₂ ,⟨ μ₂ ⟩, α ) → -- μᵢとγを揃えなきゃならん
              (x₁ : is-id-trail γ γ' μᵢ) →
              (x₂ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
              (x₃ : compatible μβ μ₀ μα) →
              same-pcontext p₁ p₂ →
              (e : var (τ ⇒ t₁ ,⟨ μ₁ ⟩, t₂ ,⟨ μ₂ ⟩, α) → term[ var ] γ ,⟨ μᵢ ⟩, γ' ,⟨ ∙ ⟩, β) →
              Reduce {τ₂ = τ₂}{μα = μα}(Prompt x₁
                     (pcontext-plug τ p₁ (Control x₁ x₂ x₃ e)))
                     (Prompt x₁ (App (Val
                     (Fun γ (τ ⇒ t₁ ,⟨ μ₁ ⟩, t₂ ,⟨ μ₂ ⟩, α) e))
                     (Val (Fun t₁ τ λ x → pcontext-plug τ p₂ (Val (Var x))))))
    --           -- t₂はγ'で、μ₁はμᵢにしないといけなくなった (本来のeは var (τ ⇒ t₁ ,⟨ μ₁ ⟩, t₂ ,⟨ μ₂ ⟩, α))
    --           Reduce {τ₂ = τ₂}{μα = μα}(Prompt x₁
    --                  (pcontext-plug τ p₁ (Control x₁ x₂ x₃ e)))
    --                  (Prompt x₁ (App (Val
    --                  (Fun γ (τ ⇒ t₁ ,⟨ μ₁ ⟩, t₂ ,⟨ μβ ⟩, α) e))
    --                  (Val (Fun t₁ τ λ x → pcontext-plug τ p₂ (Val (Var x))))))
