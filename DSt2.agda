module DSt2 where

open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

infixr 5 _⇒_⟨_⟩_⟨_⟩_

mutual
  data typ : Set where
    Nat : typ
    Tbool : typ
    _⇒_⟨_⟩_⟨_⟩_ : {μα μβ : trail} →
                  (τ₂ τ₁ : typ) → (μs : trails[ μβ ] μα) → (α : typ) →
                  (μβ : trail) → (β : typ) → typ

  data trail : Set where
    ∙ : trail
    _⇒_,_ : (τ τ' : typ) → (μ : trail) → trail

  data trails[_]_ (μα : trail) : trail → Set where
    [] : trails[ μα ] μα
    _::⟨_⟩_ : {τ₁ τ₂ : typ} {μ μβ μγ : trail} →
              (μk : trail) → (c : compatible μk μβ μγ) →
              (μs : trails[ μα ] μβ) →
              trails[ μα ] μγ

  compatible : (μ₁ μ₂ μ₃ : trail) → Set
  compatible ∙ μ₂ μ₃ = μ₂ ≡ μ₃
  compatible (τ₁ ⇒ τ₁' , μ₁) ∙ μ₃ = (τ₁ ⇒ τ₁' , μ₁) ≡ μ₃
  compatible (τ₁ ⇒ τ₁' , μ₁) (τ₂ ⇒ τ₂' , μ₂) ∙ = ⊥
  compatible (τ₁ ⇒ τ₁' , μ₁) (τ₂ ⇒ τ₂' , μ₂) (τ₃ ⇒ τ₃' , μ₃) =
             (τ₁ ≡ τ₃) × (τ₁' ≡ τ₃') ×
             (compatible (τ₂ ⇒ τ₂' , μ₂) μ₃ μ₁)

compatible-equal : {μ₁ μ₂ μ₃ : trail} →
                   (c₁ c₂ : compatible μ₁ μ₂ μ₃) → c₁ ≡ c₂
compatible-equal {∙} refl refl = refl
compatible-equal {τ₁ ⇒ τ₁' , μ₁} {∙} refl refl = refl
compatible-equal {τ₁ ⇒ τ₁' , μ₁} {τ₂ ⇒ τ₂' , μ₂} {.τ₁ ⇒ .τ₁' , μ₃}
                 (refl , refl , c₁) (refl , refl , c₂)
  rewrite compatible-equal c₁ c₂ = refl

is-id-trail : (τ τ' : typ) → (μ : trail) → Set
is-id-trail τ τ' ∙ = τ ≡ τ'
is-id-trail τ τ' (τ₁ ⇒ τ₁' , μ) = (τ ≡ τ₁) × (τ' ≡ τ₁') × (μ ≡ ∙)

is-id-trails : {μα : trail} (τ τ' : typ) → (μs : trails[ ∙ ] μα) → Set
is-id-trails {μα} τ τ' μs = is-id-trail τ τ' μα

-- source term
mutual
  data value[_]_ (var : typ → Set) : (τ : typ) → Set where
    Var : {τ₁ : typ} → var τ₁ → value[ var ] τ₁
    Num : (n : ℕ) → value[ var ] Nat
    Fun : {τ₁ τ₂ α β : typ} {μα μβ : trail} {μs : trails[ μβ ] μα} →
          (e₁ : var τ₂ → term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
          value[ var ] (τ₂ ⇒ τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β)

  data term[_]_⟨_⟩_⟨_⟩_ (var : typ → Set) : (τ : typ) {μα μβ : trail} →
          (μs : trails[ μβ ] μα) → (α : typ) → (μβ : trail) → (β : typ) →
          Set where
    Val : {τ₁ α : typ} {μα : trail} →
          (v : value[ var ] τ₁) → term[ var ] τ₁ ⟨ []{μα} ⟩ α ⟨ μα ⟩ α
    App : {τ₁ τ₂ α β γ δ : typ} {μα μβ μγ μδ : trail}
          {μ[β]α : trails[ μβ ] μα} →
          {μ[γ]β : trails[ μγ ] μβ} →
          {μ[δ]γ : trails[ μδ ] μγ} →
          {μ[δ]α : trails[ μδ ] μα} →
          (e₁ : term[ var ] (τ₂ ⇒ τ₁ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β)
                            ⟨ μ[δ]γ ⟩ γ ⟨ μδ ⟩ δ) →
          (e₂ : term[ var ] τ₂ ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ) →
          term[ var ] τ₁ ⟨ μ[δ]α ⟩ α ⟨ μδ ⟩ δ
    Plus : {α β γ : typ} {μα μβ μγ : trail} →
           {μ[β]α : trails[ μβ ] μα} →
           {μ[γ]β : trails[ μγ ] μβ} →
           {μ[γ]α : trails[ μγ ] μα} →
           (e₁ : term[ var ] Nat ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ) →
           (e₂ : term[ var ] Nat ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β) →
           term[ var ] Nat ⟨ μ[γ]α ⟩ α ⟨ μγ ⟩ γ
    Control : {τ α β γ γ' t₁ t₂ : typ} {μ₀ μ₁ μ₂ μᵢ μα μβ : trail}
              {μsᵢ : trails[ ∙ ] μᵢ} →
              {μs₁ : trails[ μ₂ ] μ₁} →
              {μ[β]α : trails[ μβ ] μα} →
              (id : is-id-trails γ γ' μsᵢ) →
              (c₁ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
              (c₂ : compatible μβ μ₀ μα) →
              (e : var (τ ⇒ t₁ ⟨ μs₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
                   term[ var ] γ ⟨ μsᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
              term[ var ] τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β
    Prompt : {τ α β β' : typ} {μα μᵢ : trail} {μsᵢ : trails[ ∙ ] μᵢ} →
             (id : is-id-trails β β' μsᵢ) →
             (e : term[ var ] β ⟨ μsᵢ ⟩ β' ⟨ ∙ ⟩ τ) →
             term[ var ] τ ⟨ []{μα} ⟩ α ⟨ μα ⟩ α

mutual
  ⟦_⟧τ : (τ : typ) → Set
  ⟦ Nat ⟧τ = ℕ
  ⟦ Tbool ⟧τ = 𝔹
  ⟦ τ₂ ⇒ τ₁ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β ⟧τ =
    (v : ⟦ τ₂ ⟧τ) → (k : ⟦ τ₁ ⟧τ → ⟦ μ[β]α ⟧μs → ⟦ α ⟧τ) → (t : ⟦ μβ ⟧μ) →
    ⟦ β ⟧τ

  ⟦_⟧μ : (t : trail) → Set
  ⟦ ∙ ⟧μ = ⊤
  ⟦ τ ⇒ τ' , μ ⟧μ = (v : ⟦ τ ⟧τ) → (t : ⟦ μ ⟧μ) → ⟦ τ' ⟧τ

  ⟦_⟧μs : {μα μβ : trail} → (μs : trails[ μβ ] μα) → Set
  ⟦_⟧μs {μα} μs = ⟦ μα ⟧μ

cons-trail : {τ₁ τ₂ : typ}{μ μα μβ : trail} →
             (c : compatible (τ₁ ⇒ τ₂ , μ) μα μβ) →
             (k : ⟦ τ₁ ⇒ τ₂ , μ ⟧μ) → (t : ⟦ μα ⟧μ) → ⟦ μβ ⟧μ
cons-trail {μα = ∙} refl k tt = k
cons-trail {μα = τα ⇒ τα' , μα} {τβ ⇒ τβ' , μβ}
           (refl , refl , c) k k' =
  λ v t' → k v (cons-trail c k' t')

append-trail : {μα μβ μγ : trail} →
               (c : compatible μα μβ μγ) →
               (k : ⟦ μα ⟧μ) → (t : ⟦ μβ ⟧μ) → ⟦ μγ ⟧μ
append-trail {∙} refl tt t = t
append-trail {τα ⇒ τα' , μα} c k t = cons-trail c k t

idk : {τ₁ τ₂ : typ} {μ : trail} →
      is-id-trail τ₁ τ₂ μ → ⟦ τ₁ ⟧τ → ⟦ μ ⟧μ → ⟦ τ₂ ⟧τ
idk {μ = ∙} refl v tt = v
idk {μ = τ ⇒ τ' , .∙} (refl , refl , refl) v k = k v tt

idt = ∙

mutual
  ⟦_⟧v : {τ : typ} → (v : value[ ⟦_⟧τ ] τ) →  ⟦ τ ⟧τ
  ⟦ Var x ⟧v = x
  ⟦ Num n ⟧v = n
  ⟦ Fun e ⟧v = λ v  → ⟦ e v ⟧

  ⟦_⟧ : {τ α β : typ} {μα μβ : trail} {μ[β]α : trails[ μβ ] μα} →
        (e : term[ ⟦_⟧τ ] τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β) →
        (k : ⟦ τ ⟧τ →  ⟦ μα ⟧μ → ⟦ α ⟧τ) → (t : ⟦ μβ ⟧μ) → ⟦ β ⟧τ
  ⟦ Val v ⟧ k t = k ⟦ v ⟧v t
  ⟦ App e₁ e₂ ⟧ k t = ⟦ e₁ ⟧ (λ v₁ → ⟦ e₂ ⟧ (λ v₂ → v₁ v₂ k)) t
  ⟦ Plus e₁ e₂ ⟧ k t = ⟦ e₁ ⟧ (λ v₁ → ⟦ e₂ ⟧ (λ v₂ → k (v₁ + v₂))) t
  ⟦ Control id c₁ c₂ e ⟧ k t =
    ⟦ e (λ v k' t' → k v (append-trail c₂ t (cons-trail c₁ k' t'))) ⟧
    (idk id) tt
  ⟦ Prompt id e ⟧ k t = k (⟦ e ⟧ (idk id) tt) t

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
    sFun  : {τ τ₁ τ₂ α β : typ} {μα μβ : trail} {μs : trails[ μβ ] μα} →
            {e₁ : var τ → var τ₂ → term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
            {v : value[ var ] τ} →
            {e₁′ : var τ₂ → term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
            ((x : var τ₂) → Subst (λ y → (e₁ y) x) v (e₁′ x)) →
            SubstVal (λ y → Fun (e₁ y)) v (Fun e₁′)

  data Subst {var : typ → Set} : {τ τ₁ α β : typ}{μα μβ : trail} {μs : trails[ μβ ] μα} →
             (var τ → term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
             value[ var ] τ →
             term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β → Set where

     sVal  : {τ τ₁ τ₃ : typ}{μα : trail} →
             {v₁ : var τ → value[ var ] τ₁} →
             {v : value[ var ] τ} →
             {v₁′ : value[ var ] τ₁} →
             SubstVal v₁ v v₁′ →
             Subst{α = τ₃}{μα = μα} (λ z → Val (v₁ z)) v (Val v₁′)

     sApp  : {τ τ₁ τ₂ α β γ δ : typ} {μα μβ μγ μδ : trail}
             {μ[β]α : trails[ μβ ] μα} →
             {μ[γ]β : trails[ μγ ] μβ} →
             {μ[δ]γ : trails[ μδ ] μγ} →
             {μ[δ]α : trails[ μδ ] μα} →
             {e₁ : var τ → term[ var ] (τ₂ ⇒ τ₁ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β)
                            ⟨ μ[δ]γ ⟩ γ ⟨ μδ ⟩ δ}
             {e₂ : var τ → term[ var ] τ₂ ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ}
             {v : value[ var ] τ}
             {e₁′ : term[ var ] (τ₂ ⇒ τ₁ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β)
                            ⟨ μ[δ]γ ⟩ γ ⟨ μδ ⟩ δ}
             {e₂′ : term[ var ] τ₂ ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ} →
             Subst e₁ v e₁′ → Subst e₂ v e₂′ →
             Subst{μs = μ[δ]α} (λ y → App (e₁ y) (e₂ y))
                   v
                   (App e₁′ e₂′)

     sPlu : {τ α β γ : typ} {μα μβ μγ : trail} →
            {μ[β]α : trails[ μβ ] μα} →
            {μ[γ]β : trails[ μγ ] μβ} →
            {μ[γ]α : trails[ μγ ] μα} →
            {e₁ : var τ → term[ var ] Nat ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ}
            {e₂ : var τ → term[ var ] Nat ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β}
            {v : value[ var ] τ}
            {e₁′ : term[ var ] Nat ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ }
            {e₂′ : term[ var ] Nat ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β  } →
            Subst e₁ v e₁′ → Subst e₂ v e₂′ →
            Subst{μs = μ[γ]α} (λ y → Plus (e₁ y) (e₂ y)) v (Plus e₁′ e₂′)



     sCon : {τ₃ τ α β γ γ' t₁ t₂ : typ} {μ₀ μ₁ μ₂ μᵢ μα μβ : trail}
            {μsᵢ : trails[ ∙ ] μᵢ} →
            {μs₁ : trails[ μ₂ ] μ₁} →
            {μ[β]α : trails[ μβ ] μα} →
            {id : is-id-trails γ γ' μsᵢ} →
            {c₁ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀} →
            {c₂ : compatible μβ μ₀ μα} →
            {e₁ : var τ₃ →
                  var (τ ⇒ t₁ ⟨ μs₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
                   term[ var ] γ ⟨ μsᵢ ⟩ γ' ⟨ ∙ ⟩ β} →
            {v : value[ var ] τ₃} →
            {e₁′ : var (τ ⇒ t₁ ⟨ μs₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
                   term[ var ] γ ⟨ μsᵢ ⟩ γ' ⟨ ∙ ⟩ β} →
            ((k : var (τ ⇒ t₁ ⟨ μs₁ ⟩ t₂ ⟨ μ₂ ⟩ α)) →
                 Subst (λ y → (e₁ y) k) v ((e₁′ k))) →
            Subst{μs = μ[β]α} (λ y → Control id c₁ c₂ (e₁ y))
                  v
                  (Control id c₁ c₂ e₁′)

     sPro : {τ₁ τ β β' α : typ} {μα μᵢ : trail} {μsᵢ : trails[ ∙ ] μᵢ} →
            {id : is-id-trails β β' μsᵢ} →
            {e₁ : var τ₁ → term[ var ] β ⟨ μsᵢ ⟩ β' ⟨ ∙ ⟩ τ} →
            {v : value[ var ] τ₁} →
            {e₁′ : term[ var ] β ⟨ μsᵢ ⟩ β' ⟨ ∙ ⟩ τ} →
            Subst e₁ v e₁′ →
            Subst {α = α}{μα = μα} (λ y → Prompt id (e₁ y)) v
                  (Prompt id e₁′)


data frame[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : typ → Set)
     : (τ : typ) {μα μβ : trail} → (μs : trails[ μβ ] μα) → (α : typ) → (μβ : trail) → (β : typ) →
       (τ₂ : typ) {μα₂ μβ₂ : trail} → (μs₂ : trails[ μβ₂ ] μα₂) → (α₂ : typ) → (μβ₂ : trail) → (β₂ : typ) →
       Set where
       
     --typ → trails[_]_ → typ → trail → typ → typ → trails → typ → trail → typ → Set where
  App₁ : {τ₁ τ₂ α β γ δ : typ} {μα μβ μγ μδ : trail}
         {μ[β]α : trails[ μβ ] μα} →
         {μ[γ]β : trails[ μγ ] μβ} →
         {μ[δ]γ : trails[ μδ ] μγ} →
         {μ[δ]α : trails[ μδ ] μα} →
         (e₂ : term[ var ] τ₂ ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ) →
         frame[ var , (τ₂ ⇒ τ₁ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β) ⟨ μ[δ]γ ⟩ γ ⟨ μδ ⟩ δ ]
                τ₁ ⟨ μ[δ]α ⟩ α ⟨ μδ ⟩ δ

  App₂ : {τ₁ τ₂ α β γ δ : typ} {μα μβ μγ μδ : trail}
         {μ[β]α : trails[ μβ ] μα} →
         {μ[γ]β : trails[ μγ ] μβ} →
         {μ[δ]γ : trails[ μδ ] μγ} →
         {μ[δ]α : trails[ μδ ] μα} →
         (v₁ : value[ var ] (τ₂ ⇒ τ₁ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β)) →
         frame[ var , τ₂ ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ ]
                τ₁ ⟨ μ[β]α ⟩ α ⟨ μγ ⟩ γ

  Plus₁ : {α β γ : typ} {μα μβ μγ : trail} →
          {μ[β]α : trails[ μβ ] μα} →
          {μ[γ]β : trails[ μγ ] μβ} →
          {μ[γ]α : trails[ μγ ] μα} →
          (e₂ : term[ var ] Nat ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β) →
          frame[ var , Nat ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ ] Nat ⟨ μ[γ]α ⟩ α ⟨ μγ ⟩ γ

  Plus₂ : {α β γ : typ} {μα μβ μγ : trail} →
          {μ[β]α : trails[ μβ ] μα} →
          {μ[γ]α : trails[ μγ ] μα} →
          (v₁ : value[ var ] Nat) →
          frame[ var , Nat ⟨ μ[β]α ⟩ α ⟨ μγ ⟩ γ ] Nat ⟨ μ[γ]α ⟩ α ⟨ μγ ⟩ γ
            

  Pro  : {τ α β β' : typ} {μα μᵢ : trail} {μsᵢ : trails[ ∙ ] μᵢ} →
         (id : is-id-trails β β' μsᵢ) →
         frame[ var , β ⟨ μsᵢ ⟩ β' ⟨ ∙ ⟩ τ ] τ ⟨ []{μα} ⟩ α ⟨ μα ⟩ α

frame-plug : {var : typ → Set}
             {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μδ : trail}
             {μs : trails[ μβ ] μα}{μt : trails[ μδ ] μγ} →
             frame[ var , τ₂ ⟨ μs ⟩ τ₄ ⟨ μβ ⟩ τ₅ ] τ₁ ⟨ μt ⟩ τ₃ ⟨ μδ ⟩ τ₆ →
             term[ var ] τ₂ ⟨ μs ⟩ τ₄ ⟨ μβ ⟩ τ₅ →
             term[ var ] τ₁ ⟨ μt ⟩ τ₃ ⟨ μδ ⟩ τ₆
frame-plug (App₁ e₂) e₁ = App e₁ e₂
frame-plug {μβ = μβ}(App₂ v₁) e₂ = App (Val v₁) e₂
frame-plug (Plus₁ e₂) e₁ = Plus e₁ e₂
frame-plug (Plus₂ v₁) e₂ = Plus (Val v₁) e₂

frame-plug {τ₁ = τ₁}{τ₂ = τ₂}{τ₃ = τ₃}{τ₄ = τ₄}{μα = μα}{μγ = μγ} (Pro x) e₁ =
           Prompt x e₁

  --frame
data pframe[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : typ → Set)
     : (τ : typ) {μα μβ : trail} → (μs : trails[ μβ ] μα) → (α : typ) → (μβ : trail) → (β : typ) →
       (τ₂ : typ) {μα₂ μβ₂ : trail} → (μs₂ : trails[ μβ₂ ] μα₂) → (α₂ : typ) → (μβ₂ : trail) → (β₂ : typ) → Set where
       
  App₁ : {τ₁ τ₂ α β γ δ : typ} {μα μβ μγ μδ : trail}
         {μ[β]α : trails[ μβ ] μα} →
         {μ[γ]β : trails[ μγ ] μβ} →
         {μ[δ]γ : trails[ μδ ] μγ} →
         {μ[δ]α : trails[ μδ ] μα} →
         (e₂ : term[ var ] τ₂ ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ) →
         pframe[ var , (τ₂ ⇒ τ₁ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β) ⟨ μ[δ]γ ⟩ γ ⟨ μδ ⟩ δ ]
                τ₁ ⟨ μ[δ]α ⟩ α ⟨ μδ ⟩ δ

  App₂ : {τ₁ τ₂ α β γ : typ} {μα μβ μγ  : trail}
         {μ[β]α : trails[ μβ ] μα} →
         {μ[γ]β : trails[ μγ ] μβ} →
         (v₁ : value[ var ] (τ₂ ⇒ τ₁ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β)) →
         pframe[ var , τ₂ ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ ]
                τ₁ ⟨ μ[β]α ⟩ α ⟨ μγ ⟩ γ

  Plus₁ : {α β γ : typ} {μα μβ μγ : trail} →
          {μ[β]α : trails[ μβ ] μα} →
          {μ[γ]β : trails[ μγ ] μβ} →
          {μ[γ]α : trails[ μγ ] μα} →
          (e₂ : term[ var ] Nat ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β) →
          pframe[ var , Nat ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ ] Nat ⟨ μ[γ]α ⟩ α ⟨ μγ ⟩ γ

  Plus₂ : {α γ : typ} {μα μβ μγ : trail} →
          {μ[β]α : trails[ μβ ] μα} →
          {μ[γ]α : trails[ μγ ] μα} →
          (v₁ : value[ var ] Nat) →
          pframe[ var , Nat ⟨ μ[β]α ⟩ α ⟨ μγ ⟩ γ ] Nat ⟨ μ[γ]α ⟩ α ⟨ μγ ⟩ γ

pframe-plug : {var : typ → Set}
              {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μδ : trail}
              {μs : trails[ μβ ] μα}{μt : trails[ μδ ] μγ} →
              pframe[ var , τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μt ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
              term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
              term[ var ] τ₄ ⟨ μt ⟩ τ₅ ⟨ μδ ⟩ τ₆

pframe-plug (App₁ e₂) e₁ = App e₁ e₂
pframe-plug (App₂ v₁) e₂ = App (Val v₁) e₂
pframe-plug (Plus₁ e₂) e₁ = Plus e₁ e₂
pframe-plug (Plus₂ v₁) e₂ = Plus (Val v₁) e₂


data same-pframe {var : typ → Set}:
                 {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : typ}
                 {μα μα' μβ μβ' μγ μγ' μδ μδ' : trail}
                 {μs : trails[ μβ ] μα}{μs' : trails[ μβ' ] μα'}
                 {μt : trails[ μδ ] μγ}{μt' : trails[ μδ' ] μγ'} →
       pframe[ var , τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μt ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
       pframe[ var , τ₁' ⟨ μs' ⟩ τ₂' ⟨ μβ' ⟩ τ₃' ] τ₄' ⟨ μt' ⟩ τ₅' ⟨ μδ' ⟩ τ₆' →
       Set where
 -- App₁ : {τ β γ τ₂ τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' : typ}{μ₁ μ₂ μβ μβ' μγ μγ' : trail}
 --        {μs : trails[ μβ ] μγ}{μs' : trails[ μβ' ] μγ}{μt : trails[ μβ ] μγ}{μt' : trails[ μβ' ] μγ'}
 --        {μ[β]α : trails[ μβ ] μγ'}
 --        {μ[γ]β : trails[ μγ ] μβ} →
 --        (e₂ : term[ var ] τ₂ ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ) →
 --        same-pframe {τ₃ = τ₃}{τ₃'}{τ₄}{τ₄'}{τ₅}{τ₅'}{μβ = μβ}{μβ'}{μγ}{μγ'}
 --                    {μs = μs}{μs' = μs'}{μt = μt}{μt' = μt'}
 --                    (App₁ {μ[β]α = μt} e₂) (App₁ {μ[β]α = μ[β]α}  e₂)

 App₁ : {τ β γ τ₂ τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' : typ}{μ₁ μ₂ μβ μβ' μγ μγ' : trail}
        {μ[β]γ : trails[ μβ ] μγ}{μ[β']γ : trails[ μβ' ] μγ}{μ[β']γ' : trails[ μβ' ] μγ'}
        {μ[β]γ' : trails[ μβ ] μγ'}
        {μ[γ]β : trails[ μγ ] μβ} →
        (e₂ : term[ var ] τ₂ ⟨ μ[γ]β ⟩ β ⟨ μγ ⟩ γ) →
        same-pframe {τ₃ = τ₃}{τ₃'}{τ₄}{τ₄'}{τ₅}{τ₅'}{μβ = μβ}{μβ'}{μγ}{μγ'}
                    {μs = μ[β]γ}{μs' = μ[β']γ}{μt = μ[β]γ}{μt' = μ[β']γ'}
                    (App₁{μ[β]α = μ[β]γ} e₂) (App₁{μ[β]α = μ[β]γ'} e₂)


 App₂ : {τ₁ τ₂ α β τ₃ τ₃' δ : typ}{μα μ₁ μ₂ μβ μβ' μδ : trail}
        {μ[β]α : trails[ μβ ] μα}{μs : trails[ μβ ] μβ} →
        (v₁ : value[ var ] (τ₂ ⇒ τ₁ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β )) →
        same-pframe {τ₃ = τ₃}{τ₃' = τ₃'}{μs = μs}{μs' = μs} (App₂  v₁) (App₂ v₁)

 Plus₁ : {α β γ τ₃ τ₃' : typ} {μα μβ μγ μβ' : trail}
         {μ[β]α : trails[ μβ ] μα}{μs : trails[ μβ ] μβ}{μs' : trails[ μβ' ] μβ}
         {μt : trails[ μβ ] μα}{μt' : trails[ μβ' ] μα} →
         (e₂ : term[ var ] Nat ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β) →
         same-pframe {τ₃ = τ₃}{τ₃'}{μβ = μβ}{μβ'}{μs = μs}{μs' = μs'}{μt = μt}{μt' = μt'} (Plus₁ e₂) (Plus₁ e₂)

 Plus₂ : {τ₂ τ₂' τ₃ τ₃' : typ} {μα μα' μβ μβ' : trail}
         {μs : trails[ μβ ] μα}{μs' : trails[ μβ' ] μα'}
         {μt : trails[ μβ ] μα}{μt' : trails[ μβ' ] μα'} →
         (v₁ : value[ var ] Nat) →
         same-pframe {τ₂ = τ₂}{τ₂'}{τ₃}{τ₃'}{μα = μα}{μα'}{μβ}{μβ'}
                     {μs = μs}{μs' = μs'}{μt = μt}{μt' = μt'} (Plus₂ v₁) (Plus₂ v₁)



data pcontext[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : typ → Set)
     : (τ : typ) {μα μβ : trail} → (μs : trails[ μβ ] μα) → (α : typ) → (μβ : trail) → (β : typ) →
       (τ₂ : typ) {μα₂ μβ₂ : trail} → (μs₂ : trails[ μβ₂ ] μα₂) → (α₂ : typ) → (μβ₂ : trail) → (β₂ : typ) → Set where
       
  Hole : {τ₁ τ₂ τ₃ : typ}{μα μβ : trail}{μs : trails[ μβ ] μα} →
         pcontext[ var , τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃
  Frame : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ : typ}{μ₁ μ₂ μα μβ μγ μδ : trail}
          {μs : trails[ μβ ] μα}{μt : trails[ μδ ] μγ}{μu : trails[ μ₁ ] μ₂} →
          (f : pframe[ var , τ₄ ⟨ μs ⟩ τ₅ ⟨ μβ ⟩ τ₆ ] τ₇ ⟨ μu ⟩ τ₈ ⟨ μ₁ ⟩ τ₉ ) →
          (c : pcontext[ var , τ₁ ⟨ μt ⟩ τ₂ ⟨ μδ ⟩ τ₃ ] τ₄ ⟨ μs ⟩ τ₅ ⟨ μβ ⟩ τ₆ ) →
          pcontext[ var , τ₁ ⟨ μt ⟩ τ₂ ⟨ μδ ⟩ τ₃ ] τ₇ ⟨ μu ⟩ τ₈ ⟨ μ₁ ⟩ τ₉

pcontext-plug : {var : typ → Set}
                {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μδ : trail}
                {μs : trails[ μβ ] μα}{μt : trails[ μδ ] μγ} →
                pcontext[ var , τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μt ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
                term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
                term[ var ] τ₄ ⟨ μt ⟩ τ₅ ⟨ μδ ⟩ τ₆
pcontext-plug Hole e₁ = e₁
pcontext-plug (Frame f p) e₁ = pframe-plug f (pcontext-plug p e₁)

data same-pcontext {var : typ → Set} :
                   {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : typ}
                   {μα μα' μβ μβ' μγ μγ' μδ μδ' : trail}
                   {μs : trails[ μβ ] μα}{μs' : trails[ μβ' ] μα'}
                   {μt : trails[ μδ ] μγ}{μt' : trails[ μδ' ] μγ'} →
                   pcontext[ var , τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μt ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
                   pcontext[ var , τ₁' ⟨ μs' ⟩ τ₂' ⟨ μβ' ⟩ τ₃' ] τ₄' ⟨ μt' ⟩ τ₅' ⟨ μδ' ⟩ τ₆' →
                   Set where
     Hole  : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' : typ}{μα μα' μβ μβ' : trail}
             {μs : trails[ μβ ] μα}{μs' : trails[ μβ' ] μα'} →
             same-pcontext {τ₁ = τ₁}{τ₁' = τ₁'}{τ₂ = τ₂}{τ₂' = τ₂'}{τ₃ = τ₃}{τ₃' = τ₃'}
                           {μα = μα}{μα' = μα'}{μβ = μβ}{μβ' = μβ'}{μs = μs}{μs' = μs'}
                           Hole Hole
     Frame : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' τ₇ τ₇' τ₈' τ₈ τ₉ τ₉' : typ}
             {μ₁ μ₁' μ₂ μ₂' μ₃ μ₃' μ₄ μ₄' μ₅ μ₅' μ₆ μ₆' : trail}
             {μs : trails[ μ₄ ] μ₃}{μt : trails[ μ₆ ] μ₅}
             {μs' : trails[ μ₄' ] μ₃'}{μt' : trails[ μ₆' ] μ₅'}
             {μu : trails[ μ₂ ] μ₁}{μu' : trails[ μ₂' ] μ₁'} →
             {f₁ : pframe[ var , τ₄ ⟨ μs ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ ] τ₇ ⟨ μt ⟩ τ₈ ⟨ μ₆ ⟩ τ₉ } →
             {f₂ : pframe[ var , τ₄' ⟨ μs' ⟩ τ₅' ⟨ μ₄' ⟩ τ₆' ] τ₇' ⟨ μt' ⟩ τ₈' ⟨ μ₆' ⟩ τ₉' } →
             same-pframe f₁ f₂ →
             {c₁ : pcontext[ var , τ₁ ⟨ μu ⟩ τ₂ ⟨ μ₂ ⟩ τ₃ ] τ₄ ⟨ μs ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ } →
             {c₂ : pcontext[ var , τ₁' ⟨ μu' ⟩ τ₂' ⟨ μ₂' ⟩ τ₃' ] τ₄' ⟨ μs' ⟩ τ₅' ⟨ μ₄' ⟩ τ₆' } →
             same-pcontext c₁ c₂ →
             same-pcontext (Frame f₁ c₁) (Frame f₂ c₂)


data Reduce {var : typ → Set} :
            {τ₁ τ₂ τ₃ : typ}{μα μβ : trail}{μs : trails[ μβ ] μα} →
            term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
            term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ → Set where
  RBeta   : {τ τ₁ τ₂ τ₃ : typ}{μα μβ : trail}{μs : trails[ μβ ] μα} →
            {e₁ : var τ → term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃} →
            {v₂ : value[ var ] τ} →
            {e₁′ : term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃} →
            Subst e₁ v₂ e₁′ →
            Reduce (App (Val (Fun e₁)) (Val v₂)) e₁′

  RPlus   : {τ₂ : typ}{μα : trail} →
            {n₁ : ℕ} →
            {n₂ : ℕ} →
            Reduce {τ₂ = τ₂}{μα = μα} (Plus (Val (Num n₁)) (Val (Num n₂))) (Val (Num (n₁ + n₂)))

  RFrame  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ}{μα μβ μγ μδ : trail}
            {μs : trails[ μβ ] μα}{μt : trails[ μδ ] μγ} →
            {e₁ : term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃} →
            {e₂ : term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃} →
            (f : frame[ var , τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ ]
                      τ₄ ⟨ μt ⟩ τ₅ ⟨ μδ ⟩ τ₆) →
            Reduce e₁ e₂ →
            Reduce (frame-plug f e₁) (frame-plug f e₂)

  RPrompt : {τ₂ β : typ}{μα : trail} →
            {v₁ : value[ var ] β} →
            Reduce {τ₂ = τ₂}{μα = μα}(Prompt refl (Val v₁)) (Val v₁)

    
  -- RControl : {τ τ₁ τ₂ α β γ γ' t₁ t₂ α' : typ} {μ₀ μ₁ μ₃ μᵢ μα μβ μα' : trail}
  --            {μ[α]α : trails[ μα' ] μα'} → 
  --            {μ[∙]μ₃ : trails[ ∙ ] μ₃} →
  --            {μ[μ₀]μ₃ : trails[ μ₀ ] μ₃} →  
  --            {μ[β]α : trails[ μβ ] μα} →
  --            {μ[∙]μᵢ : trails[ ∙ ] μᵢ} →
  --            (p₁ : pcontext[ var , τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β ]
  --                           τ₁ ⟨ μ[∙]μ₃ ⟩ τ₂ ⟨ ∙ ⟩ β ) →
  --            (p₂ : pcontext[ var , τ ⟨ []{μα'} ⟩ α' ⟨ μα' ⟩ α' ]
  --                           τ₁ ⟨ μ[μ₀]μ₃ ⟩ τ₂ ⟨ μ₀ ⟩ α ) →
  --            {id₀ : is-id-trails τ₁ τ₂ μ[∙]μ₃} →
  --            (id : is-id-trails γ γ' μ[∙]μᵢ) →
  --            (c₁ : compatible (τ₁ ⇒ τ₂ , μ₃) μ₀ μ₀) →
  --            (c₂ : compatible μβ μ₀ μα) →
  --            same-pcontext p₁ p₂ →
  --            (e : var (τ ⇒ τ₁ ⟨ μ[μ₀]μ₃ ⟩ τ₂ ⟨ μ₀ ⟩ α) →
  --                  term[ var ] γ ⟨ μ[∙]μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
  --             Reduce {τ₂ = τ₂}{μα = μα} (Prompt id₀
  --                   (pcontext-plug p₁ (Control id c₁ c₂ e)))
  --                   (Prompt{μsᵢ = μ[∙]μᵢ} id (App (Val (Fun e))
  --                   (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))))
             

  RControl : {τ α α' β β' γ γ' t₁ t₂ τ₁ τ₂ τ₃ τ₄ τ₅ : typ}
             {μ₀ μ₁ μᵢ μα μα' μβ μβ' μ₂ μ₃ μ₄ μ₅ : trail} →
             {μ[β]α : trails[ μβ ] μα} →
             {μ[∙]μ₃ : trails[ ∙ ] μ₃} →
             {μ[μ₂]μ₁ : trails[ μ₂ ] μ₁} →
             {μ[∙]μᵢ : trails[ ∙ ] μᵢ} →
              (p₁ : pcontext[ var , τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β ]
                             τ₁ ⟨ μ[∙]μ₃ ⟩ τ₂ ⟨ ∙ ⟩ β ) →
              (p₂ : pcontext[ var , τ ⟨ []{μα'} ⟩ α' ⟨ μα' ⟩ α' ]
                             t₁ ⟨ μ[μ₂]μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α ) →
              {id₀ : is-id-trails τ₁ τ₂ μ[∙]μ₃} →
              (id : is-id-trails γ γ' μ[∙]μᵢ) →
              (c₁ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
              (c₂ : compatible μβ μ₀ μα) →
              same-pcontext p₁ p₂ →
              (e : var (τ ⇒ t₁ ⟨ μ[μ₂]μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) → term[ var ] γ ⟨ μ[∙]μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
              Reduce {τ₂ = τ₂}{μα = μα} (Prompt id₀
                     (pcontext-plug p₁ (Control id c₁ c₂ e)))
                     (Prompt{μsᵢ = μ[∙]μᵢ} id (App (Val (Fun e))
                     (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))))
                     
-- RControl : {τ τ₁ τ₂ α β γ γ' t₁ t₂ α' : typ} {μ₀ μ₁ μ₂ μᵢ μα μβ μα' : trail}
--              {μ[α]α : trails[ μα' ] μα'} → 
--              {μsᵢ : trails[ ∙ ] μᵢ} →
--              {μs₁ : trails[ μ₂ ] μ₁} →  
--              {μ[β]α : trails[ μβ ] μα} →
--              (p₁ : pcontext[ var , τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β ]
--                             τ₁ ⟨ μsᵢ ⟩ τ₂ ⟨ ∙ ⟩ β ) →
--              (p₂ : pcontext[ var , τ ⟨ [] ⟩ α' ⟨ μα' ⟩ α' ]
--                             t₁ ⟨ μs₁ ⟩ t₂ ⟨ μ₂ ⟩ α ) →
--              {id₀ : is-id-trails τ₁ τ₂ μsᵢ} →
--              (id : is-id-trails γ γ' μsᵢ) →
--              (c₁ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
--              (c₂ : compatible μβ μ₀ μα) →
--              same-pcontext p₁ p₂ →
--              (e : var (τ ⇒ t₁ ⟨ μs₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
--                    term[ var ] γ ⟨ μsᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
--               Reduce {τ₂ = τ₂}{μα = μα} (Prompt id₀
--                     (pcontext-plug p₁ (Control id c₁ c₂ e)))
--                     (Prompt{μsᵢ = μsᵢ} id (App (Val (Fun e))
--                     (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))))


data Reduce* {var : typ → Set} :
             {τ₁ τ₂ τ₃ : typ}{μα μβ : trail}{μs : trails[ μβ ] μα} →
             term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
             term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ → Set where

  R*Id    : {τ₁ τ₂ τ₃ : typ}{μα μβ : trail}{μs : trails[ μβ ] μα} →
            (e : term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃ ) →
            Reduce* e e
  R*Trans : {τ₁ τ₂ τ₃ : typ}{μα μβ : trail}{μs : trails[ μβ ] μα} →
            (e₁ : term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃) →
            (e₂ : term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃) →
            (e₃ : term[ var ] τ₁ ⟨ μs ⟩ τ₂ ⟨ μβ ⟩ τ₃) →
            Reduce e₁ e₂ →
            Reduce* e₂ e₃ →
            Reduce* e₁ e₃

