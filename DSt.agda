module DSt where

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
    _⇒_⟨_⟩_⟨_⟩_ : typ → typ → trail → typ → trail → typ → typ

  data trail : Set where
    ∙ : trail
    _⇒_,_ : typ → typ → trail → trail

compatible : trail → trail → trail → Set
compatible ∙ μ₂ μ₃ = μ₂ ≡ μ₃
compatible (τ₁ ⇒ τ₁' , μ₁) ∙ μ₃ = (τ₁ ⇒ τ₁' , μ₁) ≡ μ₃
compatible (τ₁ ⇒ τ₁' , μ₁) (τ₂ ⇒ τ₂' , μ₂) ∙ = ⊥
compatible (τ₁ ⇒ τ₁' , μ₁) (τ₂ ⇒ τ₂' , μ₂) (τ₃ ⇒ τ₃' , μ₃) =
           (τ₁ ≡ τ₃) × (τ₁' ≡ τ₃') ×
           (compatible (τ₂ ⇒ τ₂' , μ₂) μ₃ μ₁)

compatible-equal : {μ₁ μ₂ μ₃ : trail} → (c₁ c₂ : compatible μ₁ μ₂ μ₃) → c₁ ≡ c₂
compatible-equal {∙} refl refl = refl
compatible-equal {x ⇒ x₁ , μ₁} {∙} refl refl = refl
compatible-equal {x ⇒ x₁ , μ₁} {x₂ ⇒ x₃ , μ₂} {x₄ ⇒ x₅ , μ₃} (refl , refl , c₁) (refl , refl , c₂)
  rewrite compatible-equal c₁ c₂  = refl

is-id-trail : typ → typ → trail → Set
is-id-trail τ τ' ∙ = τ ≡ τ'
is-id-trail τ τ' (τ₁ ⇒ τ₁' , μ) = (τ ≡ τ₁) × (τ' ≡ τ₁') × (μ ≡ ∙)

-- mutual
--   c-type : typ → Set
--   c-type Nat = ⊤
--   c-type Tbool = ⊤
--   c-type (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β ) =
--     --c-type β → c-trail μβ →
--     --c-type τ₂ × c-type τ₁ × c-type α × c-trail μα ×
--     c-type τ₁ × ((μ : trail) → compatible μ μβ μβ → compatible μ μα μα)

--   c-trail : trail → Set
--   c-trail ∙ = ⊤
--   c-trail (τ ⇒ τ' , μ ) = c-type τ × c-trail μ × c-type τ'



-- source term
mutual
  data value[_]_ (var : typ → Set) : typ → Set where
    Var : {τ₁ : typ} → var τ₁ → value[ var ] τ₁
    Num : (n : ℕ) → value[ var ] Nat
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


    Control : {τ α β γ γ' t₁ t₂ : typ}{μ₀ μ₁ μ₂ μᵢ μα μβ : trail} →
             (is-id-trail γ γ' μᵢ) →
             (compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
             (compatible μβ μ₀ μα) →
             --(c : (τ ⇒ t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α)) →
             (e : var (τ ⇒ t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
             term[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
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


-- mutual
--   c-value : {τ : typ} → value[ c-type ] τ → c-type τ
--   c-value (Var x) = x
--   c-value (Num n) = tt
--   c-value (Fun cτ₂ e)  = {!!}

--   c-term : {τ α β : typ} {μα μβ : trail} →
--             term[ c-type ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
--             c-type α →
--             --c-type β → c-trail μβ →
--             c-type τ ×  c-type β ×
--             --c-type α × c-trail μα ×
--             ((μ : trail) → compatible μ μβ μβ → compatible μ μα μα)
--   c-term {μα = μα} (Val v)  = {!!}
--   c-term {β = δ} {μβ = μδ} (App e₁ e₂) = {!!}
--   c-term  (Plus e₁ e₂) = {!!}
--   -- with c-term e₁ cβ cμβ
--   -- ...| (c₁ , cβ₁ , cμβ₁ , f₁) with c-term e₂ cβ₁ cμβ₁
--   -- ...| (c₂ , cα , cμα , f₂) = (c₁ , cα , cμα , λ μ x → f₂ μ (f₁ μ x))
--   c-term (Control id c₁ c₂ c e) = {!!}
--   -- with c-term (e c) cβ tt
--   -- ...| (cγ , cγ' , cμμᵢ , f₁) = {!!}
--   c-term (Prompt id e) = λ cα → {!c-term e!}
--   --= ({!!} , cα , cμα , λ μ x → x)


-- well-formed values and expressions

--transitive

-- cons : {τ₁ τ₂ : typ}{μ μα μβ : trail} → compatible (τ₁ ⇒ τ₂ , μ) μα μβ
--        → trail → trail → trail

-- cons {μα = ∙} refl x₁ x₂ = x₁
-- cons {μα = x₃ ⇒ x₄ , μα} {x₅ ⇒ x₆ , μβ} (refl , refl , snd) k k' = {!!}
-- cons {μα = ∙} refl k tt = k
-- cons {μα = x₃ ⇒ x₄ , μα} {x₁ ⇒ x₅ , μβ} (refl , refl , snd) k k' =
--   λ v t' → k v (cons-trail snd k' t')

-- append-trail : {μα μβ μγ : trail} → compatible μα μβ μγ → ⟦ μα ⟧μ → ⟦ μβ ⟧μ → ⟦ μγ ⟧μ
-- append-trail {∙} refl tt t = t
-- append-trail {x₃ ⇒ x₄ , μα} x k t = cons-trail x k t

-- tr-tra : {μα μβ μγ μδ : trail} → μδ ≡ μγ → μγ ≡ μβ → μβ ≡ μα → μδ ≡ μα
-- tr-tra refl refl refl = refl

-- tr-tra : {μα μβ μγ : trail} → μα ≡ μβ → μβ ≡ μγ → μα ≡ μγ
-- tr-tra refl refl  = refl

-- com-tra : {μ μα μβ μγ  : trail} →
--            compatible μ μγ μβ → compatible μ μβ μα  → compatible μ μγ μα

-- com-tra {∙} x x₁ =  tr-tra  x x₁
-- com-tra {τ ⇒ τ' , μ} {τα ⇒ τα' , μα} {τβ ⇒ τβ' , μβ} {μγ = ∙} x x₁ = {!!}
-- com-tra {τ ⇒ τ' , μ} {τα ⇒ τα' , ∙} {τβ ⇒ τβ' , μβ} {τγ ⇒ τγ' , μγ} x x₁ = {!!}
-- com-tra {τ ⇒ τ' , μ} {τα ⇒ τα' , (x₂ ⇒ x₃ , μα)} {τβ ⇒ τβ' , μβ} {τγ ⇒ τγ' , μγ} x x₁ = {!!}



-- ex-tra : {μα μβ μγ : trail} →
--          μγ extends μβ → μβ extends μα → μγ extends μα

-- ex-tra (∙ , refl) (μ₂ , c₂) = μ₂ , c₂
-- ex-tra ((x ⇒ x₁ , μ₁) , c₁) (∙ , refl) = (x ⇒ x₁ , μ₁) , c₁
-- ex-tra {∙} {μγ = μγ} ((x ⇒ x₁ , μ₁) , c₁) ((x₂ ⇒ x₃ , μ₂) , c₂) = μγ extends-bullet
-- ex-tra {x₄ ⇒ x₅ , μα} {x₆ ⇒ x₇ , ∙} {x₂ ⇒ x₃ , ∙} ((.x₂ ⇒ .x₃ , .(x₆ ⇒ x₇ , ∙)) , refl , refl , refl) ((.x₆ ⇒ .x₇ , .(x₄ ⇒ x₅ , μα)) , refl , refl , refl) = ((x₂ ⇒ x₃ , (x₄ ⇒ x₅ , μα))) , refl , refl , refl
-- ex-tra {x₄ ⇒ x₅ , μα} {x₆ ⇒ x₇ , (x ⇒ x₁ , μβ)} {x₂ ⇒ x₃ , ∙} ((.x₂ ⇒ .x₃ , .(x₆ ⇒ x₇ , (x ⇒ x₁ , μβ))) , refl , refl , refl) ((.x₆ ⇒ .x₇ , μ₂) , refl , refl , c₂) = ((x₂ ⇒ x₃ , (x₄ ⇒ x₅ , μα))) , (refl , refl , refl)

-- ex-tra {x₄ ⇒ x₅ , μα} {x₆ ⇒ x₇ , ∙} {x₂ ⇒ x₃ , (x ⇒ x₁ , ∙)} ((.x₂ ⇒ .x₃ , μ₁) , refl , refl , c₁) ((.x₆ ⇒ .x₇ , .(x₄ ⇒ x₅ , μα)) , refl , refl , refl) = (x₂ ⇒ x₃ , (x₄ ⇒ x₅ , {!!})) , refl , (refl , refl , (refl , {!!}))

-- ex-tra {x₄ ⇒ x₅ , μα} {x₆ ⇒ x₇ , ∙} {x₂ ⇒ x₃ , (x ⇒ x₁ , (x₈ ⇒ x₉ , μγ))} ((.x₂ ⇒ .x₃ , μ₁) , refl , refl , c₁) ((.x₆ ⇒ .x₇ , .(x₄ ⇒ x₅ , μα)) , refl , refl , refl) = {!!}
-- -- (x₂ ⇒ x₃ , (x₄ ⇒ x₅ , {!!})) , (refl , (refl , (refl , (refl , {!!}))))
-- ex-tra {x₄ ⇒ x₅ , μα} {x₆ ⇒ x₇ , (x₈ ⇒ x₉ , μβ)} {x₂ ⇒ x₃ , (x ⇒ x₁ , μγ)} ((.x₂ ⇒ .x₃ , μ₁) , refl , refl , c₁) ((.x₆ ⇒ .x₇ , μ₂) , refl , refl , c₂) = {!!}
-- -- ex-tra (μ₁ , c₁) (∙ , refl) = (μ₁ , c₁)
-- -- ex-tra (μ₁ , c₁) ((x ⇒ x₁ , μ₂) , c₂) = {!!}



-- mutual
--   wf-value : {τ : typ} → value[ wf-type ] τ → wf-type τ 
--   wf-value (Var x) = x
--   wf-value (Num n) = tt
--   wf-value (Fun wfτ₂ e) wfβ wfμβ = (wfτ₂ , wf-term (e wfτ₂) wfβ wfμβ)

--   wf-term : {τ α β : typ} {μα μβ : trail} →
--             term[ wf-type ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
--             wf-type β → wf-trail μβ →
--             wf-type τ × wf-type α × wf-trail μα ×
--             μα extends μβ
--   wf-term {μα = μα} (Val v) wfα wfμα with wf-value v
--   ... | wfτ = (wfτ , wfα , wfμα , μα extends-itself)
--   wf-term {β = δ} {μβ = μδ} (App e₁ e₂) wfδ wfμδ with wf-term e₁ wfδ wfμδ
--   ... | (wf₁ , wfγ , wfμγ , μγ-extends-μδ) with wf-term e₂ wfγ wfμγ
--   ... | (wf₂ , wfβ , wfμβ , μβ-extends-μγ) with wf₁ wfβ wfμβ
--   ... | (wfτ₂ , wfτ , wfα , wfμα , μα-extends-μβ) = (wfτ , wfα , wfμα , {!!})
--   wf-term (Plus e₁ e₂) wfα wfμβ = {!!}
--   wf-term (Control id c₁ c₂ wf e) wfα wfμβ = {!!}
--   wf-term (Prompt id e) wfα wfμα = {!!} -}


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

     sVal  : {τ τ₁ τ₃ : typ}{μα : trail} →
             {v₁ : var τ → value[ var ] τ₁} →
             {v : value[ var ] τ} →
             {v₁′ : value[ var ] τ₁} →
             SubstVal v₁ v v₁′ →
             Subst {τ₃ = τ₃}{μα = μα}(λ z → Val (v₁ z)) v (Val v₁′)

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
-- App : {τ₁ τ₂ α β γ δ : typ}{μα μβ μγ μδ : trail} →
--           (e₁ : term[ var ] (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ) →
--           (e₂ : term[ var ] τ₂ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ) →
--           term[ var ] τ₁ ⟨ μα ⟩ α ⟨ μδ ⟩ δ
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
            
  -- Prompt : {τ α β β' : typ}{μᵢ μα : trail} →
  --            (is-id-trail β β' μᵢ) →
  --            (e : term[ var ] β ⟨ μᵢ ⟩ β' ⟨ ∙ ⟩ τ) →
  --            term[ var ] τ ⟨ μα ⟩ α ⟨ μα ⟩ α
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

  -- Plus : {α β γ : typ} {μα μβ μγ : trail} →
  --          term[ var ] Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ →
  --          term[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β →
  --          term[ var ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ
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
            Reduce {τ₂ = τ₂}{μα = μα}(Prompt refl (Val v₁)) (Val v₁)

    -- RControl : {τ α α' β β' γ γ' t₁ t₂ τ₁ τ₂ τ₃ τ₄ τ₅ : typ}
    --            {μ₀ μ₁ μᵢ μα μα' μβ μβ' μ₂ μ₃ μ₄ μ₅ : trail} →
    --           (p₁ : pcontext[ var , τ ⟨ μα ⟩ α ⟨ μβ ⟩ β ]
    --                          τ₁ ⟨ μ₃ ⟩ τ₂ ⟨ ∙ ⟩ β ) →
    --           (p₂ : pcontext[ var , τ ⟨ μα' ⟩ α' ⟨ μα' ⟩ α' ]
    --                          t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α ) →
    --           {x₀ : is-id-trail τ₁ τ₂ μ₃} →
    --           (x₁ : is-id-trail γ γ' μᵢ) →
    --           (x₂ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
    --           (x₃ : compatible μβ μ₀ μα) →
    --           same-pcontext p₁ p₂ →
    --           (e : var (τ ⇒ t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) → term[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
    --           Reduce {τ₂ = τ₂}{μα = μα} (Prompt x₀
    --                  (pcontext-plug p₁ (Control x₁ x₂ x₃ e)))
    --                  (Prompt x₁ (App (Val (Fun e))
    --                  (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))))
    -- 元々の最も制約が少ないやつ
    -- μ₂を全部μ₀にした
    -- p₂の外側 t₁ ⟨ μ₁ ⟩ t₂ を τ₁ ⟨ μ₃ ⟩ τ₂,合わせてx₂とeも変えた

    
  RControl : {τ α α' β β' γ γ' t₁ t₂ τ₁ τ₂ τ₃ τ₄ τ₅ : typ}
             {μ₀ μ₁ μᵢ μα μα' μβ μβ' μ₂ μ₃ μ₄ μ₅ : trail} →
             (p₁ : pcontext[ var , τ ⟨ μα ⟩ α ⟨ μβ ⟩ β ]
                            τ₁ ⟨ μ₃ ⟩ τ₂ ⟨ ∙ ⟩ β ) →
             (p₂ : pcontext[ var , τ ⟨ μα' ⟩ α' ⟨ μα' ⟩ α' ]
                            τ₁ ⟨ μ₃ ⟩ τ₂ ⟨ μ₀ ⟩ α ) →
             {x₀ : is-id-trail τ₁ τ₂ μ₃} →
             (x₁ : is-id-trail γ γ' μᵢ) →
             (x₂ : compatible (τ₁ ⇒ τ₂ , μ₃) μ₀ μ₀) →
             (x₃ : compatible μβ μ₀ μα) →
             same-pcontext p₁ p₂ →
             (e : var (τ ⇒ τ₁ ⟨ μ₃ ⟩ τ₂ ⟨ μ₀ ⟩ α) → term[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
             Reduce {τ₂ = τ₂}{μα = μα} (Prompt x₀
                    (pcontext-plug p₁ (Control x₁ x₂ x₃ e)))
                    (Prompt x₁ (App (Val (Fun e))
                    (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))))
                     
-- Control : {τ α β γ γ' t₁ t₂ : typ}{μ₀ μ₁ μ₂ μᵢ μα μβ : trail} →
--              (is-id-trail γ γ' μᵢ) →
--              (compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
--              (compatible μβ μ₀ μα) →
--              (e : var (τ ⇒ t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
--              term[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
--              term[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β


--     Prompt : {τ α β β' : typ}{μᵢ μα : trail} →
--              (is-id-trail β β' μᵢ) →
--              (e : term[ var ] β ⟨ μᵢ ⟩ β' ⟨ ∙ ⟩ τ) →
--              term[ var ] τ ⟨ μα ⟩ α ⟨ μα ⟩ α


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

